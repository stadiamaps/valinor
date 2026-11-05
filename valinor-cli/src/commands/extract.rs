//! The `extract` subcommand: writes an offline sub-extract of a tile extract or tile directory.

use std::{
    collections::HashSet,
    io::BufWriter,
    num::NonZeroUsize,
    path::{Path, PathBuf},
};

#[cfg(unix)]
use std::{fs::Permissions, os::unix::fs::PermissionsExt};

use anyhow::{Context, anyhow};
use clap::Args;
use tempfile::NamedTempFile;
use valhalla_graphtile::GraphId;
use valhalla_graphtile::extract::write_extract;
use valhalla_graphtile::tile_provider::{
    DirectoryGraphTileProvider, GraphTileProvider, TarballTileProvider,
};

/// Write an offline sub-extract of a tile extract tarball or a tile directory
///
/// The output is an extract tarball in the format of `valhalla_build_extract`,
/// with the given tiles copied byte for byte.
#[derive(Args, Debug)]
pub(crate) struct ExtractArgs {
    /// Path to the source: a tile extract tarball (e.g. tiles.tar)
    /// or a tile directory (e.g. the `tile_dir` of a Valhalla config)
    source: PathBuf,

    /// Path to write the output extract tarball to
    output: PathBuf,

    /// A tile to copy, as level/tile_id (e.g. `--tile 2/763926`)
    ///
    /// Give the option once for each tile,
    /// or give a comma-separated list (e.g. `--tile 0/3015,1/47701`).
    #[arg(
        long = "tile",
        value_name = "LEVEL/TILE_ID",
        required = true,
        value_delimiter = ',',
        value_parser = parse_tile
    )]
    pub(crate) tiles: Vec<GraphId>,
}

/// Parses the base graph ID of a tile from the `level/tile_id` form.
fn parse_tile(input: &str) -> anyhow::Result<GraphId> {
    let (level, tile_id) = input
        .split_once('/')
        .ok_or_else(|| anyhow!("expected the level/tile_id form"))?;
    let level = level.parse().context("invalid level")?;
    let tile_id = tile_id.parse().context("invalid tile id")?;
    Ok(GraphId::try_from_components(level, tile_id, 0)?)
}

/// A successful extract, as reported on stderr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExtractSummary {
    tile_count: usize,
    bytes_written: u64,
}

/// Writes the sub-extract from the tile directory or the tarball at the source path.
fn write_sub_extract(args: &ExtractArgs) -> anyhow::Result<ExtractSummary> {
    let bytes_written = if args.source.is_dir() {
        // The writer reads each tile once, so a cache is of no use.
        let provider = DirectoryGraphTileProvider::new(args.source.clone(), NonZeroUsize::MIN);
        write_atomically(&provider, &args.tiles, &args.output)?
    } else {
        let provider = TarballTileProvider::new_readonly(&args.source).with_context(|| {
            format!(
                "Failed to open source tile extract at {}",
                args.source.display()
            )
        })?;
        write_atomically(&provider, &args.tiles, &args.output)?
    };

    // The extract contains each tile once, even if the arguments name it more than once.
    let tile_count = args.tiles.iter().collect::<HashSet<_>>().len();
    Ok(ExtractSummary {
        tile_count,
        bytes_written,
    })
}

/// Writes the extract to a temporary file next to `output`, and then renames it to `output`.
///
/// If the write fails, `output` keeps its previous contents.
fn write_atomically<P: GraphTileProvider>(
    provider: &P,
    tiles: &[GraphId],
    output: &Path,
) -> anyhow::Result<u64> {
    // The rename is atomic only within one file system.
    let output_dir = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));

    let mut builder = tempfile::Builder::new();
    builder.prefix(".valinor-extract-").suffix(".tar.partial");
    // Use the permissions of `File::create`, not the owner-only default of `tempfile`.
    #[cfg(unix)]
    builder.permissions(Permissions::from_mode(0o666));
    let temp_file: NamedTempFile = builder.tempfile_in(output_dir).with_context(|| {
        format!(
            "Failed to create a temporary file in {}",
            output_dir.display()
        )
    })?;

    let mut dest = BufWriter::new(temp_file);
    let bytes_written = write_extract(provider, tiles.iter().copied(), &mut dest)
        .context("Failed to write the extract")?;
    let temp_file = dest
        .into_inner()
        .map_err(|e| e.into_error())
        .context("Failed to flush the output extract")?;
    // Make sure that the data is on disk before the rename makes the file visible.
    temp_file
        .as_file()
        .sync_all()
        .context("Failed to sync the output extract to disk")?;
    temp_file.persist(output).with_context(|| {
        format!(
            "Failed to move the output extract into place at {}",
            output.display()
        )
    })?;

    Ok(bytes_written)
}

/// Runs the `extract` subcommand, and prints a one-line summary on stderr.
pub(crate) fn run(args: &ExtractArgs) -> anyhow::Result<()> {
    let summary = write_sub_extract(args)?;
    let noun = if summary.tile_count == 1 {
        "tile"
    } else {
        "tiles"
    };
    eprintln!(
        "Extracted {} {noun} ({} bytes) to {}",
        summary.tile_count,
        summary.bytes_written,
        args.output.display()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    /// Path to a fixture in the sibling `valhalla-graphtile` crate.
    fn fixture(name: &str) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("valhalla-graphtile")
            .join("fixtures")
            .join(name)
    }

    fn tile(level: u8, tile_id: u64) -> GraphId {
        GraphId::try_from_components(level, tile_id, 0).expect("valid tile ID in test")
    }

    // Tragically, memory maps are not supported by Miri!
    #[cfg(not(miri))]
    #[test]
    fn extract_round_trips_from_a_tarball_and_a_directory() {
        let temp_dir = tempfile::tempdir().expect("a temporary directory is created");
        let tiles = vec![tile(0, 3015), tile(1, 47_701), tile(2, 763_926)];
        // The arguments name one tile twice, but the extract contains it once.
        let mut tile_args = tiles.clone();
        tile_args.push(tile(1, 47_701));

        let mut outputs = Vec::new();
        for (source, name) in [
            (fixture("andorra-tiles.tar"), "from-tarball.tar"),
            (fixture("andorra-tiles"), "from-directory.tar"),
        ] {
            let output = temp_dir.path().join(name);
            let args = ExtractArgs {
                source,
                output: output.clone(),
                tiles: tile_args.clone(),
            };

            let summary = write_sub_extract(&args).expect("the extract writes cleanly");
            assert_eq!(
                summary.tile_count,
                tiles.len(),
                "The summary must count each tile once"
            );

            let on_disk = fs::metadata(&output).expect("the output exists").len();
            assert_eq!(
                summary.bytes_written, on_disk,
                "The summary must give the size of the output file"
            );

            let extract = TarballTileProvider::new_readonly(&output)
                .expect("the generated extract opens cleanly");
            let mut extracted: Vec<GraphId> = extract.tile_ids().copied().collect();
            extracted.sort_unstable();
            let mut expected = tiles.clone();
            expected.sort_unstable();
            assert_eq!(
                extracted, expected,
                "The extract must contain each requested tile once"
            );

            outputs.push(fs::read(&output).expect("the output is readable"));
        }

        assert_eq!(
            outputs[0], outputs[1],
            "The tarball and directory fixtures must give the same extract"
        );

        let mut names: Vec<_> = fs::read_dir(temp_dir.path())
            .expect("the directory is readable")
            .map(|entry| entry.expect("the entry is readable").file_name())
            .collect();
        names.sort_unstable();
        assert_eq!(
            names,
            ["from-directory.tar", "from-tarball.tar"],
            "No temporary files must remain after a successful extract"
        );
    }

    #[cfg(not(miri))]
    #[test]
    fn failed_extract_keeps_the_previous_output() {
        let temp_dir = tempfile::tempdir().expect("a temporary directory is created");
        let output = temp_dir.path().join("andorra-sub.tar");
        fs::write(&output, b"previous contents").expect("the previous output is written");

        let args = ExtractArgs {
            source: fixture("andorra-tiles.tar"),
            output: output.clone(),
            // The fixture has no tile 2/0.
            tiles: vec![tile(0, 3015), tile(2, 0)],
        };

        let error = write_sub_extract(&args).expect_err("a missing tile fails the extract");
        assert!(
            format!("{error:#}").contains("GraphId 2/0/0 is not in the provider"),
            "The error must name the missing tile: {error:#}"
        );
        assert_eq!(
            fs::read(&output).expect("the previous output still exists"),
            b"previous contents",
            "A failed extract must not change the previous output"
        );
        assert_eq!(
            fs::read_dir(temp_dir.path())
                .expect("the directory is readable")
                .count(),
            1,
            "The temporary file must be removed after a failed extract"
        );
    }

    #[cfg(unix)]
    #[cfg(not(miri))]
    #[test]
    fn output_has_the_permissions_of_a_new_file() {
        let temp_dir = tempfile::tempdir().expect("a temporary directory is created");
        let output = temp_dir.path().join("andorra-sub.tar");
        let reference = temp_dir.path().join("reference");
        fs::File::create(&reference).expect("the reference file is created");

        let args = ExtractArgs {
            source: fixture("andorra-tiles.tar"),
            output: output.clone(),
            tiles: vec![tile(0, 3015)],
        };
        write_sub_extract(&args).expect("the extract writes cleanly");

        let mode = |path: &Path| {
            fs::metadata(path)
                .expect("the file exists")
                .permissions()
                .mode()
        };
        assert_eq!(
            mode(&output),
            mode(&reference),
            "The output must have the permissions of a file from File::create"
        );
    }
}
