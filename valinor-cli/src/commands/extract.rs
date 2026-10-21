//! The `extract` subcommand: writes an offline sub-extract of a tile extract or tile directory.

use std::{
    io::BufWriter,
    num::NonZeroUsize,
    path::{Path, PathBuf},
};

#[cfg(unix)]
use std::{fs::Permissions, os::unix::fs::PermissionsExt};

use anyhow::Context;
use clap::Args;
use tempfile::NamedTempFile;
use valhalla_graphtile::GraphId;
use valhalla_graphtile::extract::write_extract;
use valhalla_graphtile::tile_provider::{
    DirectoryGraphTileProvider, TarballTileProvider, TileBytesSource,
};

/// Write an offline sub-extract of a tile extract tarball or a tile directory
///
/// Copies the given graph tiles of the source into a new, fully spec-compliant
/// extract tarball. Every tile in the output is byte-identical to its source tile,
/// and the output is interchangeable with `valhalla_build_extract` output,
/// so it is consumable by both stock Valhalla and Valinor.
///
/// Unlike the other subcommands, this takes the source path directly
/// rather than a Valhalla JSON config: extraction reads a set of tiles,
/// not a configured tile hierarchy.
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
        value_parser = GraphId::parse_tile
    )]
    pub(crate) tiles: Vec<GraphId>,
}

/// A successful extract, as reported on stderr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExtractSummary {
    tile_count: usize,
    bytes_written: u64,
}

/// Writes the sub-extract from a tile directory or a tarball, as the source path requires.
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

    Ok(ExtractSummary {
        tile_count: args.tiles.len(),
        bytes_written,
    })
}

/// Writes the extract to a temporary file next to `output`,
/// then renames the temporary file to `output`.
///
/// A partial tarball is worse than no tarball
/// (it may open, but with tiles silently missing or truncated).
/// The rename is atomic, so `output` is never a partial tarball:
/// it is either the complete extract, or what it was before the call.
/// If the write fails, the temporary file is removed.
fn write_atomically<S>(source: &S, tiles: &[GraphId], output: &Path) -> anyhow::Result<u64>
where
    S: TileBytesSource,
    S::Error: Send + Sync,
{
    // The temporary file must be on the same file system as the output,
    // or the rename cannot be atomic.
    let output_dir = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));

    let mut builder = tempfile::Builder::new();
    builder.prefix(".valinor-extract-").suffix(".tar.partial");
    // Temporary files are only readable by the owner by default.
    // Give the output the same permissions as a file from `File::create`.
    #[cfg(unix)]
    builder.permissions(Permissions::from_mode(0o666));
    let temp_file: NamedTempFile = builder.tempfile_in(output_dir).with_context(|| {
        format!(
            "Failed to create a temporary file in {}",
            output_dir.display()
        )
    })?;

    let mut dest = BufWriter::new(temp_file);
    let bytes_written =
        write_extract(source, tiles, &mut dest).context("Failed to write the extract")?;
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

    // Tragically, memory maps are not supported by Miri,
    // and the tests below open tarballs with the memory-mapped provider!
    #[cfg(not(miri))]
    #[test]
    fn extract_round_trips_from_a_tarball_and_a_directory() {
        let temp_dir = tempfile::tempdir().expect("a temporary directory is created");
        let tiles = vec![tile(0, 3015), tile(1, 47_701), tile(2, 763_926)];

        let mut outputs = Vec::new();
        for (source, name) in [
            (fixture("andorra-tiles.tar"), "from-tarball.tar"),
            (fixture("andorra-tiles"), "from-directory.tar"),
        ] {
            let output = temp_dir.path().join(name);
            let args = ExtractArgs {
                source,
                output: output.clone(),
                tiles: tiles.clone(),
            };

            let summary = write_sub_extract(&args).expect("the extract writes cleanly");
            assert_eq!(summary.tile_count, tiles.len());

            let on_disk = fs::metadata(&output).expect("the output exists").len();
            assert_eq!(summary.bytes_written, on_disk);

            // The produced tarball opens with the crate's own reader
            // and contains exactly the requested tiles.
            let extract = TarballTileProvider::new_readonly(&output)
                .expect("the generated extract opens cleanly");
            let mut extracted: Vec<GraphId> = extract.tile_ids().copied().collect();
            extracted.sort_unstable();
            let mut expected = tiles.clone();
            expected.sort_unstable();
            assert_eq!(extracted, expected);

            outputs.push(fs::read(&output).expect("the output is readable"));
        }

        assert_eq!(
            outputs[0], outputs[1],
            "the tarball and directory fixtures give the same extract"
        );

        // Only the outputs are in the directory: no temporary files are left.
        let mut names: Vec<_> = fs::read_dir(temp_dir.path())
            .expect("the directory is readable")
            .map(|entry| entry.expect("the entry is readable").file_name())
            .collect();
        names.sort_unstable();
        assert_eq!(names, ["from-directory.tar", "from-tarball.tar"]);
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
            format!("{error:#}").contains("is not in the source"),
            "{error:#}"
        );
        assert_eq!(
            fs::read(&output).expect("the previous output still exists"),
            b"previous contents"
        );
        assert_eq!(
            fs::read_dir(temp_dir.path())
                .expect("the directory is readable")
                .count(),
            1,
            "the temporary file is removed"
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
        assert_eq!(mode(&output), mode(&reference));
    }
}
