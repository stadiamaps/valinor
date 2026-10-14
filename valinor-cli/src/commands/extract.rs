//! The `extract` subcommand: writes an offline sub-extract of a tile extract tarball.

use std::{
    fs,
    fs::File,
    io::{BufWriter, Write},
    path::PathBuf,
};

use anyhow::Context;
use clap::Args;
use valhalla_graphtile::GraphId;
use valhalla_graphtile::extract::write_extract;
use valhalla_graphtile::tile_provider::TarballTileProvider;

/// Write an offline sub-extract of a tile extract tarball
///
/// Copies the given graph tiles of the source extract into a new, fully spec-compliant
/// extract tarball. Every tile in the output is byte-identical to its source tile,
/// and the output is interchangeable with `valhalla_build_extract` output,
/// so it is consumable by both stock Valhalla and Valinor.
///
/// Unlike the other subcommands, this takes the tile extract tarball path
/// directly rather than a Valhalla JSON config: extraction reads an extract
/// file, not a configured tile hierarchy.
#[derive(Args, Debug)]
pub(crate) struct ExtractArgs {
    /// Path to the source tile extract tarball (e.g. tiles.tar)
    source: PathBuf,

    /// Path to write the output extract tarball to
    output: PathBuf,

    /// A tile to copy, as level/tile_index (e.g. `--tile 2/763926`)
    ///
    /// Give the option once for each tile,
    /// or give a comma-separated list (e.g. `--tile 0/3015,1/47701`).
    #[arg(
        long = "tile",
        value_name = "LEVEL/TILE_INDEX",
        required = true,
        value_delimiter = ',',
        value_parser = parse_tile
    )]
    pub(crate) tiles: Vec<GraphId>,
}

/// A successful extract, as reported on stderr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExtractSummary {
    tile_count: usize,
    bytes_written: u64,
}

/// Parses a `level/tile_index` tile argument into a base tile ID.
fn parse_tile(input: &str) -> Result<GraphId, String> {
    let Some((level, tile_index)) = input.split_once('/') else {
        return Err(format!("'{input}' is not in the level/tile_index form"));
    };
    let level: u8 = level
        .trim()
        .parse()
        .map_err(|_| format!("the level in '{input}' is not a valid number"))?;
    let tile_index: u64 = tile_index
        .trim()
        .parse()
        .map_err(|_| format!("the tile index in '{input}' is not a valid number"))?;
    GraphId::try_from_components(level, tile_index, 0)
        .map_err(|e| format!("'{input}' is not a valid tile: {e}"))
}

/// Writes the sub-extract, and removes the partial output if the write fails.
fn write_sub_extract(args: &ExtractArgs) -> anyhow::Result<ExtractSummary> {
    let provider = TarballTileProvider::new_readonly(&args.source).with_context(|| {
        format!(
            "Failed to open source tile extract at {}",
            args.source.display()
        )
    })?;

    let file = File::create(&args.output).with_context(|| {
        format!(
            "Failed to create the output extract at {}",
            args.output.display()
        )
    })?;

    let write_result = (|| {
        let mut dest = BufWriter::new(file);
        let bytes_written = write_extract(&provider, &args.tiles, &mut dest)
            .context("Failed to write the extract")?;
        dest.flush().context("Failed to flush the output extract")?;
        Ok(bytes_written)
    })();

    match write_result {
        Ok(bytes_written) => Ok(ExtractSummary {
            tile_count: args.tiles.len(),
            bytes_written,
        }),
        Err(error) => {
            // A partial tarball is worse than no tarball
            // (it may open, but with tiles silently missing or truncated),
            // so clean up on a best-effort basis.
            let _ = fs::remove_file(&args.output);
            Err(error)
        }
    }
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

    /// Path to the Andorra fixture tarball in the sibling crate.
    fn andorra_fixture() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("valhalla-graphtile")
            .join("fixtures")
            .join("andorra-tiles.tar")
    }

    fn tile(level: u8, tile_index: u64) -> GraphId {
        GraphId::try_from_components(level, tile_index, 0).expect("valid tile ID in test")
    }

    #[test]
    fn parse_tile_accepts_level_and_tile_index() {
        assert_eq!(parse_tile("2/763926"), Ok(tile(2, 763_926)));
        assert_eq!(parse_tile(" 0 / 3015 "), Ok(tile(0, 3015)));
    }

    #[test]
    fn parse_tile_rejects_malformed_input() {
        for (input, expected) in [
            ("2", "is not in the level/tile_index form"),
            ("x/763926", "the level in 'x/763926' is not a valid number"),
            ("2/abc", "the tile index in '2/abc' is not a valid number"),
            // A graph ID with a feature index has three components.
            (
                "2/763926/7",
                "the tile index in '2/763926/7' is not a valid number",
            ),
            // Levels have 3 bits, and tile indexes have 22 bits.
            ("8/0", "'8/0' is not a valid tile"),
            ("0/4194304", "'0/4194304' is not a valid tile"),
        ] {
            let error = parse_tile(input).expect_err("malformed input is rejected");
            assert!(error.contains(expected), "{input}: {error}");
        }
    }

    // Tragically, memory maps are not supported by Miri,
    // and the tests below open tarballs with the memory-mapped provider!
    #[cfg(not(miri))]
    #[test]
    fn extract_round_trips_through_the_tarball_provider() {
        let temp_dir = tempfile::tempdir().expect("a temporary directory is created");
        let output = temp_dir.path().join("andorra-sub.tar");
        let tiles = vec![tile(0, 3015), tile(1, 47_701), tile(2, 763_926)];
        let args = ExtractArgs {
            source: andorra_fixture(),
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
        let mut expected = tiles;
        expected.sort_unstable();
        assert_eq!(extracted, expected);
    }

    #[cfg(not(miri))]
    #[test]
    fn failed_extract_removes_the_partial_output() {
        let temp_dir = tempfile::tempdir().expect("a temporary directory is created");
        let output = temp_dir.path().join("andorra-sub.tar");
        let args = ExtractArgs {
            source: andorra_fixture(),
            output: output.clone(),
            // The fixture has no tile 2/0.
            tiles: vec![tile(0, 3015), tile(2, 0)],
        };

        let error = write_sub_extract(&args).expect_err("a missing tile fails the extract");
        assert!(
            format!("{error:#}").contains("is not in the source extract"),
            "{error:#}"
        );
        assert!(!output.exists(), "the partial output is removed");
    }
}
