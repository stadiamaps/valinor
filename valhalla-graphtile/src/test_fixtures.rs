//! The test fixtures in the `fixtures` directory of this crate.
//!
//! Miri does not support memory maps, so the tarball paths are feature gated.

use crate::GraphId;
use crate::graph_tile::GraphTile;
use crate::graph_tile::handles::OwnedGraphTileHandle;
use crate::tile_provider::TILE_FILE_EXTENSION;
use std::path::PathBuf;
use std::sync::LazyLock;
use walkdir::WalkDir;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join(name)
}

/// A tile directory, as `valhalla_build_tiles` writes it.
pub(crate) fn andorra_tiles_dir() -> PathBuf {
    fixture("andorra-tiles")
}

/// The base graph ID of the smallest tile in [`andorra_tiles_dir`].
///
/// Tests that run under Miri use this tile to stay fast.
pub(crate) fn smallest_andorra_tile() -> GraphId {
    static SMALLEST: LazyLock<GraphId> = LazyLock::new(|| {
        let path = WalkDir::new(andorra_tiles_dir())
            .into_iter()
            .map(|entry| entry.expect("Unable to read the fixture directory"))
            .filter(|entry| {
                entry.file_type().is_file()
                    && entry
                        .path()
                        .extension()
                        .is_some_and(|extension| extension == TILE_FILE_EXTENSION)
            })
            .min_by_key(|entry| {
                let len = entry
                    .metadata()
                    .expect("Unable to read the tile metadata")
                    .len();
                (len, entry.path().to_path_buf())
            })
            .expect("The fixture directory has tiles")
            .into_path();
        let bytes = std::fs::read(path).expect("Unable to read the tile");
        OwnedGraphTileHandle::try_from(bytes)
            .expect("Unable to decode the tile")
            .graph_id()
    });
    *SMALLEST
}

/// The tiles of [`andorra_tiles_dir`] in an extract tarball,
/// as `valhalla_build_extract` writes it.
#[cfg(not(miri))]
pub(crate) fn andorra_tiles_tar() -> PathBuf {
    fixture("andorra-tiles.tar")
}

/// The tiles of [`andorra_tiles_dir`] with predicted traffic speeds
/// from `valhalla_add_predicted_traffic`.
pub(crate) fn andorra_tiles_with_traffic_dir() -> PathBuf {
    fixture("andorra-tiles-with-traffic")
}

/// A live traffic tarball for the Andorra tiles.
#[cfg(not(miri))]
pub(crate) fn andorra_traffic_tar() -> PathBuf {
    fixture("andorra-traffic.tar")
}
