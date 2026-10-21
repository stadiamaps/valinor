//! Paths to the test fixtures in the `fixtures` directory of this crate.
//!
//! All fixtures are made from the same OpenStreetMap extract of Andorra.

use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join(name)
}

/// A tile directory, as `valhalla_build_tiles` writes it.
pub(crate) fn andorra_tiles_dir() -> PathBuf {
    fixture("andorra-tiles")
}

/// The tiles of [`andorra_tiles_dir`] in an extract tarball,
/// as `valhalla_build_extract` writes it.
pub(crate) fn andorra_tiles_tar() -> PathBuf {
    fixture("andorra-tiles.tar")
}

/// The tiles of [`andorra_tiles_dir`] with predicted traffic speeds
/// from `valhalla_add_predicted_traffic`.
pub(crate) fn andorra_tiles_with_traffic_dir() -> PathBuf {
    fixture("andorra-tiles-with-traffic")
}

/// A live traffic tarball for the Andorra tiles.
pub(crate) fn andorra_traffic_tar() -> PathBuf {
    fixture("andorra-traffic.tar")
}
