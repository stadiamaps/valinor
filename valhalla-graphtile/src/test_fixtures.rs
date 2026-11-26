//! The test fixtures in the `fixtures` directory of this crate.
//!
//! Miri does not support memory maps, so the tarball paths are feature gated.

use crate::GraphId;
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

/// Named tile IDs for the Andorra fixtures and missing-tile tests.
pub(crate) struct AndorraFixtureTiles;

impl AndorraFixtureTiles {
    fn tile(level: u8, tile_id: u64) -> GraphId {
        GraphId::try_from_components(level, tile_id, 0).expect("valid fixture tile ID")
    }

    /// Returns the base graph ID of `fixtures/andorra-tiles/2/000/763/927.gph`.
    /// This is the smallest fixture tile, which limits Miri test time.
    pub(crate) fn smallest() -> GraphId {
        let level = 2;
        let tile_id = 763_927;
        Self::tile(level, tile_id)
    }

    /// Returns a made-up base tile ID past the Andorra fixtures' end.
    pub(crate) fn missing() -> GraphId {
        let level = 2;
        let tile_id = 763_928;
        Self::tile(level, tile_id)
    }

    /// Returns all fixture tile IDs in ascending (level, tile ID) order.
    pub(crate) fn all() -> [GraphId; 7] {
        [
            Self::tile(0, 3_015),
            Self::tile(1, 47_701),
            Self::tile(2, 762_485),
            Self::tile(2, 762_486),
            Self::tile(2, 763_925),
            Self::tile(2, 763_926),
            Self::smallest(),
        ]
    }

    /// Returns the first and last fixture tiles in archive order.
    pub(crate) fn first_and_last() -> [GraphId; 2] {
        [Self::all()[0], Self::smallest()]
    }

    /// Returns an unordered subset across all levels, including a feature index.
    pub(crate) fn unordered_subset() -> [GraphId; 4] {
        let [level_0, level_1, local, _, _, other_local, _] = Self::all();
        [
            other_local,
            level_0,
            level_1.with_feature_index(42).expect("valid feature index"),
            local,
        ]
    }

    /// Returns a fixture tile that `unordered_subset` excludes.
    pub(crate) fn excluded_from_subset() -> GraphId {
        Self::all()[4]
    }
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
