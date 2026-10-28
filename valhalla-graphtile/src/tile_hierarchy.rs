//! # The Valhalla Tile Hierarchy
//!
//! Valhalla uses a tiered hierarchy based on road class.
//! This enables efficient traversal of the graph.
//! See <https://valhalla.github.io/valhalla/tiles/> for a full writeup.

use super::{GraphId, RoadClass};
use geo::{CoordFloat, Rect, coord};
use num_traits::FromPrimitive;
use std::sync::LazyLock;
use thiserror::Error;

/// A tiling system description.
///
/// Valhalla is relatively generic here,
/// though everything is relatively hard-coded to WGS84.
pub struct TilingSystem {
    /// The bounding box of the tiling system.
    pub bounding_box: Rect<f32>,
    /// The size of each side of a square tile.
    pub tile_size: f32,
    /// The number of rows in the tiling system.
    pub n_rows: u32,
    /// The number of columns in the tiling system.
    pub n_cols: u32,
    /// The number of subdivisions within a single tile.
    pub n_subdivisions: u8,
    /// Does the tiling system wrap in the x direction (e.g. at longitude = 180)?
    pub wrap_x: bool,
}

impl TilingSystem {
    fn new(bounding_box: Rect<f32>, tile_size: f32) -> Self {
        Self {
            bounding_box,
            tile_size,
            #[expect(clippy::cast_possible_truncation)]
            #[expect(clippy::cast_sign_loss)]
            n_rows: (bounding_box.height() / tile_size).round() as u32,
            #[expect(clippy::cast_possible_truncation)]
            #[expect(clippy::cast_sign_loss)]
            n_cols: (bounding_box.width() / tile_size).round() as u32,
            n_subdivisions: 5,
            wrap_x: true, // I've not seen this overridden in Valhalla so far...
        }
    }

    pub const fn tile_count(&self) -> u32 {
        self.n_rows * self.n_cols
    }

    pub const fn min_zoom(&self) -> u8 {
        if self.tile_size > 1.0 {
            0
        } else if self.tile_size > 0.25 {
            6
        } else {
            12
        }
    }
}

/// A level in the Valhalla tile hierarchy.
pub struct TileLevel {
    /// The hierarchy level.
    pub level: u8,
    /// The minimum class of road contained in this hierarchy level.
    pub minimum_road_class: RoadClass,
    /// The human-readable name of the level.
    pub name: &'static str,
    /// The tiling system used for this level.
    pub tiling_system: TilingSystem,
}

impl TileLevel {
    /// Returns an iterator over tile indices (0-based, row-major) in this level
    /// whose geographic extent intersects the axis-aligned bbox:
    /// `lon ∈ [west, east], lat ∈ [south, north]`.
    ///
    /// Longitudes are expected in degrees, in the `[-180, 180]` range.
    /// If `west > east`, the bbox is assumed to wrap across the antimeridian
    /// and is treated as the union of `[left, 180] ∪ [-180, right]`
    ///
    /// # Correctness
    ///
    /// This function does not sanity check the input.
    /// It is the responsibility of the caller to ensure that the coordinates are in the range for
    /// latitude and longitude, and that they describe a valid bounding box.
    pub fn tiles_intersecting_bbox<N: CoordFloat + FromPrimitive>(
        &self,
        north: N,
        east: N,
        south: N,
        west: N,
    ) -> Vec<GraphId> {
        // These conversions cannot fail and are exercised by unit tests
        let size = N::from(self.tiling_system.tile_size).unwrap();
        let width = i64::from(self.tiling_system.n_cols);
        let height = i64::from(self.tiling_system.n_rows);

        let n_90 = N::from(90).unwrap();
        let n_180 = N::from(180).unwrap();

        if west > east {
            // Wrap across the antimeridian: [west, 180] ∪ [-180, east].
            self.tiles_intersecting_bbox(north, n_180, south, west)
                .into_iter()
                .chain(self.tiles_intersecting_bbox(north, east, south, -n_180))
                .collect()
        } else {
            // At this point we have a non-wrapping lon interval [w, e] with w <= e.

            // Map lon from [-180, 180] to [0, 360] and then to tile index.
            let min_x = (((west + n_180) / size)
                .floor()
                .to_i64()
                .expect("Unable to convert value to i64"))
            .clamp(0, width - 1);
            let max_x = (((east + n_180) / size)
                .floor()
                .to_i64()
                .expect("Unable to convert value to i64"))
            .clamp(0, width - 1);

            // Map lat from [-90, 90] to [0, 180] and then to tile index.
            let min_y = (((south + n_90) / size)
                .floor()
                .to_i64()
                .expect("Unable to convert value to i64"))
            .clamp(0, height - 1);
            let max_y = (((north + n_90) / size)
                .floor()
                .to_i64()
                .expect("Unable to convert value to i64"))
            .clamp(0, height - 1);

            // Iterate row-major: for each y, for each x, compute tile_index.
            (min_y..=max_y)
                .flat_map(move |y| {
                    (min_x..=max_x).map(move |x| {
                        let tile_index = (y * width + x) as u64;
                        GraphId::try_from_components(self.level, tile_index, 0)
                            .expect("valid base id")
                    })
                })
                .collect()
        }
    }
}

/// A concrete instantiation of the standard Valhalla tile system.
///
/// While other systems are technically possible, you should probably stick to the canonical one.
pub static STANDARD_LEVELS: LazyLock<[TileLevel; 3]> = LazyLock::new(|| {
    [
        TileLevel {
            level: 0,
            minimum_road_class: RoadClass::Primary,
            name: "highway",
            tiling_system: TilingSystem::new(
                Rect::new(
                    coord! { x: -180f32, y: -90f32 },
                    coord! { x: 180f32, y: 90f32 },
                ),
                4.0,
            ),
        },
        TileLevel {
            level: 1,
            minimum_road_class: RoadClass::Tertiary,
            name: "arterial",
            tiling_system: TilingSystem::new(
                Rect::new(
                    coord! { x: -180f32, y: -90f32 },
                    coord! { x: 180f32, y: 90f32 },
                ),
                1.0,
            ),
        },
        TileLevel {
            level: 2,
            minimum_road_class: RoadClass::ServiceOther,
            name: "local",
            tiling_system: TilingSystem::new(
                Rect::new(
                    coord! { x: -180f32, y: -90f32 },
                    coord! { x: 180f32, y: 90f32 },
                ),
                0.25,
            ),
        },
    ]
});

pub static TRANSIT_LEVEL: LazyLock<TileLevel> = LazyLock::new(|| TileLevel {
    level: 3,
    minimum_road_class: RoadClass::ServiceOther,
    name: "transit",
    tiling_system: TilingSystem::new(
        Rect::new(
            coord! { x: -180f32, y: -90f32 },
            coord! { x: 180f32, y: 90f32 },
        ),
        0.25,
    ),
});

/// A known Valhalla graph tile level.
///
/// Use [`ValhallaLevel::try_from`] to check a level number from a graph ID or a tile header.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum ValhallaLevel {
    /// Level 0, with primary roads and higher.
    Highway = 0,
    /// Level 1, with tertiary roads and higher.
    Arterial = 1,
    /// Level 2, with all road classes.
    Local = 2,
    /// Level 3, with transit stops, routes, and schedules.
    Transit = 3,
}

/// The level number is not a [`ValhallaLevel`].
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
#[error("unknown tile hierarchy level {0}")]
pub struct UnknownLevelError(pub u8);

impl ValhallaLevel {
    /// The standard (road) levels, in level order.
    pub const STANDARD: [Self; 3] = [Self::Highway, Self::Arterial, Self::Local];

    /// All levels, in level order.
    pub const ALL: [Self; 4] = [Self::Highway, Self::Arterial, Self::Local, Self::Transit];

    /// Gets the level number.
    #[inline]
    #[must_use]
    pub const fn number(self) -> u8 {
        self as u8
    }

    /// Is this the transit level?
    #[inline]
    #[must_use]
    pub const fn is_transit(self) -> bool {
        matches!(self, Self::Transit)
    }

    /// Gets the definition of this level from [`STANDARD_LEVELS`] or [`TRANSIT_LEVEL`].
    #[inline]
    #[must_use]
    pub fn definition(self) -> &'static TileLevel {
        match self {
            Self::Highway => &STANDARD_LEVELS[0],
            Self::Arterial => &STANDARD_LEVELS[1],
            Self::Local => &STANDARD_LEVELS[2],
            Self::Transit => &TRANSIT_LEVEL,
        }
    }
}

impl TryFrom<u8> for ValhallaLevel {
    type Error = UnknownLevelError;

    #[inline]
    fn try_from(level: u8) -> Result<Self, Self::Error> {
        match level {
            0 => Ok(Self::Highway),
            1 => Ok(Self::Arterial),
            2 => Ok(Self::Local),
            3 => Ok(Self::Transit),
            other => Err(UnknownLevelError(other)),
        }
    }
}

impl From<ValhallaLevel> for u8 {
    #[inline]
    fn from(level: ValhallaLevel) -> Self {
        level.number()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tile_hierarchy::STANDARD_LEVELS;

    /// Helper to compute the base tile GraphId at (x, y) for a given level.
    fn base_tile_id(level: &TileLevel, x: i64, y: i64) -> GraphId {
        let width = i64::from(level.tiling_system.n_cols);
        let tile_index = (y * width + x) as u64;
        GraphId::try_from_components(level.level, tile_index, 0)
            .expect("valid base tile GraphId in test")
    }

    #[test]
    fn bbox_inside_single_tile() {
        let level = &STANDARD_LEVELS[0];
        let size = f64::from(level.tiling_system.tile_size);
        let width = i64::from(level.tiling_system.n_cols);
        let height = i64::from(level.tiling_system.n_rows);
        assert!(width > 0 && height > 0);

        // Pick a tile somewhere in the grid (center-ish if possible).
        let x = width / 2;
        let y = height / 2;

        let west = -180.0 + (x as f64) * size;
        let east = west + size;
        let south = -90.0 + (y as f64) * size;
        let north = south + size;

        // Bbox strictly inside that tile.
        let ids: Vec<GraphId> = level.tiles_intersecting_bbox(
            north - 0.1 * size,
            east - 0.1 * size,
            south + 0.1 * size,
            west + 0.1 * size,
        );

        assert_eq!(ids, vec![base_tile_id(level, x, y)]);
    }

    #[test]
    fn bbox_spans_a_row_of_tiles() {
        let level = &STANDARD_LEVELS[0];
        let size = f64::from(level.tiling_system.tile_size);
        let width = i64::from(level.tiling_system.n_cols);
        assert!(width >= 2);

        // Use row 0: lat band from -90 to -90+size.
        let y = 0_i64;
        let south = -90.0 + 0.1 * size;
        let north = -90.0 + 0.9 * size;

        // Bbox spanning almost entire longitude range, no wrap.
        let west = -179.9;
        let east = 179.9;

        let mut ids: Vec<GraphId> = level.tiles_intersecting_bbox(north, east, south, west);
        ids.sort_by_key(|gid| gid.value());

        let expected: Vec<GraphId> = (0..width).map(|x| base_tile_id(level, x, y)).collect();
        assert_eq!(ids, expected);
    }

    #[test]
    fn bbox_crosses_antimeridian_hits_edge_tiles() {
        let level = &STANDARD_LEVELS[0];
        let size = f64::from(level.tiling_system.tile_size);
        let width = i64::from(level.tiling_system.n_cols);
        assert!(width >= 2);

        // Use bottom row
        let y = 0_i64;
        let south = -90.0 + 0.1 * size;
        let north = -90.0 + 0.9 * size;

        // Bbox that crosses the antimeridian: west ~ +179, east ~ -179.
        let west = 179.0;
        let east = -179.0;

        let ids: Vec<GraphId> = level.tiles_intersecting_bbox(north, east, south, west);

        let first = base_tile_id(level, 0, y);
        let last = base_tile_id(level, width - 1, y);

        // It should include only the leftmost and rightmost tiles in that row.
        assert_eq!(ids.len(), 2);
        assert!(ids.contains(&first));
        assert!(ids.contains(&last));
    }

    #[test]
    fn bbox_on_tile_boundaries_includes_neighboring_tiles_level_0() {
        let level = &STANDARD_LEVELS[0];
        let size = f64::from(level.tiling_system.tile_size);

        // Use bottom-left tile at (x=0, y=0):
        // lon: [-180, -180 + size], lat: [-90, -90 + size]
        let west = -180.0;
        let east = -180.0 + size;
        let south = -90.0;
        let north = -90.0 + size;

        let ids: Vec<GraphId> = level.tiles_intersecting_bbox(north, east, south, west);
        assert_eq!(ids.len(), 4);

        assert!(ids.contains(&base_tile_id(level, 0, 0)));
        assert!(ids.contains(&base_tile_id(level, 1, 0)));
        assert!(ids.contains(&base_tile_id(level, 0, 1)));
        assert!(ids.contains(&base_tile_id(level, 1, 1)));
    }

    #[test]
    fn bbox_on_tile_boundaries_includes_neighboring_tiles_level_1() {
        // Same as the above test area-wise, but covers 25 tiles at level 1 instead!
        let level = &STANDARD_LEVELS[1];
        let size = f64::from(level.tiling_system.tile_size);

        // Use bottom-left tile at (x=0, y=0):
        // lon: [-180, -180 + size], lat: [-90, -90 + size]
        let west = -180.0;
        let east = -180.0 + size;
        let south = -90.0;
        let north = -90.0 + size;

        let ids: Vec<GraphId> = level.tiles_intersecting_bbox(north, east, south, west);
        assert_eq!(ids.len(), 4);

        assert!(ids.contains(&base_tile_id(level, 0, 0)));
        assert!(ids.contains(&base_tile_id(level, 1, 0)));
        assert!(ids.contains(&base_tile_id(level, 0, 1)));
        assert!(ids.contains(&base_tile_id(level, 1, 1)));
    }

    #[test]
    fn test_base_tile_id() {
        // Test the base_tile_id function
        let level = &STANDARD_LEVELS[0];
        assert_eq!(
            base_tile_id(level, 0, 0),
            GraphId::try_from_components(0, 0, 0).unwrap()
        );
        assert_eq!(
            base_tile_id(level, 1, 0),
            GraphId::try_from_components(0, 1, 0).unwrap()
        );
        assert_eq!(
            base_tile_id(level, 0, 1),
            GraphId::try_from_components(0, 90, 0).unwrap()
        );
        assert_eq!(
            base_tile_id(level, 1, 1),
            GraphId::try_from_components(0, 91, 0).unwrap()
        );

        // Same idea for level 1
        let level = &STANDARD_LEVELS[1];
        assert_eq!(
            base_tile_id(level, 0, 0),
            GraphId::try_from_components(1, 0, 0).unwrap()
        );
        assert_eq!(
            base_tile_id(level, 1, 0),
            GraphId::try_from_components(1, 1, 0).unwrap()
        );
        assert_eq!(
            base_tile_id(level, 0, 1),
            GraphId::try_from_components(1, 360, 0).unwrap()
        );
        assert_eq!(
            base_tile_id(level, 1, 1),
            GraphId::try_from_components(1, 361, 0).unwrap()
        );
    }

    #[test]
    fn test_valhalla_level_round_trip() {
        for level in ValhallaLevel::ALL {
            assert_eq!(ValhallaLevel::try_from(level.number()), Ok(level));
            assert_eq!(u8::from(level), level.number());
            assert_eq!(level.definition().level, level.number());
        }
        assert_eq!(ValhallaLevel::Local.definition().name, "local");
        assert_eq!(ValhallaLevel::Transit.definition().name, "transit");
        assert!(ValhallaLevel::Transit.is_transit());
        assert!(ValhallaLevel::STANDARD.iter().all(|l| !l.is_transit()));

        for level in 4..=u8::MAX {
            assert_eq!(
                ValhallaLevel::try_from(level),
                Err(UnknownLevelError(level))
            );
        }
    }

    #[test]
    fn test_standard_levels_match_definitions() {
        let standard: Vec<_> = ValhallaLevel::STANDARD
            .iter()
            .map(|level| level.definition().level)
            .collect();
        let statics: Vec<_> = STANDARD_LEVELS.iter().map(|level| level.level).collect();
        assert_eq!(standard, statics);
    }
}
