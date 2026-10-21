use crate::tile_hierarchy::{STANDARD_LEVELS, TRANSIT_LEVEL};
use core::str::FromStr;
#[cfg(feature = "serde")]
use serde::{Serialize, Serializer};
use std::fmt::{Display, Formatter};
use std::path::PathBuf;
use thiserror::Error;
use zerocopy::{LE, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

/// The max valid hierarchy level.
///
/// There are 3 bits for the hierarchy level.
const MAX_HIERARCHY_LEVEL: u8 = (1 << 3) - 1;

/// The max valid tile ID.
///
/// There are 22 bits for the tile ID.
const MAX_GRAPH_TILE_ID: u64 = (1 << 22) - 1;

/// The max valid tile index.
///
/// There are 21 bits for the index within the tile
const MAX_TILE_INDEX: u64 = (1 << 21) - 1;

/// All 46 bits set to 1
const INVALID_GRAPH_ID: u64 = (1 << 46) - 1;

#[derive(Debug, Error, PartialEq)]
pub enum InvalidGraphIdError {
    #[error("Level is larger than the maximum allowed value.")]
    Level,
    #[error("Tile ID is larger than the maximum allowed value.")]
    GraphTileId,
    #[error("Tile index is larger than the maximum allowed value.")]
    TileIndex,
    #[error("Graph ID is invalid")]
    InvalidGraphId,
}

/// The reasons why a string is not a valid graph ID or tile.
#[derive(Debug, Error, PartialEq)]
pub enum ParseGraphIdError {
    /// The input does not have the expected number of `/`-separated components.
    #[error("'{input}' is not in the {expected} form")]
    Format {
        input: String,
        /// The expected form (e.g. `level/tile_id`).
        expected: &'static str,
    },
    /// A component of the input is not a non-negative integer.
    #[error("the {component} in '{input}' is not a valid number")]
    Component {
        input: String,
        /// The name of the component (e.g. `level`).
        component: &'static str,
    },
    /// The components are numbers, but they do not make a valid graph ID.
    #[error("'{input}' is not a valid graph ID: {source}")]
    Invalid {
        input: String,
        source: InvalidGraphIdError,
    },
}

/// An Identifier of a node or an edge within the tiled, hierarchical graph.
/// It packs a hierarchy level, tile ID, and an identifier within
/// the tile/level into a 64-bit integer.
///
/// # Hierarchy (level + Tile ID)
///
/// Valhalla organizes tiles into several levels.
/// For a description of the common ones, see [`STANDARD_LEVELS`]
/// and [`TRANSIT_LEVEL`].
/// Each level includes progressively more "local" roads.
/// This helps improve efficiency.
///
/// Each level contains square tiles of a fixed size (noted in the level definition).
/// And within each tile, features are identified by a node or edge index.
///
/// # Feature index and overloading
///
/// The identifier field points to a specific feature within a graph tile.
/// The same identifier format is used for multiple features,
/// so make sure you know which you're dealing with!
///
/// The feature index is simply an index of _some_ feature within a list in the tile.
/// This struct does not encode any information on what type of feature is being referenced
/// (e.g. and edge or node).
///
/// This is normally evident form the API surface, but this is not enforced at the type level.
///
/// ## Future ideas to explore
///
/// - Hiding most uses of this type from the public API and using an enum
/// - Using the reserved area to indicate type
///   (NOTE: This would probably be a Valinor-only change if we did this short term,
///   since it would be a breaking change.)
///
/// # Bit field layout
///
/// Here is a lovely ANSI art diagram of the bit field layout
/// from the Valhalla documentation, lightly modified for clarity.
///
/// ```text
///        MSb                                     LSb
///        ▼                                       ▼
/// bit   64         46        25         3        0
/// pos    ┌──────────┬───────────────┬────────┬───────┐
///        │ RESERVED │ feature index │ tileid │ level │
///        └──────────┴───────────────┴────────┴───────┘
/// size     18         21        22        3
///```
///
/// Note that there are only 46 used bits in the scheme (ask Valhalla's authors why 46).
#[repr(C)]
#[derive(IntoBytes, Immutable, Unaligned, FromBytes, Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct GraphId(U64<LE>);

impl GraphId {
    // TBD: Should we use u64 everywhere? We need to cast AND bounds check anyway.
    /// Tries to construct a Graph ID from the given components.
    ///
    /// # Errors
    ///
    /// This will fail if any argument contains a value greater than the allowed number of field bits.
    /// - `level` - 3 bits
    /// - `tile_id` - 22 bits
    /// - `index` - 21 bits
    #[inline]
    pub const fn try_from_components(
        level: u8,
        tile_id: u64,
        index: u64,
    ) -> Result<Self, InvalidGraphIdError> {
        if level > MAX_HIERARCHY_LEVEL {
            Err(InvalidGraphIdError::Level)
        } else if tile_id > MAX_GRAPH_TILE_ID {
            Err(InvalidGraphIdError::GraphTileId)
        } else if index > MAX_TILE_INDEX {
            Err(InvalidGraphIdError::TileIndex)
        } else {
            Ok(Self(U64::<LE>::new(
                level as u64 | (tile_id << 3) | index << 25,
            )))
        }
    }

    /// Creates a graph ID from the given components without performing any validity checks.
    ///
    /// # Safety
    ///
    /// Invalid values risk things like out-of-bounds level indexes,
    /// which could cause crashes or other unexpected behavior.
    /// This is in some ways more unsafe than [`GraphId::from_id_unchecked`],
    /// since it is possible to specify an illegal field value (e.g. `level`),
    /// which will result in a completely bogus ID.
    pub const unsafe fn from_components_unchecked(level: u8, tile_id: u64, index: u64) -> Self {
        Self(U64::<LE>::new(level as u64 | (tile_id << 3) | index << 25))
    }

    /// Creates a graph ID from the given raw value.
    ///
    /// # Errors
    ///
    /// This function will fail if the graph ID fails to conform to the invariants.
    pub const fn try_from_id(id: u64) -> Result<Self, InvalidGraphIdError> {
        if id == INVALID_GRAPH_ID {
            return Err(InvalidGraphIdError::InvalidGraphId);
        }

        let result = GraphId(U64::<LE>::new(id));
        if result.level() > MAX_HIERARCHY_LEVEL {
            Err(InvalidGraphIdError::Level)
        } else if result.tile_id() > MAX_GRAPH_TILE_ID {
            Err(InvalidGraphIdError::GraphTileId)
        } else if result.feature_index() > MAX_TILE_INDEX {
            Err(InvalidGraphIdError::TileIndex)
        } else {
            Ok(result)
        }
    }

    /// Creates a graph ID from the given raw value without performing any validity checks.
    ///
    /// # Safety
    ///
    /// Invalid values risk things like out-of-bounds level indexes,
    /// which could cause crashes or other unexpected behavior.
    pub const unsafe fn from_id_unchecked(id: U64<LE>) -> Self {
        Self(id)
    }

    /// Creates a new graph ID from the existing one, but with a new feature index within the tile.
    ///
    /// # Errors
    ///
    /// See [`GraphId::try_from_components`] for a description of errors.
    #[inline]
    pub const fn with_feature_index(&self, tile_index: u64) -> Result<Self, InvalidGraphIdError> {
        Self::try_from_components(self.level(), self.tile_id(), tile_index)
    }

    /// Extracts the raw (packed) graph ID value.
    #[inline]
    pub const fn value(&self) -> u64 {
        self.0.get()
    }

    /// Gets the hierarchy level.
    #[inline]
    #[expect(clippy::cast_possible_truncation)]
    pub const fn level(&self) -> u8 {
        (self.value() & MAX_HIERARCHY_LEVEL as u64) as u8
    }

    /// Gets the graph tile ID.
    #[inline]
    pub const fn tile_id(&self) -> u64 {
        (self.value() & 0x01ff_fff8) >> 3
    }

    /// Gets the feature index within the tile.
    #[inline]
    pub const fn feature_index(&self) -> u64 {
        (self.value() & 0x3fff_fe00_0000) >> 25
    }

    /// Returns a [`GraphId`] which omits the feature index within the tile.
    ///
    /// This is useful primarily for deriving file names.
    #[inline]
    #[must_use]
    pub const fn tile_base_id(&self) -> GraphId {
        GraphId(U64::<LE>::new(self.value() & 0x01ff_ffff))
    }

    /// Parses the base graph ID of a tile from the `level/tile_id` form (e.g. `2/762485`).
    ///
    /// This is the tile form of [`GraphId::from_str`]:
    /// it names a whole tile, so it has no feature index component,
    /// and the feature index of the result is zero.
    /// Whitespace around each component is ignored.
    ///
    /// # Errors
    ///
    /// This fails if the input does not have exactly two `/`-separated components,
    /// if a component is not a non-negative integer,
    /// or if the level or tile ID is out of range (see [`GraphId::try_from_components`]).
    pub fn parse_tile(input: &str) -> Result<Self, ParseGraphIdError> {
        let [level, tile_id] = parse_components(input, "level/tile_id", ["level", "tile ID"])?;
        components_to_graph_id(input, level, tile_id, 0)
    }

    /// Constructs the relative path of the tile file for this graph ID,
    /// with `/` separators on every platform (e.g. `2/000/762/485.gph`).
    ///
    /// This is the form that Valhalla uses for tile directories, tar entry names, and tile URLs.
    /// The first component is the level;
    /// the rest is the tile ID, zero-padded to the width of the level
    /// and split into groups of three digits.
    /// The feature index is ignored.
    ///
    /// # Errors
    ///
    /// This will fail if the tile is invalid for this level of tiling.
    /// TODO: It seems like we could do this check at tile creation time?
    pub fn relative_path(&self, extension: &str) -> Result<String, InvalidGraphIdError> {
        let level_number = self.level();
        let level = if level_number == TRANSIT_LEVEL.level {
            &*TRANSIT_LEVEL
        } else {
            STANDARD_LEVELS
                .get(level_number as usize)
                .ok_or(InvalidGraphIdError::Level)?
        };

        let max_id = level.tiling_system.n_cols * level.tiling_system.n_rows - 1;
        let tile_id = self.tile_id();
        if tile_id > u64::from(max_id) {
            return Err(InvalidGraphIdError::GraphTileId);
        }

        // The width of the largest tile ID of the level, rounded up to a whole number of groups.
        let n_digits = (max_id.max(1).ilog10() + 1).next_multiple_of(3) as usize;
        let padded_id = format!("{tile_id:0>n_digits$}");

        let mut path = level_number.to_string();
        // The padded ID is ASCII digits, and its length is a multiple of 3,
        // so these byte ranges are always whole groups.
        for group_start in (0..n_digits).step_by(3) {
            path.push('/');
            path.push_str(&padded_id[group_start..group_start + 3]);
        }
        if !extension.is_empty() {
            path.push('.');
            path.push_str(extension);
        }

        Ok(path)
    }

    /// Constructs a relative path for the given tile.
    ///
    /// This is [`GraphId::relative_path`] as a [`PathBuf`],
    /// with the separators of the platform.
    ///
    /// # Errors
    ///
    /// This will fail if the tile is invalid for this level of tiling.
    pub fn file_path(&self, extension: &str) -> Result<PathBuf, InvalidGraphIdError> {
        Ok(self.relative_path(extension)?.split('/').collect())
    }
}

impl FromStr for GraphId {
    type Err = ParseGraphIdError;

    /// Parses a graph ID from its packed `u64` value (e.g. `16889572344463360`)
    /// or from the `level/tile_id/index` form (e.g. `2/762485/42`).
    ///
    /// To parse a whole tile in the `level/tile_id` form, use [`GraphId::parse_tile`].
    fn from_str(input: &str) -> Result<Self, Self::Err> {
        if let Ok(id) = input.trim().parse::<u64>() {
            return GraphId::try_from_id(id).map_err(|source| ParseGraphIdError::Invalid {
                input: input.to_string(),
                source,
            });
        }

        let [level, tile_id, index] = parse_components(
            input,
            "level/tile_id/index",
            ["level", "tile ID", "feature index"],
        )?;
        components_to_graph_id(input, level, tile_id, index)
    }
}

/// Splits `input` into exactly `N` `/`-separated integer components.
fn parse_components<const N: usize>(
    input: &str,
    expected: &'static str,
    names: [&'static str; N],
) -> Result<[u64; N], ParseGraphIdError> {
    let format_error = || ParseGraphIdError::Format {
        input: input.to_string(),
        expected,
    };

    let mut parts = input.split('/');
    let mut values = [0; N];
    for (value, component) in values.iter_mut().zip(names) {
        let part = parts.next().ok_or_else(format_error)?;
        *value = part
            .trim()
            .parse()
            .map_err(|_| ParseGraphIdError::Component {
                input: input.to_string(),
                component,
            })?;
    }
    if parts.next().is_some() {
        return Err(format_error());
    }

    Ok(values)
}

/// Converts parsed components into a graph ID, and reports range errors against `input`.
fn components_to_graph_id(
    input: &str,
    level: u64,
    tile_id: u64,
    index: u64,
) -> Result<GraphId, ParseGraphIdError> {
    let invalid = |source| ParseGraphIdError::Invalid {
        input: input.to_string(),
        source,
    };
    let level = u8::try_from(level).map_err(|_| invalid(InvalidGraphIdError::Level))?;
    GraphId::try_from_components(level, tile_id, index).map_err(invalid)
}

impl Ord for GraphId {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let level = self.level();
        let other_level = other.level();
        let tile_id = self.tile_id();
        let other_tile_id = other.tile_id();

        if level != other_level {
            // Different levels
            // NOTE: We implement the ordering by level in REVERSE!
            // This is because the call sites where we actually do sorting
            // typically start with an L2 tile first.
            // level.cmp(&other_level)
            other_level.cmp(&level)
        } else if tile_id != other_tile_id {
            // Same level, but different tile
            return tile_id.cmp(&other_tile_id);
        } else {
            // Same tile
            self.feature_index().cmp(&other.feature_index())
        }
    }
}

impl PartialOrd for GraphId {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for GraphId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "GraphId {}/{}/{}",
            self.level(),
            self.tile_id(),
            self.feature_index()
        ))
    }
}

#[cfg(feature = "serde")]
impl Serialize for GraphId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u64(self.0.get())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invalid_level() {
        assert_eq!(
            GraphId::try_from_components(MAX_HIERARCHY_LEVEL + 1, 0, 0),
            Err(InvalidGraphIdError::Level)
        );
    }

    #[test]
    fn test_invalid_tile_id() {
        assert_eq!(
            GraphId::try_from_components(0, MAX_GRAPH_TILE_ID + 1, 0),
            Err(InvalidGraphIdError::GraphTileId)
        );
    }

    #[test]
    fn test_invalid_tile_index() {
        assert_eq!(
            GraphId::try_from_components(0, 0, MAX_TILE_INDEX + 1),
            Err(InvalidGraphIdError::TileIndex)
        );
    }

    #[test]
    fn test_min_tile() {
        let Ok(graph_id) = GraphId::try_from_components(0, 0, 0) else {
            panic!("Expected that we would construct a valid graph ID.")
        };

        assert_eq!(graph_id, GraphId(0.into()));
        assert_eq!(graph_id.level(), 0);
        assert_eq!(graph_id.tile_id(), 0);
        assert_eq!(graph_id.feature_index(), 0);
    }

    #[test]
    fn test_max_tile() {
        let Ok(graph_id) =
            GraphId::try_from_components(MAX_HIERARCHY_LEVEL, MAX_GRAPH_TILE_ID, MAX_TILE_INDEX)
        else {
            panic!("Expected that we would construct a valid graph ID.")
        };

        assert_eq!(
            graph_id,
            // Note: only 46 bits actually used
            // TODO: HUH??
            GraphId(INVALID_GRAPH_ID.into())
        );
        assert_eq!(graph_id.level(), MAX_HIERARCHY_LEVEL);
        assert_eq!(graph_id.tile_id(), MAX_GRAPH_TILE_ID);
        assert_eq!(graph_id.feature_index(), MAX_TILE_INDEX);
    }

    #[test]
    fn test_valid_tile_by_id() {
        // This a very strange one.... but verified from live debugging a Valhalla process...
        let Ok(graph_id) = GraphId::try_from_id(16889572344463360) else {
            panic!("Expected that we would construct a valid graph ID.")
        };

        assert_eq!(graph_id, GraphId(16889572344463360.into()));
        assert_eq!(graph_id.level(), 0);
        assert_eq!(graph_id.tile_id(), 0);
        assert_eq!(graph_id.feature_index(), 32000);
    }

    #[test]
    fn test_invalid_tile_by_id() {
        assert_eq!(
            GraphId::try_from_id(INVALID_GRAPH_ID),
            // Note: only 46 bits actually used
            Err(InvalidGraphIdError::InvalidGraphId)
        );
    }

    #[test]
    fn test_graph_id_file_valid_suffixes() {
        // Level 2
        assert_eq!(
            GraphId::try_from_components(2, 2, 0)
                .unwrap()
                .file_path("gph"),
            Ok("2/000/000/002.gph".into())
        );
        assert_eq!(
            GraphId::try_from_components(2, 4, 0)
                .unwrap()
                .file_path("gph"),
            Ok("2/000/000/004.gph".into())
        );
        // Level 1
        assert_eq!(
            GraphId::try_from_components(1, 64799, 0)
                .unwrap()
                .file_path("gph"),
            Ok("1/064/799.gph".into())
        );
        // Level 0
        assert_eq!(
            GraphId::try_from_components(0, 49, 0)
                .unwrap()
                .file_path("gph"),
            Ok("0/000/049.gph".into())
        );
        // Transit level
        assert_eq!(
            GraphId::try_from_components(3, 1000000, 1)
                .unwrap()
                .file_path("gph"),
            Ok("3/001/000/000.gph".into())
        );
    }

    /// Helper to construct a base tile [`GraphId`].
    fn tile(level: u8, tile_id: u64) -> GraphId {
        GraphId::try_from_components(level, tile_id, 0).expect("valid tile ID in test")
    }

    #[test]
    fn test_relative_path() {
        // Levels 0 and 1 pad the tile ID to 6 digits (two groups);
        // level 2 pads to 9 digits (three groups).
        for (graph_id, expected) in [
            (tile(0, 3015), "0/003/015.gph"),
            (tile(0, 49), "0/000/049.gph"),
            (tile(1, 47_701), "1/047/701.gph"),
            (tile(1, 0), "1/000/000.gph"),
            (tile(2, 762_485), "2/000/762/485.gph"),
            (tile(2, 1_036_799), "2/001/036/799.gph"),
        ] {
            assert_eq!(graph_id.relative_path("gph").as_deref(), Ok(expected));
            // The file path is the same path with the separators of the platform.
            assert_eq!(
                graph_id.file_path("gph"),
                Ok(expected.split('/').collect::<PathBuf>())
            );
        }

        // The feature index is not part of the path.
        let with_index = GraphId::try_from_components(2, 762_485, 42).unwrap();
        assert_eq!(
            with_index.relative_path("gph").as_deref(),
            Ok("2/000/762/485.gph")
        );

        // An empty extension adds no dot.
        assert_eq!(
            tile(1, 47_701).relative_path("").as_deref(),
            Ok("1/047/701")
        );
    }

    #[test]
    fn test_relative_path_invalid() {
        // Level 0 has 45 rows and 90 columns of 4-degree tiles,
        // so its largest tile ID is 45 * 90 - 1 = 4049.
        assert_eq!(
            tile(0, 4049).relative_path("gph").as_deref(),
            Ok("0/004/049.gph")
        );
        assert_eq!(
            tile(0, 4050).relative_path("gph"),
            Err(InvalidGraphIdError::GraphTileId)
        );
        // Levels 4 to 7 fit in the bit field, but there is no tiling system for them.
        assert_eq!(
            tile(5, 0).relative_path("gph"),
            Err(InvalidGraphIdError::Level)
        );
    }

    #[test]
    fn test_parse_tile() {
        assert_eq!(GraphId::parse_tile("2/763926"), Ok(tile(2, 763_926)));
        assert_eq!(GraphId::parse_tile(" 0 / 3015 "), Ok(tile(0, 3015)));
    }

    #[test]
    fn test_parse_tile_invalid() {
        let format = |input: &str| ParseGraphIdError::Format {
            input: input.to_string(),
            expected: "level/tile_id",
        };
        assert_eq!(GraphId::parse_tile("2"), Err(format("2")));
        // A graph ID with a feature index is not a tile.
        assert_eq!(GraphId::parse_tile("2/763926/7"), Err(format("2/763926/7")));
        assert_eq!(
            GraphId::parse_tile("2/"),
            Err(ParseGraphIdError::Component {
                input: "2/".to_string(),
                component: "tile ID",
            })
        );
        assert_eq!(
            GraphId::parse_tile("x/763926"),
            Err(ParseGraphIdError::Component {
                input: "x/763926".to_string(),
                component: "level",
            })
        );
        assert_eq!(
            GraphId::parse_tile("-1/0"),
            Err(ParseGraphIdError::Component {
                input: "-1/0".to_string(),
                component: "level",
            })
        );
        // Levels have 3 bits, and tile IDs have 22 bits.
        for (input, source) in [
            ("8/0", InvalidGraphIdError::Level),
            ("256/0", InvalidGraphIdError::Level),
            ("0/4194304", InvalidGraphIdError::GraphTileId),
        ] {
            assert_eq!(
                GraphId::parse_tile(input),
                Err(ParseGraphIdError::Invalid {
                    input: input.to_string(),
                    source,
                })
            );
        }
    }

    #[test]
    fn test_from_str() {
        let expected = GraphId::try_from_components(2, 762_485, 42).unwrap();
        assert_eq!("2/762485/42".parse(), Ok(expected));
        assert_eq!(expected.value().to_string().parse(), Ok(expected));
        // Whitespace around a packed value is ignored.
        assert_eq!(
            " 16889572344463360 "
                .parse::<GraphId>()
                .map(|id| id.value()),
            Ok(16_889_572_344_463_360)
        );
    }

    #[test]
    fn test_from_str_invalid() {
        assert_eq!(
            "2/762485".parse::<GraphId>(),
            Err(ParseGraphIdError::Format {
                input: "2/762485".to_string(),
                expected: "level/tile_id/index",
            })
        );
        assert_eq!(
            "2/762485/x".parse::<GraphId>(),
            Err(ParseGraphIdError::Component {
                input: "2/762485/x".to_string(),
                component: "feature index",
            })
        );
        assert_eq!(
            INVALID_GRAPH_ID.to_string().parse::<GraphId>(),
            Err(ParseGraphIdError::Invalid {
                input: INVALID_GRAPH_ID.to_string(),
                source: InvalidGraphIdError::InvalidGraphId,
            })
        );
        assert_eq!(
            "0/0/2097152".parse::<GraphId>(),
            Err(ParseGraphIdError::Invalid {
                input: "0/0/2097152".to_string(),
                source: InvalidGraphIdError::TileIndex,
            })
        );
    }
}
