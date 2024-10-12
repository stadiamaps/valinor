use std::fmt::{Display, Formatter};
use crate::tile_hierarchy::{STANDARD_LEVELS, TRANSIT_LEVEL};
use std::path::PathBuf;
use thiserror::Error;

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

/// The maximum graph ID (not to be confused with the graph tile ID).
const MAX_GRAPH_ID: u64 = (1 << 46) - 1;

#[derive(Debug, Error, PartialEq)]
pub enum InvalidGraphIdError {
    #[error("Level is larger than the maximum allowed value.")]
    Level,
    #[error("Tile ID is larger than the maximum allowed value.")]
    GraphTileId,
    #[error("Tile index is larger than the maximum allowed value.")]
    TileIndex,
    #[error("Graph ID is invalid")]
    GraphId,
}

/// An Identifier of a node or an edge within the tiled, hierarchical graph.
/// It packs a tile ID, hierarchy level, and a unique identifier within
/// the tile/level into a 64-bit integer.
///
/// Bit fields within the ID include:
///   - 3 bits for hierarchy level (these are the least significant 3 bits)
///   - 22 bits for tile ID (supports lat,lon tiles down to 1/8 degree)
///   - 21 bits for the index within the tile
///
/// Note that there are only 46 used bits in the scheme (ask Valhalla's authors why 46).
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct GraphId(u64);

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
    pub fn try_from_components(
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
            Ok(Self(u64::from(level) | (tile_id << 3) | index << 25))
        }
    }

    /// Creates a graph ID from the given raw value.
    ///
    /// # Errors
    ///
    /// This function will fail if the graph ID is obviously invalid
    /// (greater than 46 bits wide).
    pub fn try_from_id(id: u64) -> Result<Self, InvalidGraphIdError> {
        // Simple check since we know the max bit width
        if id > MAX_GRAPH_ID {
            Err(InvalidGraphIdError::GraphId)
        } else {
            Ok(GraphId(id))
        }
    }

    /// Creates a graph ID from the given raw value without doing any validity checks.
    ///
    /// # Safety
    ///
    /// If you know that the value cannot possibly be larger than 46 bits,
    /// this is safe.
    /// Otherwise, you may risk things like invalid level indexes,
    /// which could cause unexpected behavior elsewhere.
    pub unsafe fn from_id_unchecked(id: u64) -> Self {
        Self(id)
    }

    /// Extracts the raw (packed) graph ID value.
    #[inline]
    pub const fn value(&self) -> u64 {
        self.0
    }

    /// Gets the hierarchy level.
    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    pub const fn level(&self) -> u8 {
        (self.value() & MAX_HIERARCHY_LEVEL as u64) as u8
    }

    /// Gets the graph tile ID.
    #[inline]
    pub const fn tile_id(&self) -> u64 {
        (self.value() & 0x01ff_fff8) >> 3
    }

    /// Gets the unique identifier (index) within the hierarchy level.
    #[inline]
    pub const fn tile_index(&self) -> u64 {
        (self.value() & 0x3fff_fe00_0000) >> 25
    }

    /// Returns a [`GraphId`] which omits the index within the level.
    /// This is useful primarily for deriving file names.
    #[inline]
    #[must_use]
    pub const fn tile_base_id(&self) -> GraphId {
        GraphId(self.value() & 0x01ff_ffff)
    }

    /// Constructs a relative path for the given tile.
    ///
    /// # Errors
    ///
    /// This will fail if the tile is invalid for this level of tiling.
    /// TODO: It seems like we could do this check at tile creation time?
    pub fn file_path(&self, extension: &str) -> Result<PathBuf, InvalidGraphIdError> {
        // This is quite ugly and prone to failure; this is a pretty literal C++ translation
        let level_number = self.level();
        let level = if level_number == TRANSIT_LEVEL.level {
            &*TRANSIT_LEVEL
        } else {
            &STANDARD_LEVELS[level_number as usize]
        };

        let max_id = level.tiling_system.n_cols * level.tiling_system.n_rows - 1;
        let tile_id = self.tile_id();
        if tile_id > u64::from(max_id) {
            return Err(InvalidGraphIdError::GraphTileId);
        }

        let l = max_id.max(1).ilog10() + 1;
        let rem = l % 3;
        let n_digits = if rem == 0 { l } else { l + (3 - rem) };
        debug_assert!(n_digits % 3 == 0);

        // This may not be as efficient as the Valhalla implementation, but it's more readable.
        // Format tile_id with leading zeros to match max_length
        let padded_id = format!("{:0>width$}", tile_id, width = n_digits as usize);
        let tile_id_chars: Vec<_> = padded_id.chars().collect();
        // Create the final path using groups of threes
        let tile_id_component = tile_id_chars
            .rchunks(3)
            .fold(PathBuf::new(), |acc, chunk| {
                PathBuf::from(chunk.iter().collect::<String>()).join(acc)
            })
            .with_extension(extension);

        // Build and return the final string
        Ok(PathBuf::from(self.level().to_string()).join(tile_id_component))
    }
}

impl Display for GraphId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("GraphId {}/{}/{}", self.level(), self.tile_id(), self.tile_index()))
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

        assert_eq!(graph_id, GraphId(0));
        assert_eq!(graph_id.level(), 0);
        assert_eq!(graph_id.tile_id(), 0);
        assert_eq!(graph_id.tile_index(), 0);
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
            GraphId(MAX_GRAPH_ID)
        );
        assert_eq!(graph_id.level(), MAX_HIERARCHY_LEVEL);
        assert_eq!(graph_id.tile_id(), MAX_GRAPH_TILE_ID);
        assert_eq!(graph_id.tile_index(), MAX_TILE_INDEX);
    }

    #[test]
    fn test_valid_tile_by_id() {
        let Ok(graph_id) = GraphId::try_from_id(MAX_GRAPH_ID) else {
            panic!("Expected that we would construct a valid graph ID.")
        };

        assert_eq!(
            graph_id,
            // Note: only 46 bits actually used
            GraphId(MAX_GRAPH_ID)
        );
        assert_eq!(graph_id.level(), MAX_HIERARCHY_LEVEL);
        assert_eq!(graph_id.tile_id(), MAX_GRAPH_TILE_ID);
        assert_eq!(graph_id.tile_index(), MAX_TILE_INDEX);
    }

    #[test]
    fn test_invalid_tile_by_id() {
        assert_eq!(
            GraphId::try_from_id(MAX_GRAPH_ID + 1),
            // Note: only 46 bits actually used
            Err(InvalidGraphIdError::GraphId)
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
}
