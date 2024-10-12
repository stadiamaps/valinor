use crate::GraphId;
use thiserror::Error;

// TODO: mmapped tarball version
mod directory_tile_provider;

use crate::graph_id::InvalidGraphIdError;
use crate::graph_tile::{GraphTile, GraphTileError, LookupError};
pub use directory_tile_provider::DirectoryTileProvider;

#[derive(Debug, Error)]
pub enum GraphTileProviderError {
    #[error("This tile does not exist (ex: in your extract)")]
    TileDoesNotExist,
    #[error("Error fetching tile: {0}")]
    TileFetchError(String),
    #[error("Invalid graph ID: {0}")]
    InvalidGraphId(#[from] InvalidGraphIdError),
    #[error("IO Error: {0}")]
    IoError(#[from] std::io::Error),
    #[error("Graph tile error: {0}")]
    GraphTileError(#[from] GraphTileError),
    #[error("Graph tile lookup error: {0}")]
    GraphTileLookupError(#[from] LookupError),
}

pub trait GraphTileProvider {
    // TODO: Should this return an owned structure or a pointer?
    // TODO: Should this be async? Seems like it to allow network retrieval.
    /// Gets a tile with the given graph ID.
    ///
    /// # Errors
    ///
    /// This operation may fail for several reasons,
    /// including the tile not existing, I/O errors, and more.
    /// Refer to [`GraphTileProviderError`] for details.
    ///
    /// # Implementation notes
    ///
    /// Implementations should ensure that they look up the base ID for IDs that are passed in
    /// with [`GraphId::tile_base_id`].
    fn get_tile(&self, graph_id: &GraphId) -> Result<GraphTile, GraphTileProviderError>;

    /// Gets the opposing edge and the tile containing it.
    ///
    /// # Performance
    ///
    /// This method always has to do a tile lookup (potentially cached, but a lookup nonetheless).
    /// TODO: Provide APIs which will try to use the existing tile
    fn get_opposing_edge(
        &self,
        graph_id: &GraphId,
    ) -> Result<Option<(GraphId, GraphTile)>, GraphTileProviderError> {
        let tile = self.get_tile(graph_id)?;
        let edge = tile.get_directed_edge(graph_id)?;

        // Valhalla does not currently implement this method for transit edges
        // TODO: Does such a check belong in this method?
        if edge.is_transit_line() {
            return Ok(None);
        }

        // The edge might leave the tile, so we have to do a complicated lookup
        let end_node_id = edge.end_node_id();
        let opp_edge_index = edge.opposing_edge_index();

        // TODO: Probably a cleaner pattern here?
        let (opp_tile, node_edge_index) = match tile.get_node(&end_node_id).map(|n| n.edge_index())
        {
            Ok(index) => (tile, index),
            Err(LookupError::MismatchedBase) => {
                let tile = self.get_tile(&end_node_id)?;
                let index = tile.get_node(&end_node_id)?.edge_index();
                (tile, index)
            }
            Err(LookupError::InvalidIndex) => return Err(LookupError::InvalidIndex)?,
        };

        // Construct an ID with the index set to the opposing edge
        let id = GraphId::try_from_components(
            end_node_id.level(),
            end_node_id.tile_id(),
            u64::from(node_edge_index + opp_edge_index),
        )?;

        // TODO: Should we try to return the edge too?
        // let edge = opp_tile.get_directed_edge(&id)?;

        Ok(Some((id, opp_tile)))
    }
    // TODO: Coordinate, bbox, etc. (can have implementations that are generic!!)
}
