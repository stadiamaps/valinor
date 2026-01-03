use crate::GraphId;
use crate::graph_tile::{GraphTile, NodeInfo};
use crate::tile_provider::{GraphTileProvider, GraphTileProviderError};
use geo::{CoordFloat, Point};
use num_traits::FromPrimitive;
use std::collections::VecDeque;
use std::marker::PhantomData;

/// A handle to an object in the graph in response to a search.
pub struct GraphSearchResult<T, N: CoordFloat + FromPrimitive, H: GraphTile> {
    handle: H,
    graph_id: GraphId,
    approx_distance: N,
    _marker: PhantomData<T>,
}

impl<T, N: CoordFloat + FromPrimitive, H: GraphTile> GraphSearchResult<T, N, H> {
    /// The full graph ID of the result.
    #[inline]
    pub fn graph_id(&self) -> GraphId {
        self.graph_id
    }

    /// The approximate distance to the object from the query point.
    ///
    /// The distance is calculated using the squares approximator ([`crate::spatial::DistanceApproximator`]),
    /// which is not quite as accurate as Haversine distance, but is significantly faster and has
    /// acceptable error over short distances.
    #[inline]
    pub fn approx_distance(&self) -> N {
        self.approx_distance
    }
}

impl<N: CoordFloat + FromPrimitive, H: GraphTile> GraphSearchResult<NodeInfo, N, H> {
    /// Retrieves the node info for the graph node.
    ///
    /// # Performance
    ///
    /// This is a cheap operation, since this struct keeps an internal handle to the tile.
    #[inline]
    pub fn node_info(&self) -> &NodeInfo {
        // NB: This is not publicly constructible; we guarantee that the node is valid for the tile
        // when creating this struct internally, so the direct slice access is infallible.
        &self.handle.nodes()[self.graph_id.feature_index() as usize]
    }
}

/// An iterator over nodes within a given radius.
///
/// Used internally and returned as an opaque `impl Iterator`.
pub(super) struct NodesWithinRadius<'prov, P: GraphTileProvider, N: CoordFloat + FromPrimitive> {
    provider: &'prov P,
    center: Point<N>,
    radius_in_meters: N,
    tile_ids: Vec<GraphId>,
    buffer: VecDeque<GraphSearchResult<NodeInfo, N, P::TileHandle>>,
}

impl<'prov, P: GraphTileProvider, N: CoordFloat + FromPrimitive> NodesWithinRadius<'prov, P, N> {
    pub(super) fn new(
        provider: &'prov P,
        center: Point<N>,
        radius_in_meters: N,
        tile_ids: Vec<GraphId>,
    ) -> Self {
        Self {
            provider,
            center,
            radius_in_meters,
            tile_ids,
            buffer: VecDeque::new(),
        }
    }
}

impl<'prov, P: GraphTileProvider, N: CoordFloat + FromPrimitive> Iterator
    for NodesWithinRadius<'prov, P, N>
{
    type Item = Result<GraphSearchResult<NodeInfo, N, P::TileHandle>, GraphTileProviderError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node_ref) = self.buffer.pop_front() {
            return Some(Ok(node_ref));
        }

        let base_id = match self.tile_ids.pop() {
            Some(base_id) => base_id,
            None => return None,
        };

        let tile_handle = match self.provider.get_handle_for_tile_containing(base_id) {
            Ok(tile_handle) => tile_handle,
            Err(err) => {
                return Some(Err(err));
            }
        };

        // Stream items from the current tile, storing everything but the node info reference,
        // since we can reconstruct it later.
        // The tile handle clones are cheap (this is a documented assumption in the trait).
        let iter = tile_handle.nodes_within_radius(self.center, self.radius_in_meters);
        self.buffer
            .extend(iter.map(|(graph_node, distance)| GraphSearchResult {
                handle: tile_handle.clone(),
                graph_id: graph_node.node_id,
                approx_distance: distance,
                _marker: PhantomData,
            }));

        self.next()
    }
}
