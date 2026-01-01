//! # Graph tile providers
//!
//! This module contains implementations for several graph tile providers.
//! Note that there is currently no single generic trait for accessing tiles,
//! due to the fundamental difference in how memory maps work vs file systems.

use crate::GraphId;
use dashmap::DashMap;
use geo::{CoordFloat, Point};
use num_traits::FromPrimitive;
use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::Mutex;
use thiserror::Error;

mod directory;
mod tarball;
mod traffic;

use crate::graph_id::InvalidGraphIdError;
use crate::graph_tile::{
    GraphNode, GraphTile, GraphTileDecodingError, GraphTileView, LookupError, NodeInfo,
    OpposingEdgeIndex,
};
pub use directory::DirectoryGraphTileProvider;
pub use tarball::TarballTileProvider;
pub use traffic::TrafficTileProvider;

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
    #[error("Decoding error: {0}")]
    DecodingError(#[from] GraphTileDecodingError),
    #[error("Graph tile lookup error: {0}")]
    GraphTileLookupError(#[from] LookupError),
    #[error("Cache lock is poisoned: {0}")]
    PoisonedCacheLock(String),
    #[error("Invalid tarball: {0}")]
    InvalidTarball(String),
    #[error("Unsupported tile version; this may or may not be compatible.")]
    UnsupportedTileVersion,
}

pub trait GraphTileProvider {
    /// Gets the tile containing the given graph ID,
    /// and does some work in a closure which takes the reference as a parameter.
    ///
    /// # Performance
    ///
    /// This may or may not make use of caches,
    /// require filesystem access, etc.
    /// This is left up to the implementation.
    ///
    /// # Errors
    ///
    /// This operation may fail for several reasons,
    /// including the tile not existing, I/O errors, and more.
    /// Refer to [`GraphTileProviderError`] for details.
    fn with_tile_containing<F, T>(
        &self,
        graph_id: GraphId,
        process: F,
    ) -> Result<T, GraphTileProviderError>
    where
        F: FnOnce(&GraphTileView) -> T;

    /// Enumerate base tile Graph IDs across all hierarchy levels that intersect a circle around
    /// `center` with radius `radius`.
    ///
    /// Assumes that `center` is a valid geographic coordinate (lat+lon).
    /// `radius` is specified in meters.
    ///
    /// # Implementation note
    ///
    /// All returned tiles MUST be accessible by the provider (callers are allowed to assume this).
    fn enumerate_tiles_within_radius<N: CoordFloat + FromPrimitive>(
        &self,
        center: Point<N>,
        radius: N,
    ) -> Vec<GraphId>;

    /// Gets a tile containing the given graph ID, or else panics.
    ///
    /// This is an unfortunately necessary convenience,
    /// since some use cases involve use in contexts where failure is not encodable
    /// in the type signature.
    ///
    /// Uses [`GraphTileProvider::with_tile_containing`] under the hood.
    ///
    /// # Panics
    ///
    /// This will panic if the tile can't be loaded.
    fn with_tile_containing_or_panic<F, T>(&self, graph_id: GraphId, process: F) -> T
    where
        F: FnOnce(&GraphTileView) -> T,
    {
        self.with_tile_containing(graph_id, process)
            .expect("Should be able to get a tile for this node (either the trait impl is incorrect or a tile has invalid data)")
    }

    /// Returns the [`GraphId`] for an opposing edge.
    ///
    /// The input for this typically comes from [`GraphTile::get_opp_edge_index`].
    /// Since the opposite edge may be in another tile, a [`GraphTileProvider`] is required
    /// to fully resolve it.
    ///
    /// # Performance
    ///
    /// If the opposing edge is contained in the same tile as `tile_hint`,
    /// this method can take a fast path; otherwise, it will need to fetch a tile.
    ///
    /// # Errors
    ///
    /// This can fail if an underlying tile load fails (e.g., an I/O error),
    /// or the `OpposingEdgeIndex` points to an invalid edge (e.g., corrupt / invalid tiles).
    fn graph_id_for_opposing_edge_index(
        &self,
        OpposingEdgeIndex {
            end_node_id,
            opposing_edge_index,
        }: OpposingEdgeIndex,
        tile_hint: &GraphTileView,
    ) -> Result<GraphId, GraphTileProviderError> {
        match tile_hint.get_node(end_node_id).map(NodeInfo::edge_index) {
            // Fast path: same tile
            Ok(node_edge_idx) => Ok(tile_hint
                .header()
                .graph_id()
                .with_feature_index(u64::from(node_edge_idx + opposing_edge_index))?),
            // Slow path: fetch from another tile
            Err(LookupError::MismatchedBase) => self.with_tile_containing(end_node_id, |tile| {
                let node_edge_idx = tile.get_node(end_node_id)?.edge_index();
                Ok(tile
                    .header()
                    .graph_id()
                    .with_feature_index(u64::from(node_edge_idx + opposing_edge_index))?)
            })?,
            Err(e) => Err(e)?,
        }
    }

    /// Gets the opposing edge.
    ///
    /// All edges in a Valhalla graph are directed and stored as a pair.
    /// This function makes it easy to get the opposite one.
    ///
    /// # Errors
    ///
    /// This may fail under the following circumstances:
    ///
    /// - Failing to fetch the tile containing the graph ID
    /// - The index within the tile being invalid
    /// - Failing to fetch the tile containing the end node of the edge (or the end node therein)
    /// - Corrupt end node information in the tile
    ///
    /// # Performance
    ///
    /// This method will try to look up the edge in the tile view (`tile_hint`) first,
    /// to save a tile fetch (which might have a high overhead in some tile providers).
    fn get_opposing_edge_id(
        &self,
        edge_id: GraphId,
        tile_hint: &GraphTileView,
    ) -> Result<GraphId, GraphTileProviderError> {
        let get_opp_edge_id_from_tile =
            |tile: &GraphTileView| -> Result<GraphId, GraphTileProviderError> {
                let idx = tile.get_opp_edge_index(edge_id)?;

                // Construct an ID with the index set to the opposing edge
                // TODO: Should we try to return the edge too??
                self.graph_id_for_opposing_edge_index(idx, tile)
            };

        match get_opp_edge_id_from_tile(tile_hint) {
            // Fast path (opposide edge within this tile)
            Ok(edge_id) => Ok(edge_id),
            // Slow path (need to fetch an edge outside the tile)
            Err(GraphTileProviderError::GraphTileLookupError(LookupError::MismatchedBase)) => {
                self.with_tile_containing(edge_id, |tile| get_opp_edge_id_from_tile(tile))?
            }
            e => e,
        }
    }

    /// Gets the shortcut edge that includes the given edge, if any.
    ///
    /// `Ok(None)` indicates that either no shortcut was found for the provided edge,
    /// OR multiple shortcuts were found.
    fn get_shortcut(&self, id: GraphId) -> Result<Option<GraphId>, GraphTileProviderError> {
        if id.level() >= 2 {
            // Shortcuts don't exist on these levels
            return Ok(None);
        }

        // Helper to get the single continuing edge from a node, if uniquely determined.
        // Also reports whether any shortcut edges were present at the node.
        let find_continuing_edge =
            |tile: &GraphTileView,
             node: &NodeInfo,
             skip_edge_index: u32|
             -> Result<(Option<GraphId>, bool), GraphTileProviderError> {
                let edges = tile.get_outbound_edges_from_node(node);

                let mut candidate: Option<u32> = None; // store absolute index within tile
                let mut saw_shortcut = false;
                for (i, de) in edges.iter().enumerate() {
                    let abs_index = node.edge_index() + (i as u32);
                    if de.is_shortcut() {
                        saw_shortcut = true;
                    }
                    if abs_index == skip_edge_index || !de.can_form_shortcut() {
                        continue;
                    }
                    if candidate.is_some() {
                        // More than one possible continuing edge
                        return Ok((None, saw_shortcut));
                    }
                    candidate = Some(abs_index);
                }

                let cont = if let Some(idx) = candidate {
                    Some(
                        tile.header()
                            .graph_id()
                            .with_feature_index(u64::from(idx))?,
                    )
                } else {
                    None
                };
                Ok((cont, saw_shortcut))
            };

        self.with_tile_containing(id, |tile| {
            if tile.get_directed_edge(id).map(|e| e.is_shortcut())? {
                // If this edge is already a shortcut, return it as-is.
                return Ok(Some(id));
            }

            // Walk backwards along the opposing directed edge until a shortcut beginning is found
            // or until ambiguity / boundary conditions are encountered.
            let first_de_id = self.get_opposing_edge_id(id, tile)?;
            let mut cont_de_id: Option<GraphId> = Some(first_de_id);
            let mut prev_node_id: Option<GraphId> = None;
            let mut shortcut_at_node = false;

            loop {
                // Determine the continuing directed edge.
                if let Some(node_id) = prev_node_id {
                    // For all iterations beyond the first,
                    // get the continuing directed edge.
                    // The initial case will use the opposing directed edge
                    // from the starting edge (see pre-loop code).
                    let (opp_index, _) = self.with_tile_containing(
                        cont_de_id.expect("continuing edge must exist"),
                        |tile| {
                            let de = tile.get_directed_edge(cont_de_id.unwrap())?;
                            Ok::<_, GraphTileProviderError>((
                                de.opposing_edge_index(),
                                de.end_node_id(),
                            ))
                        },
                    )??;

                    let (next_cont, saw_short) = match tile.get_node(node_id) {
                        Ok(node) => {
                            // Fast path (stay within the same tile)
                            let skip_edge_index = node.edge_index() + opp_index;
                            find_continuing_edge(tile, node, skip_edge_index)?
                        }
                        Err(_) => {
                            // Slow path (need to load another tile)
                            self.with_tile_containing(node_id, |tile| {
                                let node = tile.get_node(node_id)?;
                                let skip_edge_index = node.edge_index() + opp_index;
                                Ok::<_, GraphTileProviderError>(find_continuing_edge(
                                    tile,
                                    node,
                                    skip_edge_index,
                                )?)
                            })??
                        }
                    };

                    shortcut_at_node = saw_short;
                    cont_de_id = next_cont;

                    if cont_de_id == Some(first_de_id) {
                        // Loop detected; no shortcut found
                        return Ok(None);
                    }
                }

                let Some(curr_cont_id) = cont_de_id else {
                    // No clear continuing edge
                    return Ok(None);
                };

                // The following is definitely not perfectly optimized, but it's "fast enough"
                // as far as we can tell from some stress tests (there's a fairly reasonable fast path
                // when everything is in the current tile, though it is not branch-free).
                // Get end node of the continuing edge and its node info
                let (end_node_id, opp_index) = match tile.get_directed_edge(curr_cont_id) {
                    Ok(de) => (de.end_node_id(), de.opposing_edge_index()),
                    Err(LookupError::MismatchedBase) => {
                        self.with_tile_containing(curr_cont_id, |tile| {
                            let de = tile.get_directed_edge(curr_cont_id)?;
                            Ok::<_, GraphTileProviderError>((
                                de.end_node_id(),
                                de.opposing_edge_index(),
                            ))
                        })??
                    }
                    Err(e) => return Err(e.into()),
                };

                // Get the node info (may reside in a different tile if the edge leaves tile)
                let node_edge_index = match tile.get_node(end_node_id) {
                    Ok(node) => node.edge_index(),
                    Err(LookupError::MismatchedBase) => self
                        .with_tile_containing(end_node_id, |tile| {
                            tile.get_node(end_node_id).map(NodeInfo::edge_index)
                        })??,
                    Err(e) => return Err(e.into()),
                };

                // Construct the opposing edge id at the end node (the edge we "arrived on" at this node)
                let arriving_edge_id =
                    end_node_id.with_feature_index(u64::from(node_edge_index + opp_index))?;

                // Inspect the arriving edge to see if it is superseded (i.e., shortcut starts here)
                let superseded_idx = match tile.get_directed_edge(arriving_edge_id) {
                    Ok(de) => de.superseded_index(),
                    Err(LookupError::MismatchedBase) => {
                        self.with_tile_containing(arriving_edge_id, |tile| {
                            let de = tile.get_directed_edge(arriving_edge_id)?;
                            Ok::<_, GraphTileProviderError>(de.superseded_index())
                        })??
                    }
                    Err(e) => return Err(e.into()),
                };

                if superseded_idx.is_none() && shortcut_at_node {
                    // Found a shortcut at the node, but it doesn't supersede the arriving edge.
                    // This implies we started outside a shortcut's internal edges.
                    return Ok(None);
                }

                if let Some(idx) = superseded_idx {
                    // Calculate the shortcut index within the node's outbound edges
                    let shortcut_abs_index = u64::from(node_edge_index + idx);
                    let shortcut_id = end_node_id.with_feature_index(shortcut_abs_index)?;
                    return Ok(Some(shortcut_id));
                }

                // Prepare for next iteration: continue from this node
                prev_node_id = Some(end_node_id);
            }
        })?
    }

    /// Creates an iterator over all nodes within a given radius of a point.
    ///
    /// No sorting or filtering of nodes is performed besides ensuring that they are close enough.
    /// The distance returned (second tuple element) is approximate,
    /// but should be accurate to within 1 meter for radii of up to 20km.
    ///
    /// # Performance
    ///
    /// This method is designed to give results with as little overhead as possible:
    ///
    /// - It only buffers results internally for one tile at a time.
    /// - The iteration order is not guaranteed to follow any particular sorting.
    /// - Internally, an approximator is used to (very!) quickly weed out unrealistic candidates
    ///   before doing the heavier trigonometry.
    ///
    /// # Panics
    ///
    /// This isn't intended to be used to get nodes over large distances.
    /// In debug builds, this will panic if `radius_in_meters` is larger than 20,000 (20km).
    ///
    /// Also panics if you provide non-finite floating point values (e.g., NaN or infinity).
    #[inline]
    fn nodes_within_radius<N: CoordFloat + FromPrimitive, F, T>(
        &self,
        center: Point<N>,
        radius_in_meters: N,
        op: F,
    ) -> impl Iterator<Item = Result<T, GraphTileProviderError>>
    where
        F: FnMut(GraphNode<'_>, N) -> T,
        Self: Sized,
    {
        NodesWithinRadius {
            provider: self,
            center,
            radius_in_meters,
            op,
            tiles: self
                .enumerate_tiles_within_radius(center, radius_in_meters)
                .into_iter(),
            buffer: VecDeque::new(),
        }
    }
}

pub trait OwnedGraphTileProvider<T: GraphTile>: GraphTileProvider {
    /// Gets a tile containing the given graph ID.
    ///
    /// The result is an owned handle to a graph tile,
    /// which implements the [`GraphTile`](GraphTile) trait.
    ///
    /// # Errors
    ///
    /// This operation may fail for several reasons,
    /// including the tile not existing, I/O errors, and more.
    /// Refer to [`GraphTileProviderError`] for details.
    fn get_handle_for_tile_containing(
        &self,
        graph_id: GraphId,
    ) -> Result<T, GraphTileProviderError>;
}

/// A keyed lock.
///
/// This enables more granular locking than over an entire data structure.
pub(crate) struct LockTable<K>(DashMap<K, Arc<Mutex<()>>>);

impl<K: std::hash::Hash + Eq + Clone> LockTable<K> {
    pub fn new() -> Self {
        Self(DashMap::new())
    }

    pub fn lock_for(&self, k: K) -> Arc<Mutex<()>> {
        self.0
            .entry(k)
            .or_insert_with(|| Arc::new(Mutex::new(())))
            .clone()
    }
}

/// An iterator over nodes within a given radius.
///
/// Used internally and returned as an opaque `impl Iterator`.
struct NodesWithinRadius<'prov, P, N, F, T, I>
where
    P: GraphTileProvider,
    N: CoordFloat + FromPrimitive,
    F: for<'t> FnMut(GraphNode<'t>, N) -> T,
    I: Iterator<Item = GraphId>,
{
    provider: &'prov P,
    center: Point<N>,
    radius_in_meters: N,
    op: F,
    tiles: I,
    buffer: VecDeque<T>,
}

impl<'prov, P, N, F, T, I> Iterator for NodesWithinRadius<'prov, P, N, F, T, I>
where
    P: GraphTileProvider,
    N: CoordFloat + FromPrimitive,
    F: for<'t> FnMut(GraphNode<'t>, N) -> T,
    I: Iterator<Item = GraphId>,
{
    type Item = Result<T, GraphTileProviderError>;

    fn next(&mut self) -> Option<Self::Item> {
        // Try to get an item from the buffer
        if let Some(next) = self.buffer.pop_front() {
            return Some(Ok(next));
        }

        // Fill the buffer if needed
        let base_id = self.tiles.next()?;
        if let Err(err) = self.provider.with_tile_containing(base_id, |tile| {
            self.buffer.extend(
                tile.nodes_within_radius(self.center, self.radius_in_meters)
                    .map(|(gn, approx_dist)| (self.op)(gn, approx_dist)),
            );
        }) {
            return Some(Err(err));
        }

        // After filling from the tile, either return the first item or keep iterating
        self.buffer.pop_front().map(Ok).or_else(|| self.next())
    }
}

#[cfg(test)]
mod tests {
    use crate::GraphId;
    use crate::graph_tile::GraphTile;
    use crate::tile_provider::{DirectoryGraphTileProvider, GraphTileProvider};
    use geo::{Destination, Haversine, point};
    use std::num::NonZeroUsize;
    use std::path::PathBuf;

    #[test]
    fn haversine_antimeridian_wraps() {
        // Wrapping from east -> west
        let projected = Haversine.destination(point!(x: 179.9, y: 0.0), 90.0, 50_000.0);
        assert!(projected.x() < -179.0);
        assert!(projected.x() > -180.0);

        // Wrapping the other way
        let projected = Haversine.destination(point!(x: -179.9, y: 0.0), 270.0, 50_000.0);
        assert!(projected.x() > 179.0);
        assert!(projected.x() < 180.0);
    }

    #[test]
    fn test_nodes_within_radius() {
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryGraphTileProvider::new(base, NonZeroUsize::new(4).unwrap());
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        provider.with_tile_containing_or_panic(graph_id, |tile_view| {
            let sw = tile_view.header().sw_corner();

            for (idx, node) in tile_view.nodes().into_iter().enumerate() {
                assert!(
                    provider
                        .nodes_within_radius(
                            node.coordinate(sw).into(),
                            25.0,
                            |graph_node, distance| { (graph_node.node_id, distance) }
                        )
                        .any(|res| {
                            match res {
                                Ok((node_id, distance)) => {
                                    node_id
                                        == tile_view
                                            .header()
                                            .graph_id()
                                            .with_feature_index(idx as u64)
                                            .unwrap()
                                        && distance == 0.0
                                }
                                Err(e) => {
                                    panic!("Error searching for nodes: {:?}", e);
                                }
                            }
                        }),
                    "Expected to find a match for the node"
                );
            }
        })
    }
}
