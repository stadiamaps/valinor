//! # Graph iterators
//!
//! This module supports filtered iteration over graph tiles.
//! While this module appears to make quite heavy use of the Rust type system's abstractions,
//! the code has been benchmarked against large scale datasets to ensure performance matches
//! the same code as if it were inlined (tested using release builds with LTO).

use crate::GraphId;
use crate::graph_tile::{DirectedEdge, GraphTile, NodeInfo};
use crate::spatial::{DistanceApproximator, bbox_with_center};
use crate::tile_hierarchy::STANDARD_LEVELS;
use crate::tile_provider::{GraphTileProvider, GraphTileProviderError};
use core::cell::LazyCell;
use core::fmt::Display;
use core::marker::PhantomData;
use geo::{
    Closest, ClosestPoint, CoordFloat, Distance, GeoFloat, HasDimensions, Haversine, LineString,
    Point, Validation, coord,
};
use num_traits::FromPrimitive;
use std::collections::VecDeque;

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

/// An iterator over results within a given radius.
///
/// Used internally and returned as an opaque `impl Iterator`.
pub(super) struct ResultsWithinRadius<
    'prov,
    F: Fn(&T) -> bool,
    T,
    P: GraphTileProvider,
    N: CoordFloat + FromPrimitive,
> {
    provider: &'prov P,
    filter_predicate: F,
    center: Point<N>,
    radius_in_meters: N,
    tile_ids: Vec<GraphId>,
    buffer: VecDeque<GraphSearchResult<T, N, P::TileHandle>>,
}

// Node constructor
impl<'prov, F: Fn(&NodeInfo) -> bool, P: GraphTileProvider, N: CoordFloat + FromPrimitive>
    ResultsWithinRadius<'prov, F, NodeInfo, P, N>
{
    pub(super) fn nodes(
        provider: &'prov P,
        filter_predicate: F,
        center: Point<N>,
        radius_in_meters: N,
        tile_ids: Vec<GraphId>,
    ) -> Self {
        Self {
            provider,
            filter_predicate,
            center,
            radius_in_meters,
            tile_ids,
            buffer: VecDeque::new(),
        }
    }
}

// Edge constructor
impl<
    'prov,
    F: Fn(&DirectedEdge) -> bool,
    P: GraphTileProvider,
    N: GeoFloat + CoordFloat + FromPrimitive + Display,
> ResultsWithinRadius<'prov, F, DirectedEdge, P, N>
{
    pub(super) fn edges(
        provider: &'prov P,
        filter_predicate: F,
        center: Point<N>,
        radius_in_meters: N,
        mut tile_ids: Vec<GraphId>,
    ) -> Self {
        // We can use the edge bins at L2 which also contain L0 and L1 edges; clever, right?
        tile_ids.retain(|tile| tile.level() == 2);

        Self {
            provider,
            filter_predicate,
            center,
            radius_in_meters,
            tile_ids,
            buffer: VecDeque::new(),
        }
    }
}

// Node iterator
impl<F: Fn(&NodeInfo) -> bool, P: GraphTileProvider, N: CoordFloat + FromPrimitive> Iterator
    for ResultsWithinRadius<'_, F, NodeInfo, P, N>
{
    type Item = Result<GraphSearchResult<NodeInfo, N, P::TileHandle>, GraphTileProviderError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(result) = self.buffer.pop_front() {
            return Some(Ok(result));
        }

        let base_id = self.tile_ids.pop()?;

        let tile_handle = match self.provider.get_handle_for_tile_containing(base_id) {
            Ok(tile_handle) => tile_handle,
            Err(err) => {
                return Some(Err(err));
            }
        };

        // Stream items from the current tile, storing everything but the node info reference,
        // since we can reconstruct it later.
        // The tile handle clones are cheap (this is a documented assumption in the trait).
        let iter = tile_handle.nodes_within_radius(
            &self.filter_predicate,
            self.center,
            self.radius_in_meters,
        );
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

// Edge iterator
impl<
    F: Fn(&DirectedEdge) -> bool,
    P: GraphTileProvider,
    N: GeoFloat + CoordFloat + FromPrimitive + Display,
> Iterator for ResultsWithinRadius<'_, F, DirectedEdge, P, N>
{
    type Item = Result<GraphSearchResult<DirectedEdge, N, P::TileHandle>, GraphTileProviderError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(result) = self.buffer.pop_front() {
            return Some(Ok(result));
        }

        let base_id = self.tile_ids.pop()?;

        let tile_handle = match self.provider.get_handle_for_tile_containing(base_id) {
            Ok(tile_handle) => tile_handle,
            Err(err) => {
                return Some(Err(err));
            }
        };

        match edges_within_radius(
            self.provider,
            tile_handle,
            &self.filter_predicate,
            self.center,
            self.radius_in_meters,
        ) {
            Ok(results) => {
                self.buffer.extend(results);
            }
            Err(err) => {
                return Some(Err(err));
            }
        }

        self.next()
    }
}

/// A helper function that finds edges using L2 edge bins as a spatial filter.
fn edges_within_radius<
    P: GraphTileProvider,
    F,
    N: GeoFloat + CoordFloat + FromPrimitive + Display,
>(
    provider: &P,
    tile: P::TileHandle,
    edge_filter_predicate: F,
    query_point: Point<N>,
    radius: N,
) -> Result<Vec<GraphSearchResult<DirectedEdge, N, P::TileHandle>>, GraphTileProviderError>
where
    F: Fn(&DirectedEdge) -> bool,
{
    debug_assert!(
        tile.graph_id().level() == 2,
        "edges_within_radius must be called with a level 2 tile so we can use edge bins as a filter"
    );

    let approximator = DistanceApproximator::new(query_point.into());
    let tile_graph_id = tile.graph_id();

    // Build up the set of edge IDs.
    // Our decision for the moment is to make the API easy to use, which means we make a break
    // from how Loki does things, only returning one edge or the other based on a filter.
    // To make our iterator easy to use, we're rolling with all (sortof) edges.
    //
    // The "sortof" qualifier is because edge bins don't include inbound edges for tweeners,
    // which is great, since this isn't what we're searching for anyway.
    // This will give us a set of all edge IDs that are possibly relevant in both directions.
    // This enables the caller to filter based on what they will actually use
    // in terms of forward edges, and removes some of the 4D mental chess burden.
    let initial_edge_ids = prefilter_edge_ids(&tile, query_point, radius);

    let mut edge_ids = Vec::with_capacity(initial_edge_ids.len() * 2);
    let mut unresolved_opp_edge_indexes = Vec::new();
    let mut unresolved_opp_edge_index_lookups = Vec::new();

    // First, we iterate over the very rough list of candidate edge IDs from the edge bins
    // (a spatial filter) and calculate the opposing edge ID (or as much of it as we can,
    // depending on whether it touches in the L2 tile).
    for edge_id in initial_edge_ids {
        if tile.may_contain_id(edge_id) {
            let opp_edge_index = tile.get_opp_edge_index(edge_id)?;
            if opp_edge_index.end_node_id.tile_base_id() == tile_graph_id {
                // Fast path: the edge and its opposing edge are fully contained within the tile.
                let opp_edge_id =
                    provider.graph_id_for_opposing_edge_index(opp_edge_index, &tile)?;
                edge_ids.push(edge_id);
                edge_ids.push(opp_edge_id);
            } else {
                // The edge starts in this tile but ends in another.
                // We eventually need to hit another tile, but we can at least build up the index struct.
                unresolved_opp_edge_indexes.push((edge_id, opp_edge_index));
            }
        } else {
            // The edge doesn't start in this tile (e.g. an L0 or L1 edge); defer processing until later
            unresolved_opp_edge_index_lookups.push(edge_id);
        }
    }

    // Sort the lists of unresolved items so that we don't need to keep churning through tile handles
    unresolved_opp_edge_indexes.sort_unstable_by_key(|(_, index)| index.end_node_id.tile_base_id());
    unresolved_opp_edge_index_lookups.sort_unstable_by_key(|id| id.tile_base_id());

    // Set up a tile handle that will be "sticky" (low churn)
    // as we iterate through the "foreign" edges in tile order
    let mut other_tile = tile.clone();

    // Resolve opposing edge indexes which originate in the current tile but end in another.
    for (edge_id, opp_edge_index) in unresolved_opp_edge_indexes {
        if !other_tile.may_contain_id(opp_edge_index.end_node_id) {
            other_tile = provider.get_handle_for_tile_containing(opp_edge_index.end_node_id)?;
        }

        let opp_edge_id = provider.graph_id_for_opposing_edge_index(opp_edge_index, &other_tile)?;
        edge_ids.push(edge_id);
        edge_ids.push(opp_edge_id);
    }

    // Resolve cases where neither edge is in the current L2 tile
    for edge_id in unresolved_opp_edge_index_lookups {
        if !other_tile.may_contain_id(edge_id) {
            other_tile = provider.get_handle_for_tile_containing(edge_id)?;
        }

        let opp_edge_id = provider.get_opposing_edge_id(edge_id, &other_tile)?;
        edge_ids.push(edge_id);
        edge_ids.push(opp_edge_id);
    }
    drop(other_tile);

    // Sort the final vector to ensure we hit tiles in a more cache-friendly order
    // and don't churn tile handles.
    edge_ids.sort_unstable();

    // It's possible for an edge to show up multiple times.
    // This efficiently removes all dupes as the vector is sorted.
    edge_ids.dedup();

    let mut results = Vec::with_capacity(edge_ids.len());

    // Final "sticky" tile handle; we'll iterate in order, so we only need to remember the last one.
    let mut tile = tile.clone();

    // Loop through the pre-filtered edges (only a subset of levels with binning; otherwise all edges)
    // NOTE: We may currently invoke calculate_distance on both edges in the pair.
    // There is probably a way to avoid doing this, but initial attempts at stashing the opposing edge ID
    // in the vector and using a HashMap to save distance calculations didn't show any improvement.
    for edge_id in edge_ids {
        // NOTE: This code IS a bit weird, but it's also like twice as fast as several attempts
        // which broke it out into smaller functions.
        if tile.may_contain_id(edge_id) {
            // Fast path
            let edge = tile.get_directed_edge(edge_id)?;
            if edge_filter_predicate(edge) {
                if let Some(d) =
                    calculate_distance(&tile, edge, &approximator, query_point, radius)?
                    && d <= radius
                {
                    results.push(GraphSearchResult {
                        handle: tile.clone(),
                        graph_id: edge_id,
                        approx_distance: d,
                        _marker: PhantomData,
                    });
                }
            }
        } else {
            // Get a new tile handle and store it (the next edge is most likely to be in the same tile)
            tile = provider.get_handle_for_tile_containing(edge_id)?;

            let edge = tile.get_directed_edge(edge_id)?;
            if edge_filter_predicate(edge) {
                if let Some(d) =
                    calculate_distance(&tile, edge, &approximator, query_point, radius)?
                    && d <= radius
                {
                    results.push(GraphSearchResult {
                        handle: tile.clone(),
                        graph_id: edge_id,
                        approx_distance: d,
                        _marker: PhantomData,
                    });
                }
            }
        }
    }

    Ok(results)
}

/// Returns a pre-filtered list of edge IDs in a tile,
/// based on a query point and radius using edge bins as a rough index.
///
/// This function assumes that tiles at level 2 have valid edge bins
/// (a standard step in the Valhalla tile build).
/// If edge bins don't exist at level 2, this function will fail to find any edges.
fn prefilter_edge_ids<T: GraphTile, N: CoordFloat + FromPrimitive>(
    tile: &T,
    query_point: Point<N>,
    radius: N,
) -> Vec<GraphId> {
    let header = tile.header();
    let graph_id = header.graph_id();
    let sw = header.sw_corner();

    let mut edge_ids: Vec<GraphId> = Vec::new();
    if graph_id.level() == 2 {
        // Compute which bins intersect the query radius within this tile
        let level_info = &STANDARD_LEVELS[usize::from(graph_id.level())];
        let n = level_info.tiling_system.n_subdivisions as usize;
        let tile_size = level_info.tiling_system.tile_size;
        // Casts from valid floats and integers will succeed
        // The following code has a lot of conversions, but profiling demonstrates ~zero overhead
        // even in a hot loop.
        let bin_size = N::from(tile_size).unwrap() / N::from(n).unwrap();

        let sw_lon = N::from(sw.x).unwrap();
        let sw_lat = N::from(sw.y).unwrap();
        let ne_lon = sw_lon + N::from(tile_size).unwrap();
        let ne_lat = sw_lat + N::from(tile_size).unwrap();

        // Get a bounding rect and clamp it to the tile
        let (north, east, south, west) = bbox_with_center(query_point, radius);
        let bbox_min_lon = west.max(sw_lon);
        let bbox_max_lon = east.min(ne_lon);
        let bbox_min_lat = south.max(sw_lat);
        let bbox_max_lat = north.min(ne_lat);

        // Figure out which bins we need to look into
        // Unless one of the above is not a "normal" float value (e.g., inf, nan, etc.),
        // these conversions are infallible.
        // TODO: Double check the Valhalla code for this... they seem to expand the search in some cases.
        // Since we are already creating a bounding box that's buffered,
        // it's unclear to me that we actually NEED to do that.
        let min_bx = ((bbox_min_lon - sw_lon) / bin_size)
            .floor()
            .to_i32()
            .unwrap()
            .clamp(0, (n as i32) - 1) as usize;
        let max_bx = ((bbox_max_lon - sw_lon) / bin_size)
            .floor()
            .to_i32()
            .unwrap()
            .clamp(0, (n as i32) - 1) as usize;
        let min_by = ((bbox_min_lat - sw_lat) / bin_size)
            .floor()
            .to_i32()
            .unwrap()
            .clamp(0, (n as i32) - 1) as usize;
        let max_by = ((bbox_max_lat - sw_lat) / bin_size)
            .floor()
            .to_i32()
            .unwrap()
            .clamp(0, (n as i32) - 1) as usize;

        // Collect candidate edges from bins
        for bin_y in min_by..=max_by {
            for bin_x in min_bx..=max_bx {
                let bin_index = tile.bin_index_xy(bin_x, bin_y);
                edge_ids.extend(tile.edges_in_bin(bin_index));
            }
        }
    } else {
        // No bins available at this level, so we need to scan the whole tile
        edge_ids.reserve_exact(header.directed_edge_count() as usize);
        edge_ids.extend((0..u64::from(header.directed_edge_count())).map(|idx| {
            graph_id
                .with_feature_index(idx)
                .expect("Graph ID construction should be infallible given the index iterator")
        }));
    }

    edge_ids
}

fn calculate_distance<T: GraphTile, N: GeoFloat + FromPrimitive + Display>(
    tile: &T,
    edge: &DirectedEdge,
    approximator: &DistanceApproximator<N>,
    query_point: Point<N>,
    radius: N,
) -> Result<Option<N>, GraphTileProviderError> {
    let ei = LazyCell::new(|| {
        tile.get_edge_info(edge)
            .expect("Missing edge info (tile is probably corrupt)")
    });

    // Try to short circuit if there's no way we're close to the edge...
    // To do this, we'll leverage the property that, for a LineString of length M,
    // all points must be within radius M of every other point
    // (the shortest path is a straight line between 2 points).
    let any_coord = if let Ok(end_node) = tile.get_node(edge.end_node_id()) {
        // Path 1: If we can cheaply get the end node (this is always faster than getting the start node
        // due to the singly linked list pointer structure),
        // use that coordinate
        let end_coord = end_node.coordinate(tile.header().sw_corner());

        coord! { x: N::from(end_coord.x).unwrap(), y: N::from(end_coord.y).unwrap() }
    } else {
        // Path 2: Just decode the first coordinate of its geometry.
        ei.decode_first_coordinate()?
    };

    // Use the approximator to weed out lines which couldn't possibly be
    // close to the edge geometry.
    // Given one endpoint of the edge, we set the threshold at length + the search distance.
    // This is a conservative heuristic, since most edges will not be straight lines.
    let threshold = radius + N::from(edge.length()).unwrap();

    // Finally, we use the approximator based on rough square distance
    // (very accurate for distances of up to several tens of km, which is a reasonable radius).
    // Only if this extremely conservative heuristic signals false can we bail early.
    // In a real-world dataset, this cuts about 2/3 of the runtime.
    if !approximator.is_probably_within_distance_of(any_coord, threshold) {
        return Ok(None);
    }

    // Note: it doesn't matter if the edge info is forward or reverse here; we just need the closest point.
    let shape = LineString::new(
        ei.decode_raw_shape()
            .expect("Unable to decode shape (tile is probably corrupt)"),
    );

    if !shape.is_valid() || shape.is_empty() {
        tracing::debug!(
            edge = format!("{edge:?}"),
            reason = format!("Shape is invalid or empty: {:?}", shape)
        );
        return Ok(None);
    }

    let closest = shape.closest_point(&query_point);
    Ok(match closest {
        Closest::SinglePoint(c) | Closest::Intersection(c) => {
            // TODO: We might be able to use an approximator here too??
            Some(Haversine.distance(query_point, Point::new(c.x(), c.y())))
        }
        Closest::Indeterminate => {
            tracing::error!(edge = format!("{edge:?}"), lon = %query_point.x(), lat = %query_point.y(), reason = format!("Indeterminate closest_point result for linestring: {:?}", shape));
            None
        }
    })
}
