//! # Routing Graph Tiles
//!
//! This module provides definitions for Valhalla-compatible routing graph tiles.
//! Access is defined by the [`GraphTile`] trait.
//! The memory layout, down to the bit level, is specified in the individual data structures.
//! Start at the [`GraphTileView`], which can reinterpret a byte slice safely as a tile,
//! and work down from there as needed.
//! For writing tiles, a safe builder API is provided in [`GraphTileBuilder`].

use std::ops::Deref;
use std::sync::Arc;
use thiserror::Error;
use zerocopy::{FromBytes, I16, LE, U32};

use enumset::EnumSet;
use geo::{CoordFloat, Point, coord};
use num_traits::FromPrimitive;
#[cfg(test)]
use std::sync::LazyLock;
// To keep files manageable, we will keep internal modules specific to each mega-struct,
// and re-export the public type.
// Each struct should be tested on fixture tiles to a reasonable level of confidence.
// Leverage snapshot tests where possible, compare with Valhalla C++ results,
// and test the first and last elements of variable length vectors
// with snapshot tests.

mod access_restriction;
mod admin;
mod builder;
mod directed_edge;
mod edge_info;
pub mod handles;
mod header;
mod node;
pub mod predicted_speeds;
mod sign;
mod transit;
mod turn_lane;

use crate::graph_tile::handles::OwnedGraphTileHandle;
use crate::graph_tile::predicted_speeds::{
    COEFFICIENT_COUNT, PredictedSpeedCodecError, PredictedSpeeds,
};
use crate::spatial::DistanceApproximator;
use crate::tile_hierarchy::{UnknownLevelError, ValhallaLevel};
pub use crate::{
    Access,
    graph_id::{GraphId, InvalidGraphIdError},
};
pub use access_restriction::{AccessRestriction, AccessRestrictionType};
pub use admin::Admin;
pub use builder::GraphTileBuilder;
pub use directed_edge::{DirectedEdge, DirectedEdgeExt};
pub use edge_info::EdgeInfo;
pub use header::GraphTileHeader;
pub use node::{NodeInfo, NodeTransition};
pub use sign::{Sign, SignType};
pub use transit::{TransitDeparture, TransitRoute, TransitSchedule, TransitStop, TransitTransfer};
pub use turn_lane::TurnLane;

#[derive(Debug, Error)]
pub enum GraphTileDecodingError {
    #[error("Unable to extract a slice of the correct length; the tile data is malformed.")]
    SliceArrayConversion(#[from] std::array::TryFromSliceError),
    #[error("Unable to extract a slice of the correct length; the tile data is malformed.")]
    SliceLength,
    #[error("The byte sequence is not valid for this type.")]
    ByteSequenceValidityError,
    #[error("Invalid graph ID.")]
    GraphIdParseError(#[from] InvalidGraphIdError),
    #[error(
        "Data cast failed for field {field} (this almost always means invalid data): {error_description}"
    )]
    CastError {
        field: String,
        error_description: String,
    },
    #[error(
        "Expected to have consumed all bytes in the graph tile, but we still have a leftover buffer of {0} bytes. This is either a tile reader implementation error, or the tile is invalid."
    )]
    LeftoverBytesAfterReading(usize),
    #[error("Tile level {0} is not currently supported by Valinor.")]
    UnsupportedTileLevel(u8),
}

#[derive(Debug, Error)]
pub enum GraphTileBuildError {
    #[error("{0}")]
    InvalidGraphId(#[from] InvalidGraphIdError),
    #[error("Invalid version string: {0} does not fit into 16 bytes in UTF-8.")]
    InvalidVersionString(String),
    #[error("Invalid index: {0}.")]
    InvalidIndex(String),
    #[error(
        "Bitfield overflow: Value {value} for field {field} exceeds the allowed number of bits."
    )]
    BitfieldOverflow { field: String, value: usize },
    #[error("{0:?}")]
    PredictedSpeedCodec(#[from] PredictedSpeedCodecError),
    #[error(
        "Unable to cast an integer to another type (usually means data is too large for the type): {0:?}."
    )]
    TryFromInt(#[from] std::num::TryFromIntError),
    #[error("Error writing tile: {0}")]
    IoError(#[from] std::io::Error),
    #[error("Poisoned cache lock when writing tile: {0}")]
    PoisonedCacheLock(String),
}

#[derive(Debug, Error)]
pub enum LookupError {
    #[error("Mismatched base; the graph ID cannot exist in this tile.")]
    MismatchedBase,
    #[error("The feature base graph ID matches this tile, but the index is invalid.")]
    InvalidIndex,
}

pub trait GraphTile {
    /// Gets the Graph ID of the tile.
    fn graph_id(&self) -> GraphId;

    /// Does the supplied graph ID belong in this tile?
    ///
    /// A true result does not necessarily guarantee that an object with this ID exists,
    /// but in that case, either you've probably, cooked up an invalid ID for fun,
    /// the graph tiles are invalid, or you've confused a graph ID and a node ID.
    fn may_contain_id(&self, id: GraphId) -> bool;

    /// Gets a reference to the [`GraphTileHeader`].
    fn header(&self) -> &GraphTileHeader;

    /// Gets a reference to a node in this tile with the given graph ID.
    ///
    /// # Errors
    ///
    /// Returns an error if the graph ID cannot be contained in this tile
    /// or the index is invalid.
    fn get_node(&self, id: GraphId) -> Result<&NodeInfo, LookupError>;

    /// Gets a slice of all outbound directed edges from the node.
    ///
    /// No filtering is applied, and this includes edges of all types.
    /// (See also: [`get_transitions`](GraphTile::get_transitions)
    /// if you need edges that may leave the current hierarchy level).
    ///
    /// # Performance
    ///
    /// This does not perform any heap allocations and returns a continuous slice.
    ///
    /// # Errors
    ///
    /// This function may return an incorrect result or panic if the node info
    /// is from another tile.
    /// The node info does not contain tile information, so it is the responsibility of the caller
    /// to ensure this.
    fn get_outbound_edges_from_node(&self, node_info: &NodeInfo) -> &[DirectedEdge];

    /// Gets a slice of all (outbound) transitions (links to other levels) from a node.
    fn get_transitions(&self, node: &NodeInfo) -> &[NodeTransition];

    /// Gets a reference to the directed edge in this tile by graph ID.
    ///
    /// # Errors
    ///
    /// Returns an error if the graph ID cannot be contained in this tile
    /// or the index is invalid.
    fn get_directed_edge(&self, id: GraphId) -> Result<&DirectedEdge, LookupError>;

    /// Gets an index which can be used to retrieve the opposing edge for a given graph ID.
    ///
    /// As long as the original `graph_id` can exist within the tile,
    /// this method will return an index, even if it exists in another tile.
    /// However, access to other tiles may be required to actually get the edge,
    /// or create an unambiguous [`GraphID`].
    ///
    /// # Errors
    ///
    /// Returns a [`LookupError`] if the graph ID is not present in the tile.
    fn get_opp_edge_index(&self, graph_id: GraphId) -> Result<OpposingEdgeIndex, LookupError>;

    /// Gets a reference to an extended directed edge in this tile by graph ID.
    ///
    /// # Errors
    ///
    /// Returns an error if the graph ID cannot be contained in this tile
    /// or the index is invalid.
    fn get_ext_directed_edge(&self, id: GraphId) -> Result<&DirectedEdgeExt, LookupError>;

    /// Gets access restrictions for a directed edge.
    ///
    /// The returned list includes restrictions that apply
    /// to *any* of the supplied access modes (ex: auto, bicycle, etc.).
    fn get_access_restrictions(
        &self,
        directed_edge_index: u32,
        access_modes: EnumSet<Access>,
    ) -> Vec<&AccessRestriction>;

    /// Gets predicted speed information for a directed edge.
    ///
    /// `seconds_from_start_of_week` is measured from midnight Sunday **local time**.
    /// The output is measured in kilometers per hour.
    /// Returns `None` if the edge at this index does not have predicted speed information.
    fn get_predicted_speed(
        &self,
        directed_edge_index: usize,
        seconds_from_start_of_week: u32,
    ) -> Option<f32>;

    /// Gets edge info for a directed edge.
    ///
    /// Note that this is NOT a zero-cost operation.
    /// While it does not immediately decode everything,
    /// several memory accesses and checks need to happen upfront.
    /// As such, it is recommended to avoid calling this during costing.
    ///
    /// # Errors
    ///
    /// Since this accepts a directed edge reference,
    /// two types of errors are possible:
    ///
    /// * An invalid/corrupt graph tile (a serious tile validity error)
    /// * An edge not belonging to the current tile (there is no way to verify this; it is the caller's responsibility)
    fn get_edge_info(
        &self,
        directed_edge: &DirectedEdge,
    ) -> Result<EdgeInfo<'_>, GraphTileDecodingError>;

    // Lower level "raw" accessors

    /// A raw slice of the tile's directed edges (i.e. for iteration).
    fn directed_edges(&self) -> &[DirectedEdge];

    /// A raw slice of the tile's nodes (i.e. for iteration).
    fn nodes(&self) -> &[NodeInfo];

    /// Administrative regions covered in this tile.
    fn admins(&self) -> &[Admin];

    /// Returns the list of edge IDs contained in the specified bin.
    ///
    /// The bin contents are stored as a single concatenated array with prefix offsets
    /// for each bin in the tile header. This method returns a slice of that array.
    ///
    /// Valhalla's edge bins speed up for finding edges by dividing the level 2 tiles into
    /// a grid and storing edges that cross through each bounding box.
    /// This limits the search space, since it's relatively expensive to deserialize edge geometry.
    ///
    /// While the directed graph edges always come in pairs,
    /// only one edge from the pair is included in the edge bins!
    ///
    /// # Panics
    ///
    /// This may panic if the tile data is invalid and references an out-of-bounds index.
    fn edges_in_bin(&self, bin_index: usize) -> &[GraphId];

    /// Computes the row-major bin index for the given bin coordinates within
    /// the tile's bin grid.
    ///
    /// # Panics
    ///
    /// Assumes that the level in the graph tile header is a standard or transit Valhalla level
    /// (0 through 3 - transit)
    ///
    /// This function also assumes that the `x` and `y` values are within the accepted range
    /// (specifically, they must each be <= the square root of [`crate::BIN_COUNT`]).
    fn bin_index_xy(&self, x: usize, y: usize) -> usize;

    /// Returns an iterator over all nodes near a specified point,
    /// within this tile, including the approximate distance from the point.
    ///
    /// No sorting or filtering of nodes is performed besides ensuring that they are close enough.
    /// The distance returned (second tuple element) is approximate,
    /// but should be accurate to within 1 meter for radii of up to 20km.
    ///
    /// # Performance
    ///
    /// This method is very fast for a few reasons:
    ///
    /// - It only considers nodes within a single tile (which you already have a reference to!)
    /// - The result is an unsorted iterator
    /// - Internally, an approximator is used to (very!) quickly weed out unrealistic candidates
    ///   before doing the heavier trigonometry.
    ///
    /// Currently, this requires a scan of all nodes in the tile.
    /// This is a lot faster than in may sound,
    /// but in the future, it would be interesting to explore k-d trees
    /// for things like map matching, which need to find candidates for a large number of points.
    ///
    /// A k-d tree also maps directly to the most common question,
    /// which is to retrieve the `k` nearest nodes.
    ///
    /// # Panics
    ///
    /// This isn't intended to be used to get nodes over large distances.
    /// In debug builds, this will panic if `radius_in_meters` is larger than 20,000 (20km).
    ///
    /// Also panics if you provide non-finite floating point values (e.g., NaN or infinity).
    #[inline]
    fn nodes_within_radius<N: CoordFloat + FromPrimitive, F: Fn(&NodeInfo) -> bool>(
        &self,
        filter_predicate: F,
        center: Point<N>,
        radius_in_meters: N,
    ) -> impl Iterator<Item = (GraphNode<'_>, N)> {
        let header = self.header();
        let level = header.graph_id().level();
        let tile_id = header.graph_id().tile_id();
        let sw = header.sw_corner();

        // Set up an approximator based on square distance.
        // This is good enough for reasonable distances (<1m for distances up to a few tens of km).
        let approximator = DistanceApproximator::new(center.into());
        let radius_squared = radius_in_meters * radius_in_meters;

        self.nodes()
            .iter()
            .enumerate()
            .filter_map(move |(idx, node_info)| {
                if !filter_predicate(node_info) {
                    return None;
                }

                let node_id = GraphId::try_from_components(level, tile_id, idx as u64).ok()?;
                let nc = node_info.coordinate(sw);

                let nc_lon = N::from(nc.x).unwrap();
                let nc_lat = N::from(nc.y).unwrap();
                let sq_dist = approximator.distance_squared(coord! {x: nc_lon, y: nc_lat});
                if sq_dist <= radius_squared {
                    Some((GraphNode { node_id, node_info }, sq_dist.sqrt()))
                } else {
                    None
                }
            })
    }
}

impl<T> GraphTile for Arc<T>
where
    T: GraphTile,
{
    #[inline]
    fn graph_id(&self) -> GraphId {
        self.deref().graph_id()
    }

    #[inline]
    fn may_contain_id(&self, id: GraphId) -> bool {
        self.deref().may_contain_id(id)
    }

    #[inline]
    fn header(&self) -> &GraphTileHeader {
        self.deref().header()
    }

    #[inline]
    fn get_node(&self, id: GraphId) -> Result<&NodeInfo, LookupError> {
        self.deref().get_node(id)
    }

    #[inline]
    fn get_outbound_edges_from_node(&self, node_info: &NodeInfo) -> &[DirectedEdge] {
        self.deref().get_outbound_edges_from_node(node_info)
    }

    #[inline]
    fn get_transitions(&self, node: &NodeInfo) -> &[NodeTransition] {
        self.deref().get_transitions(node)
    }

    #[inline]
    fn get_directed_edge(&self, id: GraphId) -> Result<&DirectedEdge, LookupError> {
        self.deref().get_directed_edge(id)
    }

    #[inline]
    fn get_opp_edge_index(&self, graph_id: GraphId) -> Result<OpposingEdgeIndex, LookupError> {
        self.deref().get_opp_edge_index(graph_id)
    }

    #[inline]
    fn get_ext_directed_edge(&self, id: GraphId) -> Result<&DirectedEdgeExt, LookupError> {
        self.deref().get_ext_directed_edge(id)
    }

    #[inline]
    fn get_access_restrictions(
        &self,
        directed_edge_index: u32,
        access_modes: EnumSet<Access>,
    ) -> Vec<&AccessRestriction> {
        self.deref()
            .get_access_restrictions(directed_edge_index, access_modes)
    }

    #[inline]
    fn get_predicted_speed(
        &self,
        directed_edge_index: usize,
        seconds_from_start_of_week: u32,
    ) -> Option<f32> {
        self.deref()
            .get_predicted_speed(directed_edge_index, seconds_from_start_of_week)
    }

    #[inline]
    fn get_edge_info(
        &self,
        directed_edge: &DirectedEdge,
    ) -> Result<EdgeInfo<'_>, GraphTileDecodingError> {
        self.deref().get_edge_info(directed_edge)
    }

    #[inline]
    fn directed_edges(&self) -> &[DirectedEdge] {
        self.deref().directed_edges()
    }

    #[inline]
    fn nodes(&self) -> &[NodeInfo] {
        self.deref().nodes()
    }

    #[inline]
    fn admins(&self) -> &[Admin] {
        self.deref().admins()
    }

    #[inline]
    fn edges_in_bin(&self, bin_index: usize) -> &[GraphId] {
        self.deref().edges_in_bin(bin_index)
    }

    #[inline]
    fn bin_index_xy(&self, x: usize, y: usize) -> usize {
        self.deref().bin_index_xy(x, y)
    }
}

/// A node in a graph tile.
///
/// Nodes represent intersections between edges in the graph.
/// These are not directly analogous to OSM nodes; most nodes in OSM don't exist in the graph,
/// as they are only needed for geometry, and would make traversal / path finding slow.
pub struct GraphNode<'a> {
    /// The Graph ID identifying this node.
    pub node_id: GraphId,
    pub node_info: &'a NodeInfo,
}

/// A view over a single tile in the Valhalla hierarchical tile graph.
///
/// Access should normally go through the [`GraphTile`] trait.
///
/// # Cloning
///
/// Cloning this struct is cheap, since the internal types are all references.
#[derive(Clone)]
pub struct GraphTileView<'a> {
    /// Header with various metadata about the tile and internal sizes.
    header: &'a GraphTileHeader,
    /// The checked hierarchy level from the header.
    level: ValhallaLevel,
    /// The list of nodes in the graph tile.
    nodes: &'a [NodeInfo],
    /// The list of transitions between nodes on different levels.
    transitions: &'a [NodeTransition],
    directed_edges: &'a [DirectedEdge],
    ext_directed_edges: &'a [DirectedEdgeExt],
    access_restrictions: &'a [AccessRestriction],
    transit_departures: &'a [TransitDeparture],
    transit_stops: &'a [TransitStop],
    transit_routes: &'a [TransitRoute],
    transit_schedules: &'a [TransitSchedule],
    transit_transfers: &'a [TransitTransfer],
    signs: &'a [Sign],
    turn_lanes: &'a [TurnLane],
    admins: &'a [Admin],
    edge_bins: &'a [GraphId],
    complex_forward_restrictions_memory: &'a [u8],
    complex_reverse_restrictions_memory: &'a [u8],
    // Variable length byte arrays (indexed into at various other points; hidden with public safe accessors)...
    // These are all slices which DO have a known size at runtime, but not at compile time.
    edge_info_memory: &'a [u8],
    text_memory: &'a [u8],
    lane_connectivity_memory: &'a [u8],
    predicted_speeds: Option<PredictedSpeeds<'a>>,
}

impl GraphTile for GraphTileView<'_> {
    #[inline]
    fn graph_id(&self) -> GraphId {
        self.header.graph_id()
    }

    #[inline]
    fn may_contain_id(&self, id: GraphId) -> bool {
        id.tile_base_id() == self.graph_id().tile_base_id()
    }

    #[inline]
    fn header(&self) -> &GraphTileHeader {
        self.header
    }

    #[inline]
    fn get_node(&self, id: GraphId) -> Result<&NodeInfo, LookupError> {
        if self.may_contain_id(id) {
            self.nodes
                .get(id.feature_index() as usize)
                .ok_or(LookupError::InvalidIndex)
        } else {
            Err(LookupError::MismatchedBase)
        }
    }

    #[inline]
    fn get_outbound_edges_from_node(&self, node_info: &NodeInfo) -> &[DirectedEdge] {
        let start = node_info.edge_index() as usize;
        let count = usize::from(node_info.edge_count());

        &self.directed_edges[start..(start + count)]
    }

    #[inline]
    fn get_transitions(&self, node: &NodeInfo) -> &[NodeTransition] {
        let start = node.transition_index() as usize;
        let count = usize::from(node.transition_count());
        &self.transitions[start..(start + count)]
    }

    #[inline]
    fn get_directed_edge(&self, id: GraphId) -> Result<&DirectedEdge, LookupError> {
        if self.may_contain_id(id) {
            self.directed_edges
                .get(id.feature_index() as usize)
                .ok_or(LookupError::InvalidIndex)
        } else {
            Err(LookupError::MismatchedBase)
        }
    }

    fn get_opp_edge_index(&self, graph_id: GraphId) -> Result<OpposingEdgeIndex, LookupError> {
        let edge = self.get_directed_edge(graph_id)?;

        // The edge might leave the tile, so we have to do a complicated lookup
        let end_node_id = edge.end_node_id();
        let opposing_edge_index = edge.opposing_edge_index();

        Ok(OpposingEdgeIndex {
            end_node_id,
            opposing_edge_index,
        })
    }

    fn get_ext_directed_edge(&self, id: GraphId) -> Result<&DirectedEdgeExt, LookupError> {
        if self.may_contain_id(id) {
            self.ext_directed_edges
                .get(id.feature_index() as usize)
                .ok_or(LookupError::InvalidIndex)
        } else {
            Err(LookupError::MismatchedBase)
        }
    }

    fn get_access_restrictions(
        &self,
        directed_edge_index: u32,
        access_modes: EnumSet<Access>,
    ) -> Vec<&AccessRestriction> {
        // Find the point such that all elements below index are less than directed_edge_index
        // (NOTE: the list is pre-sorted during tile building)
        let index = self
            .access_restrictions
            .partition_point(|e| e.edge_index() < directed_edge_index);

        self.access_restrictions
            .iter()
            // Iterate over the relevant objects (this is an empty iterator if index >= length)
            .skip(index)
            .take_while(|e| e.edge_index() == directed_edge_index)
            .filter(|e| !e.affected_access_modes().is_disjoint(access_modes))
            .collect()
    }

    fn get_predicted_speed(
        &self,
        directed_edge_index: usize,
        seconds_from_start_of_week: u32,
    ) -> Option<f32> {
        match &self.predicted_speeds {
            Some(ps) => {
                if self.directed_edges[directed_edge_index].has_predicted_speed() {
                    ps.speed(directed_edge_index, seconds_from_start_of_week)
                } else {
                    None
                }
            }
            None => None,
        }
    }

    fn get_edge_info(
        &self,
        directed_edge: &DirectedEdge,
    ) -> Result<EdgeInfo<'_>, GraphTileDecodingError> {
        let edge_info_offset = directed_edge.edge_info_offset() as usize;

        EdgeInfo::try_from((&self.edge_info_memory[edge_info_offset..], self.text_memory))
    }

    #[inline]
    fn directed_edges(&self) -> &[DirectedEdge] {
        self.directed_edges
    }

    #[inline]
    fn nodes(&self) -> &[NodeInfo] {
        self.nodes
    }

    #[inline]
    fn admins(&self) -> &[Admin] {
        self.admins
    }

    #[inline]
    fn edges_in_bin(&self, bin_index: usize) -> &[GraphId] {
        if self.edge_bins.is_empty() {
            return &[];
        }
        let (start, end) = self.header.edge_bin_offsets(bin_index);
        assert!(
            end <= self.edge_bins.len(),
            "Unexpected end that runs past the edge bins structure"
        );
        &self.edge_bins[start..end]
    }

    #[inline]
    fn bin_index_xy(&self, x: usize, y: usize) -> usize {
        assert!(
            x << 1 < crate::BIN_COUNT,
            "x must be less than the square root of crate::BIN_COUNT"
        );
        assert!(
            y << 1 < crate::BIN_COUNT,
            "y must be less than the square root of crate::BIN_COUNT"
        );

        let n_subdivisions = usize::from(self.level.definition().tiling_system.n_subdivisions);
        y * n_subdivisions + x
    }
}

impl<'a> TryFrom<&'a [u8]> for GraphTileView<'a> {
    type Error = GraphTileDecodingError;

    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        let (header, bytes) = GraphTileHeader::ref_from_prefix(bytes).map_err(|e| {
            GraphTileDecodingError::CastError {
                field: "header".to_string(),
                error_description: e.to_string(),
            }
        })?;

        let level = ValhallaLevel::try_from(header.graph_id().level()).map_err(
            |UnknownLevelError(level)| GraphTileDecodingError::UnsupportedTileLevel(level),
        )?;

        // All the variably sized data arrays...
        // The pattern here is to use `ref_from_prefix_with_elems` to consume a known number of elements
        // from the byte slice, returning a reference to the tail.
        //
        // In this way, we don't typically need to track manual offsets;
        // we just consume the known number of elements sequentially.
        // This is not *strictly* the same as how Valhalla parses the tile in `GraphTile::Initialize`,
        // but it is functionally identical.
        // The only theoretical avenues for breakage is when data order changes (a breaking change anyway!).
        // All of our size calculations are explicit though (in header.rs),
        // and the ordering of data sections is explicit in the implementation
        // (this also doubles as documentation now).
        //
        // One helpful side effect of this approach is that we can be certain
        // that there are no accidentally overlapping borrows!
        // Additionally, at the end, we can check that we've consumed all bytes,
        // thus ensuring that we have either mapped every byte or else something is wrong.

        // Basic features
        let (nodes, bytes) =
            <[NodeInfo]>::ref_from_prefix_with_elems(bytes, header.node_count() as usize).map_err(
                |e| GraphTileDecodingError::CastError {
                    field: "node_info".to_string(),
                    error_description: e.to_string(),
                },
            )?;
        let (transitions, bytes) = <[NodeTransition]>::ref_from_prefix_with_elems(
            bytes,
            header.transition_count() as usize,
        )
        .map_err(|e| GraphTileDecodingError::CastError {
            field: "transitions".to_string(),
            error_description: e.to_string(),
        })?;
        let (directed_edges, bytes) = <[DirectedEdge]>::ref_from_prefix_with_elems(
            bytes,
            header.directed_edge_count() as usize,
        )
        .map_err(|e| GraphTileDecodingError::CastError {
            field: "directed_edges".to_string(),
            error_description: e.to_string(),
        })?;

        // Extended directed edges
        let directed_edge_ext_count = if header.has_ext_directed_edge() {
            header.directed_edge_count() as usize
        } else {
            0
        };
        let (ext_directed_edges, bytes) =
            <[DirectedEdgeExt]>::ref_from_prefix_with_elems(bytes, directed_edge_ext_count)
                .map_err(|e| GraphTileDecodingError::CastError {
                    field: "directed_edge_ext".to_string(),
                    error_description: e.to_string(),
                })?;

        // Access restrictions
        let (access_restrictions, bytes) = <[AccessRestriction]>::ref_from_prefix_with_elems(
            bytes,
            header.access_restriction_count() as usize,
        )
        .map_err(|e| GraphTileDecodingError::CastError {
            field: "access_restrictions".to_string(),
            error_description: e.to_string(),
        })?;

        // Transit features
        let (transit_departures, bytes) = <[TransitDeparture]>::ref_from_prefix_with_elems(
            bytes,
            header.departure_count() as usize,
        )
        .map_err(|e| GraphTileDecodingError::CastError {
            field: "transit_departures".to_string(),
            error_description: e.to_string(),
        })?;
        let (transit_stops, bytes) =
            <[TransitStop]>::ref_from_prefix_with_elems(bytes, header.stop_count() as usize)
                .map_err(|e| GraphTileDecodingError::CastError {
                    field: "transit_stops".to_string(),
                    error_description: e.to_string(),
                })?;
        let (transit_routes, bytes) =
            <[TransitRoute]>::ref_from_prefix_with_elems(bytes, header.route_count() as usize)
                .map_err(|e| GraphTileDecodingError::CastError {
                    field: "transit_routes".to_string(),
                    error_description: e.to_string(),
                })?;
        let (transit_schedules, bytes) = <[TransitSchedule]>::ref_from_prefix_with_elems(
            bytes,
            header.schedule_count() as usize,
        )
        .map_err(|e| GraphTileDecodingError::CastError {
            field: "transit_schedules".to_string(),
            error_description: e.to_string(),
        })?;
        let (transit_transfers, bytes) = <[TransitTransfer]>::ref_from_prefix_with_elems(
            bytes,
            header.transfer_count() as usize,
        )
        .map_err(|e| GraphTileDecodingError::CastError {
            field: "transit_transfers".to_string(),
            error_description: e.to_string(),
        })?;

        let (signs, bytes) =
            <[Sign]>::ref_from_prefix_with_elems(bytes, header.sign_count() as usize).map_err(
                |e| GraphTileDecodingError::CastError {
                    field: "signs".to_string(),
                    error_description: e.to_string(),
                },
            )?;
        let (turn_lanes, bytes) =
            <[TurnLane]>::ref_from_prefix_with_elems(bytes, header.turn_lane_count() as usize)
                .map_err(|e| GraphTileDecodingError::CastError {
                    field: "turn_lanes".to_string(),
                    error_description: e.to_string(),
                })?;

        let (admins, bytes) =
            <[Admin]>::ref_from_prefix_with_elems(bytes, header.admin_count() as usize).map_err(
                |e| GraphTileDecodingError::CastError {
                    field: "admins".to_string(),
                    error_description: e.to_string(),
                },
            )?;

        let (edge_bins, bytes) =
            <[GraphId]>::ref_from_prefix_with_elems(bytes, header.edge_bins_count()).map_err(
                |e| GraphTileDecodingError::CastError {
                    field: "edge_bins".to_string(),
                    error_description: e.to_string(),
                },
            )?;

        let (complex_forward_restrictions_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.complex_forward_restrictions_size())
                .map_err(|e| GraphTileDecodingError::CastError {
                field: "complex_forward_restrictions".to_string(),
                error_description: e.to_string(),
            })?;

        let (complex_reverse_restrictions_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.complex_reverse_restrictions_size())
                .map_err(|e| GraphTileDecodingError::CastError {
                field: "complex_reverse_restrictions".to_string(),
                error_description: e.to_string(),
            })?;

        let (edge_info_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.edge_info_size()).map_err(|e| {
                GraphTileDecodingError::CastError {
                    field: "edge_info_memory".to_string(),
                    error_description: e.to_string(),
                }
            })?;

        let (text_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.text_list_size()).map_err(|e| {
                GraphTileDecodingError::CastError {
                    field: "text_memory".to_string(),
                    error_description: e.to_string(),
                }
            })?;

        let (lane_connectivity_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.lane_connectivity_size()).map_err(
                |e| GraphTileDecodingError::CastError {
                    field: "lane_connectivity".to_string(),
                    error_description: e.to_string(),
                },
            )?;

        let (predicted_speeds, bytes) = if header.predicted_speeds_count() > 0 {
            // Curiously, these seem to actually be unaligned in a Valhalla tile I generated!
            let (offsets, profile_data) = <[U32<LE>]>::ref_from_prefix_with_elems(
                bytes,
                header.directed_edge_count() as usize,
            )
            .map_err(|e| GraphTileDecodingError::CastError {
                field: "predicted_speed_offsets".to_string(),
                error_description: e.to_string(),
            })?;

            let (profiles, bytes) = <[I16<LE>]>::ref_from_prefix_with_elems(
                profile_data,
                header.predicted_speeds_count() as usize * COEFFICIENT_COUNT,
            )
            .map_err(|e| GraphTileDecodingError::CastError {
                field: "predicted_speed_profiles".to_string(),
                error_description: e.to_string(),
            })?;

            (Some(PredictedSpeeds::new(offsets, profiles)), bytes)
        } else {
            (None, bytes)
        };

        if bytes.is_empty() {
            Ok(Self {
                header,
                level,
                nodes,
                transitions,
                directed_edges,
                ext_directed_edges,
                access_restrictions,
                transit_departures,
                transit_stops,
                transit_routes,
                transit_schedules,
                transit_transfers,
                signs,
                turn_lanes,
                admins,
                edge_bins,
                complex_forward_restrictions_memory,
                complex_reverse_restrictions_memory,
                edge_info_memory,
                text_memory,
                lane_connectivity_memory,
                predicted_speeds,
            })
        } else {
            Err(GraphTileDecodingError::LeftoverBytesAfterReading(
                bytes.len(),
            ))
        }
    }
}

/// A pair which can be used to get an opposing edge from a graph tile provider.
pub struct OpposingEdgeIndex {
    /// The ID of the end node.
    ///
    /// NOTE: This might be in another tile from the original edge!
    pub(crate) end_node_id: GraphId,
    /// The index of the opposing directed edge at the end node of this directed edge.
    pub(crate) opposing_edge_index: u32,
}

#[cfg(test)]
const TEST_GRAPH_TILE_ID_L0: GraphId = unsafe { GraphId::from_components_unchecked(0, 3015, 0) };
#[cfg(test)]
const TEST_GRAPH_TILE_ID_L2: GraphId = unsafe { GraphId::from_components_unchecked(2, 762485, 0) };

#[cfg(test)]
static TEST_GRAPH_TILE_L0: LazyLock<OwnedGraphTileHandle> = LazyLock::new(|| {
    let relative_path = TEST_GRAPH_TILE_ID_L0
        .file_path("gph")
        .expect("Unable to get relative path");
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-tiles")
        .join(relative_path);
    let bytes = std::fs::read(path).expect("Unable to read file");

    OwnedGraphTileHandle::try_from(bytes).expect("Unable to get tile")
});

#[cfg(test)]
static TEST_GRAPH_TILE_L2: LazyLock<OwnedGraphTileHandle> = LazyLock::new(|| {
    let relative_path = TEST_GRAPH_TILE_ID_L2
        .file_path("gph")
        .expect("Unable to get relative path");
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-tiles")
        .join(relative_path);
    let bytes = std::fs::read(path).expect("Unable to read file");

    OwnedGraphTileHandle::try_from(bytes).expect("Unable to get tile")
});

/// Test data note: this relies on a binary fixture
/// where speed info is added to the Andorra tiles using the `valhalla_add_predicted_traffic`
/// utility.
///
/// The contents of the file `0/003/015.csv` used to generate the test fixture are as follows:
///
/// ```csv
/// 0/3015/0,50,40,
/// 0/3015/42,100,42,BcUACQAEACEADP/7/9sAGf/fAAwAGwARAAX/+AAAAB0AFAAS//AAF//+ACwACQAqAAAAKP/6AEMABABsAAsBBAAq/rcAAP+bAAz/zv/s/9MABf/Y//X/8//9/+wACf/P//EADv/8//L//P/y//H////7AAwAFf/5//oADgAZAAQAFf/3/+8AB//yAB8ABv/0AAUAEf/8//QAFAAG//b////j//v//QAT//7/+f/kABMABwABAAv/6//8//cAEwAAABT/8v/6//wAAAAQ//cACwAFAAT/1//sAAEADAABAAYAE//9AAn/7gAH/+AAFQAB//4AC//o/+gAE//+AAAAFf/l//kABP/+//kACAAG//cAHv/qAB0AAv/4/+v/+wALAAMABP/3AAT/8wAIAAr/9wAK//j/+wAEAAD/+P/8//v/8f/2//L//AALAAcABgAG//gAAv/5AAoAHv//AAcAFf/zABD/7AAUAAv/7v/8AAgACAAN//0ADP/iABD/9f/3//7/+P/3AAQADP//AAMABw==
/// 0/3015/7,12,34,CKD/4f/r/+H/6//g/+v/4P/q/9//6v/f/+r/3v/q/93/6f/b/+n/2v/o/9f/5//V/+b/0f/l/8z/4//G/+D/vf/d/67/1/+V/8z/Xf+u/nz+GwLJAEcAqwAWAFwABwA8AAAAK//8ACD/+AAZ//YAE//0AA//8gAM//AACf/uAAb/7AAE/+kAAv/m////4v/9/93/+f/U//T/xf/q/5//y/6PAQMAngApADkAFwAfABAAEwAMAAwACQAHAAcAAwAGAAAABf/9AAT/+wAD//kAA//2AAL/9AAC//EAAf/tAAH/6AAA/+EAAP/U////tv///x8AFADL//8AQ///ACf//gAa//4AE//+AA7//QAL//0ACP/9AAb//AAE//wAAv/8AAD/+//+//v//P/6//r/+v/2//n/8v/4/+v/9f/b/+//nP+TALoADAAyAAMAHgAAABX//gAQ//0ADf/9AAv//AAJ//sAB//7AAb/+gAF//kABP/4AAP/9wAC//YAAf/1AAD/8//+//D//P/q//f/2w==
/// ```
#[cfg(test)]
static TEST_GRAPH_TILE_WITH_FLOW: LazyLock<OwnedGraphTileHandle> = LazyLock::new(|| {
    let relative_path = TEST_GRAPH_TILE_ID_L0
        .file_path("gph")
        .expect("Unable to get relative path");
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-tiles-with-traffic")
        .join(relative_path);
    let bytes = std::fs::read(path).expect("Unable to read file");

    OwnedGraphTileHandle::try_from(bytes).expect("Unable to get tile")
});

/// The tile ID (at levels 2 and 3) of the tiles in the `andorra-transit-tiles` fixture.
#[cfg(test)]
const TEST_TRANSIT_FIXTURE_TILE_ID: u64 = 763_926;

#[cfg(test)]
fn transit_fixture_dir() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-transit-tiles")
}

#[cfg(test)]
fn load_transit_fixture_tile(level: u8) -> OwnedGraphTileHandle {
    let relative_path = GraphId::try_from_components(level, TEST_TRANSIT_FIXTURE_TILE_ID, 0)
        .expect("Invalid graph ID")
        .file_path("gph")
        .expect("Unable to get relative path");
    let bytes =
        std::fs::read(transit_fixture_dir().join(relative_path)).expect("Unable to read file");

    OwnedGraphTileHandle::try_from(bytes).expect("Unable to get tile")
}

/// The local tile under [`TEST_TRANSIT_TILE_L3`], from the same build.
#[cfg(test)]
static TEST_TRANSIT_TILE_L2: LazyLock<OwnedGraphTileHandle> =
    LazyLock::new(|| load_transit_fixture_tile(2));

/// A transit tile that Valhalla 3.8.2 built from a small GTFS feed.
#[cfg(test)]
static TEST_TRANSIT_TILE_L3: LazyLock<OwnedGraphTileHandle> =
    LazyLock::new(|| load_transit_fixture_tile(3));

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Access;
    use crate::graph_tile::predicted_speeds::BUCKETS_PER_WEEK;
    use crate::graph_tile::{
        GraphTile, TEST_GRAPH_TILE_ID_L0, TEST_GRAPH_TILE_L0, TEST_GRAPH_TILE_L2,
        TEST_GRAPH_TILE_WITH_FLOW, TEST_TRANSIT_TILE_L2, TEST_TRANSIT_TILE_L3,
    };
    use crate::{AsCowStr, RoadUse};
    use enumset::{EnumSet, enum_set};
    use rand::{Rng, rng};
    use std::borrow::Cow;
    use walkdir::WalkDir;

    #[test]
    fn test_get_opp_edge_index() {
        let tile = &*TEST_GRAPH_TILE_L0;

        let edges: Vec<_> = (0..u64::from(tile.header().directed_edge_count()))
            .flat_map(|index| {
                let edge_id = TEST_GRAPH_TILE_ID_L0
                    .with_feature_index(index)
                    .expect("Invalid graph ID.");
                let OpposingEdgeIndex {
                    end_node_id,
                    opposing_edge_index,
                } = tile
                    .get_opp_edge_index(edge_id)
                    .expect("Unable to get opp edge index.");

                // Currently the fixture has no edges exiting the tile, but we play it safe.
                if let Ok(node) = tile.get_node(end_node_id) {
                    // This is not the way you'd normally want to build these up;
                    // you should use GraphTileProvider's convenience methods almost all the time.
                    // This just makes the test independent and self-contained using only tile methods.
                    Some(node.edge_index() + opposing_edge_index)
                } else {
                    None
                }
            })
            .collect();

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(edges);
        }
    }

    #[test]
    fn test_get_access_restrictions() {
        let tile = &*TEST_GRAPH_TILE_L0;

        let mut found_restriction_count = 0;
        let mut found_partial_subset_count = 0;
        for edge_index in 0..tile.header().directed_edge_count() {
            // Sanity check edge index with no access mode filter
            let all_edge_restrictions = tile.get_access_restrictions(edge_index, EnumSet::all());
            for restriction in &all_edge_restrictions {
                found_restriction_count += 1;
                assert_eq!(restriction.edge_index(), edge_index);
            }

            // In the tile fixture, all restrictions apply to trucks
            assert_eq!(
                all_edge_restrictions,
                tile.get_access_restrictions(edge_index, enum_set!(Access::Truck))
            );

            // Empty set should yield no access restrictions
            assert!(
                tile.get_access_restrictions(edge_index, EnumSet::empty())
                    .is_empty()
            );

            // This set includes one mode that matches 4 elements in the fixture tile,
            // and another mode that matches none.
            for restriction in
                tile.get_access_restrictions(edge_index, enum_set!(Access::Auto | Access::GolfCart))
            {
                found_partial_subset_count += 1;
                assert_eq!(restriction.edge_index(), edge_index);
            }
        }

        // Hard-coded bits based on the test fixture
        assert_eq!(found_restriction_count, 8);
        assert_eq!(found_partial_subset_count, 4);
    }

    #[test]
    fn test_edge_bins() {
        let tile = &*TEST_GRAPH_TILE_L0;
        let tile_view = tile.borrow_dependent();
        assert!(
            tile_view.edge_bins.is_empty(),
            "The level 0 tile has no edge bins"
        );

        let tile = &*TEST_GRAPH_TILE_L2;
        let tile_view = tile.borrow_dependent();
        assert!(
            !tile_view.edge_bins.is_empty(),
            "The level 2 tile should have edge bins"
        );

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_yaml_snapshot!(tile_view.edge_bins);
        }
    }

    #[test]
    fn test_bin_accessors_integrity() {
        // Level without bins should yield empty slices across all bins
        let l0 = &*TEST_GRAPH_TILE_L0;
        let l0_view = l0.borrow_dependent();
        let mut total = 0usize;
        for i in 0..crate::BIN_COUNT {
            let bin = l0_view.edges_in_bin(i);
            assert!(bin.is_empty(), "L0 has no bins, bin {i} should be empty");
            total += bin.len();
        }
        assert_eq!(total, 0);

        // Level with bins should have slices that sum to the backing array size
        let l2 = &*TEST_GRAPH_TILE_L2;
        let l2_view = l2.borrow_dependent();
        let mut total = 0usize;
        for i in 0..crate::BIN_COUNT {
            total += l2_view.edges_in_bin(i).len();
        }
        assert_eq!(total, l2_view.edge_bins.len());

        // Check bin index mapping at corners doesn't panic and returns a valid index
        let n = 5;
        let idx_tl = l2_view.bin_index_xy(0, 0);
        let idx_tr = l2_view.bin_index_xy(n - 1, 0);
        let idx_bl = l2_view.bin_index_xy(0, n - 1);
        let idx_br = l2_view.bin_index_xy(n - 1, n - 1);
        for idx in [idx_tl, idx_tr, idx_bl, idx_br] {
            assert!(idx < crate::BIN_COUNT);
        }
    }

    #[test]
    fn test_edge_info() {
        let tile = &*TEST_GRAPH_TILE_L0;

        let first_edge_info = tile
            .get_edge_info(&tile.directed_edges().first().unwrap())
            .expect("Unable to get edge info.");

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!("first_edge_info", first_edge_info);
            insta::assert_debug_snapshot!(
                "first_edge_info_decoded_shape",
                first_edge_info.decode_raw_shape::<f64>()
            );
            insta::assert_debug_snapshot!(
                "first_edge_info_decoded_shape_f32",
                first_edge_info.decode_raw_shape::<f32>()
            );
            insta::assert_debug_snapshot!("first_edge_info_names", first_edge_info.get_names());
        }

        assert_eq!(first_edge_info.way_id(), 0);

        let last_edge_info = tile
            .get_edge_info(tile.directed_edges().last().unwrap())
            .expect("Unable to get edge info.");

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!("last_edge_info", last_edge_info);
        }

        assert_eq!(last_edge_info.way_id(), 247995246);

        // Edge chosen somewhat randomly; it happens to have multiple names.
        let other_edge_info = tile
            .get_edge_info(&tile.directed_edges()[2000])
            .expect("Unable to get edge info.");

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!("other_edge_info", other_edge_info);
            insta::assert_debug_snapshot!("other_edge_info_names", other_edge_info.get_names());
        }

        assert_eq!(other_edge_info.way_id(), 28833880);
    }

    #[test]
    fn test_predicted_speed_access_when_absent_in_tile() {
        let tile = &*TEST_GRAPH_TILE_L0;
        let tile_view = tile.borrow_dependent();

        // The tile was built without speed information
        assert_eq!(tile_view.get_predicted_speed(0, 0), None);

        // The index is clearly invalid
        assert_eq!(tile_view.get_predicted_speed(usize::MAX, 0), None);
    }

    #[test]
    fn test_traffic_flow_speeds() {
        let tile = &*TEST_GRAPH_TILE_WITH_FLOW;
        let tile_view = tile.borrow_dependent();

        const EDGE_INDEX: usize = 0;
        let edge = &tile_view.directed_edges()[EDGE_INDEX];

        assert_eq!(edge.free_flow_speed(), 50);
        assert_eq!(edge.constrained_flow_speed(), 40);
        assert_eq!(edge.has_predicted_speed(), false);

        // This edge doesn't have any predicted speeds.
        assert_eq!(tile_view.get_predicted_speed(EDGE_INDEX, 0), None);
    }

    #[test]
    fn test_predicted_traffic_speeds() {
        let tile = &*TEST_GRAPH_TILE_WITH_FLOW;
        let tile_view = tile.borrow_dependent();

        // We specifically added predicted speeds to this random edge index.
        // See the test case info in the comment for TEST_GRAPH_TILE_WITH_FLOW.
        const EDGE_INDEX: usize = 42;
        let edge = &tile_view.directed_edges()[EDGE_INDEX];

        assert_eq!(edge.free_flow_speed(), 100);
        assert_eq!(edge.constrained_flow_speed(), 42);
        assert_eq!(edge.has_predicted_speed(), true);

        // A few predicted speed samples.
        // See predicted_speeds.rs for the array of speeds that we expected to encode.
        assert!(
            tile_view
                .get_predicted_speed(EDGE_INDEX, 0)
                .is_some_and(|s| { (s - 36f32).abs() < 0.5 })
        );

        // 60 * 5 = number of seconds in a 5 minute block. We encode data in 5 min chunks.
        assert!(
            tile_view
                .get_predicted_speed(EDGE_INDEX, 42 * 60 * 5)
                .is_some_and(|s| { (s - 45f32).abs() < 0.5 })
        );

        assert!(
            tile_view
                .get_predicted_speed(EDGE_INDEX, 20 * 60 * 5)
                .is_some_and(|s| { (s - 42f32).abs() < 0.5 })
        );

        // There are 2016 total buckets per week; this indexes into the last one (zero indexed)
        assert!(
            tile_view
                .get_predicted_speed(EDGE_INDEX, 2016 * 60 * 5 - 1)
                .is_some_and(|s| { (s - 29f32).abs() < 0.5 })
        );
    }

    #[test]
    fn test_predicted_traffic_speeds_second_profile() {
        let tile = &*TEST_GRAPH_TILE_WITH_FLOW;
        let tile_view = tile.borrow_dependent();

        // We specifically added predicted speeds to another random edge index.
        // See the test case info in the comment for TEST_GRAPH_TILE_WITH_FLOW.
        const EDGE_INDEX: usize = 7;
        let edge = &tile_view.directed_edges()[EDGE_INDEX];

        assert_eq!(edge.free_flow_speed(), 12);
        // No, this isn't intended to make sense; it's test data ;)
        assert_eq!(edge.constrained_flow_speed(), 34);
        assert_eq!(edge.has_predicted_speed(), true);

        // Reconstruct the entire array of speeds.
        let speeds: [i64; BUCKETS_PER_WEEK] = std::array::from_fn(|i| {
            tile_view
                .get_predicted_speed(EDGE_INDEX, (i as u32) * 300)
                .unwrap() as i64
        });

        // Laying it all out, this highlights that the encoding is indeed quite.... lossy ;)
        // This was originally a series going from 0 to 100 in a loop, sawtooth fashion.
        // DCT is optimized for high compressibility of datasets which don't vary so wildly.
        // As one would expect for datasets like speed variance over time.
        assert_eq!(
            speeds,
            [
                0, 0, 0, 1, 3, 4, 6, 8, 9, 11, 12, 13, 13, 14, 14, 14, 15, 15, 15, 16, 17, 18, 20,
                21, 23, 25, 27, 28, 30, 31, 32, 33, 33, 34, 34, 34, 34, 35, 35, 36, 37, 38, 40, 41,
                43, 45, 47, 49, 50, 52, 53, 53, 54, 54, 54, 54, 54, 54, 54, 55, 56, 57, 59, 61, 63,
                66, 68, 70, 72, 73, 74, 74, 75, 74, 74, 73, 72, 72, 72, 72, 74, 75, 78, 81, 84, 87,
                91, 94, 97, 99, 100, 99, 98, 94, 90, 84, 77, 69, 61, 52, 43, 35, 27, 20, 14, 9, 5,
                3, 1, 1, 2, 4, 6, 8, 11, 13, 16, 18, 20, 22, 23, 24, 24, 25, 25, 25, 26, 26, 27,
                27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 48, 48, 49,
                50, 51, 51, 52, 52, 53, 54, 55, 56, 57, 58, 60, 61, 63, 64, 66, 68, 69, 70, 71, 72,
                72, 72, 73, 72, 72, 72, 73, 73, 74, 75, 77, 80, 82, 85, 88, 91, 94, 96, 98, 98, 98,
                96, 93, 89, 84, 77, 70, 62, 53, 45, 36, 28, 21, 15, 9, 5, 2, 1, 0, 1, 2, 4, 7, 10,
                13, 16, 18, 21, 23, 24, 25, 26, 26, 26, 26, 26, 26, 26, 26, 27, 28, 29, 30, 32, 33,
                35, 36, 38, 39, 41, 42, 43, 44, 45, 46, 47, 47, 48, 48, 49, 50, 50, 51, 52, 53, 54,
                55, 56, 58, 59, 61, 62, 64, 65, 67, 68, 69, 70, 71, 71, 72, 72, 72, 72, 72, 72, 73,
                74, 75, 76, 78, 80, 83, 86, 88, 91, 94, 96, 97, 97, 97, 95, 92, 88, 83, 77, 70, 62,
                54, 45, 37, 29, 22, 15, 10, 5, 2, 0, 0, 0, 2, 4, 6, 9, 13, 16, 19, 21, 23, 25, 26,
                26, 27, 27, 26, 26, 26, 26, 26, 26, 27, 28, 29, 31, 33, 34, 36, 38, 40, 42, 43, 44,
                45, 46, 47, 47, 47, 48, 48, 48, 49, 50, 50, 51, 52, 54, 55, 56, 58, 60, 61, 63, 64,
                66, 67, 68, 69, 70, 70, 71, 71, 71, 71, 71, 72, 72, 73, 74, 75, 77, 79, 81, 83, 86,
                89, 91, 94, 95, 97, 97, 96, 95, 92, 88, 83, 77, 70, 62, 54, 46, 37, 30, 22, 16, 10,
                5, 2, 0, 0, 0, 1, 3, 6, 9, 12, 15, 18, 21, 23, 25, 26, 27, 27, 27, 27, 26, 26, 26,
                26, 26, 26, 27, 29, 30, 32, 34, 36, 38, 40, 42, 43, 45, 46, 46, 47, 47, 47, 48, 48,
                48, 48, 49, 50, 51, 52, 53, 55, 56, 58, 60, 62, 63, 65, 66, 68, 68, 69, 70, 70, 70,
                70, 70, 70, 71, 71, 71, 72, 73, 75, 77, 79, 81, 84, 87, 89, 92, 94, 96, 96, 97, 96,
                94, 91, 87, 82, 76, 69, 62, 54, 46, 38, 30, 23, 16, 10, 6, 3, 0, 0, 0, 1, 3, 5, 8,
                12, 15, 18, 21, 23, 25, 26, 27, 27, 27, 27, 27, 26, 26, 26, 26, 26, 27, 28, 30, 32,
                34, 36, 38, 40, 42, 44, 45, 46, 47, 47, 48, 48, 48, 48, 48, 48, 49, 49, 50, 52, 53,
                55, 56, 58, 60, 62, 64, 65, 67, 68, 69, 69, 70, 70, 70, 70, 70, 70, 70, 71, 71, 72,
                73, 75, 77, 79, 82, 84, 87, 90, 92, 94, 96, 96, 96, 96, 94, 91, 87, 82, 76, 69, 62,
                54, 46, 38, 30, 23, 16, 11, 6, 3, 1, 0, 0, 0, 2, 5, 8, 11, 15, 18, 21, 23, 25, 27,
                28, 28, 28, 28, 27, 27, 26, 26, 26, 26, 27, 28, 30, 31, 33, 36, 38, 40, 42, 44, 45,
                46, 47, 48, 48, 48, 48, 48, 48, 48, 49, 49, 50, 51, 53, 54, 56, 58, 60, 62, 64, 66,
                67, 68, 69, 70, 70, 70, 70, 70, 70, 70, 70, 71, 71, 72, 73, 75, 77, 79, 82, 85, 87,
                90, 92, 94, 96, 96, 96, 95, 93, 90, 86, 81, 76, 69, 62, 54, 46, 38, 30, 23, 17, 11,
                7, 3, 1, 0, 0, 0, 2, 5, 8, 11, 14, 17, 20, 23, 25, 27, 28, 28, 28, 28, 27, 27, 26,
                26, 26, 26, 27, 28, 29, 31, 33, 35, 38, 40, 42, 44, 45, 47, 48, 48, 48, 48, 48, 48,
                48, 48, 48, 49, 50, 51, 52, 54, 56, 58, 60, 62, 64, 66, 67, 68, 69, 70, 70, 70, 70,
                70, 70, 70, 70, 70, 71, 71, 73, 75, 77, 79, 82, 85, 87, 90, 93, 95, 96, 97, 97, 96,
                93, 90, 86, 81, 75, 69, 61, 54, 46, 38, 31, 23, 17, 11, 7, 3, 1, 0, 0, 0, 2, 4, 7,
                11, 14, 17, 20, 23, 25, 27, 28, 28, 28, 28, 28, 27, 27, 26, 26, 26, 27, 28, 29, 31,
                33, 35, 37, 40, 42, 44, 45, 47, 48, 48, 49, 49, 49, 48, 48, 48, 48, 49, 49, 51, 52,
                54, 55, 58, 60, 62, 64, 66, 67, 69, 70, 70, 71, 71, 71, 70, 70, 70, 70, 70, 70, 71,
                73, 74, 77, 79, 82, 85, 88, 90, 93, 95, 96, 97, 97, 96, 94, 90, 86, 81, 75, 68, 61,
                54, 46, 38, 31, 24, 17, 12, 7, 4, 1, 0, 0, 1, 2, 5, 7, 10, 14, 17, 20, 22, 25, 26,
                27, 28, 28, 28, 28, 27, 27, 26, 26, 26, 27, 28, 29, 31, 32, 35, 37, 39, 41, 44, 45,
                47, 48, 48, 49, 49, 49, 49, 48, 48, 48, 49, 49, 50, 52, 53, 55, 57, 59, 62, 64, 66,
                68, 69, 70, 71, 71, 71, 71, 70, 70, 70, 69, 69, 70, 71, 72, 74, 76, 79, 82, 85, 88,
                91, 93, 95, 97, 97, 97, 96, 94, 90, 86, 81, 75, 68, 61, 53, 45, 38, 30, 23, 17, 12,
                7, 4, 1, 0, 0, 1, 2, 5, 7, 10, 14, 17, 20, 22, 25, 26, 28, 28, 29, 29, 28, 28, 27,
                27, 26, 26, 27, 28, 29, 30, 32, 34, 37, 39, 41, 43, 45, 47, 48, 49, 49, 49, 49, 49,
                49, 49, 49, 49, 49, 50, 52, 53, 55, 57, 59, 62, 64, 66, 68, 69, 70, 71, 71, 71, 71,
                71, 70, 70, 70, 70, 70, 71, 72, 74, 76, 79, 82, 85, 88, 91, 93, 95, 97, 98, 97, 96,
                94, 91, 86, 81, 75, 68, 61, 53, 45, 37, 30, 23, 17, 12, 7, 4, 2, 0, 0, 1, 2, 5, 7,
                10, 13, 17, 20, 22, 24, 26, 28, 28, 29, 29, 28, 28, 27, 27, 27, 27, 27, 28, 29, 31,
                32, 34, 37, 39, 41, 43, 45, 47, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 51,
                53, 55, 57, 59, 61, 64, 66, 67, 69, 70, 71, 71, 71, 71, 71, 70, 70, 70, 70, 70, 71,
                72, 74, 76, 79, 81, 85, 88, 91, 93, 96, 97, 98, 98, 96, 94, 91, 86, 81, 75, 68, 60,
                53, 45, 37, 30, 23, 17, 12, 7, 4, 2, 1, 1, 1, 3, 5, 7, 10, 13, 16, 19, 22, 24, 26,
                27, 28, 28, 28, 28, 28, 27, 27, 27, 27, 27, 28, 29, 31, 32, 34, 37, 39, 41, 43, 45,
                46, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 50, 50, 51, 53, 55, 57, 59, 61, 64, 66,
                68, 69, 70, 71, 72, 72, 71, 71, 70, 70, 70, 69, 70, 70, 72, 73, 76, 78, 81, 84, 88,
                91, 94, 96, 97, 98, 98, 97, 94, 91, 86, 81, 75, 68, 60, 53, 45, 37, 30, 23, 17, 12,
                7, 4, 2, 1, 1, 1, 3, 5, 7, 10, 13, 16, 19, 22, 24, 26, 27, 28, 28, 28, 28, 28, 28,
                27, 27, 27, 27, 28, 29, 30, 32, 34, 36, 38, 41, 43, 45, 46, 48, 49, 49, 50, 50, 50,
                49, 49, 49, 49, 50, 50, 51, 53, 54, 56, 59, 61, 63, 65, 67, 69, 70, 71, 72, 72, 72,
                71, 71, 70, 70, 70, 70, 71, 72, 73, 76, 78, 81, 84, 88, 91, 93, 96, 97, 98, 98, 97,
                94, 91, 86, 81, 75, 68, 60, 52, 44, 37, 29, 23, 17, 12, 7, 4, 2, 1, 1, 2, 3, 5, 8,
                11, 13, 16, 19, 22, 24, 26, 27, 28, 28, 28, 28, 28, 28, 27, 27, 27, 28, 28, 29, 31,
                32, 34, 36, 38, 41, 43, 45, 46, 48, 49, 49, 50, 50, 50, 50, 49, 49, 49, 50, 50, 51,
                53, 54, 56, 58, 61, 63, 65, 67, 69, 70, 71, 72, 72, 72, 71, 71, 70, 70, 70, 70, 70,
                71, 73, 75, 78, 81, 84, 87, 90, 93, 96, 97, 98, 98, 97, 95, 91, 87, 81, 75, 68, 60,
                52, 44, 37, 29, 23, 17, 12, 7, 4, 2, 1, 1, 2, 3, 5, 8, 11, 13, 16, 19, 21, 23, 25,
                27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 30, 31, 32, 34, 36, 38, 40, 42, 44,
                46, 47, 48, 49, 49, 50, 50, 50, 50, 50, 50, 50, 51, 52, 53, 54, 56, 58, 61, 63, 65,
                67, 69, 70, 71, 72, 72, 72, 72, 71, 71, 70, 70, 70, 71, 72, 73, 75, 78, 81, 84, 87,
                90, 93, 96, 97, 98, 98, 97, 95, 91, 87, 81, 75, 68, 60, 52, 44, 36, 29, 22, 16, 11,
                7, 4, 2, 1, 1, 2, 4, 6, 8, 11, 13, 16, 19, 21, 23, 25, 26, 27, 28, 28, 28, 28, 28,
                28, 28, 28, 28, 29, 30, 31, 32, 34, 36, 38, 40, 42, 44, 45, 47, 48, 49, 49, 50, 50,
                50, 50, 50, 50, 50, 51, 52, 53, 54, 56, 58, 60, 63, 65, 67, 69, 70, 71, 72, 72, 72,
                72, 71, 71, 70, 70, 70, 70, 71, 73, 75, 77, 80, 83, 87, 90, 93, 96, 97, 99, 99, 97,
                95, 92, 87, 82, 75, 68, 60, 52, 44, 36, 29, 22, 16, 11, 7, 4, 2, 1, 2, 2, 4, 6, 8,
                11, 14, 16, 19, 21, 23, 25, 26, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 29, 30, 31,
                33, 34, 36, 38, 40, 42, 44, 45, 47, 48, 49, 49, 50, 50, 50, 50, 50, 50, 51, 51, 52,
                53, 54, 56, 58, 60, 62, 64, 66, 68, 70, 71, 72, 72, 72, 72, 72, 71, 71, 70, 70, 71,
                72, 73, 75, 77, 80, 83, 86, 90, 93, 95, 97, 98, 99, 98, 95, 92, 88, 82, 75, 68, 60,
                52, 44, 36, 29, 22, 16, 11, 7, 4, 2, 2, 2, 3, 4, 6, 9, 11, 14, 17, 19, 21, 23, 25,
                26, 26, 27, 27, 27, 28, 28, 28, 28, 28, 29, 29, 30, 31, 33, 34, 36, 38, 40, 42, 43,
                45, 46, 48, 49, 49, 50, 50, 50, 50, 50, 51, 51, 51, 52, 53, 54, 56, 58, 60, 62, 64,
                66, 68, 70, 71, 72, 72, 73, 73, 72, 72, 71, 71, 71, 71, 72, 73, 75, 77, 80, 83, 86,
                89, 93, 95, 97, 99, 99, 98, 96, 93, 88, 82, 76, 68, 60, 52, 44, 36, 28, 21, 15, 10,
                6, 4, 2, 2, 2, 3, 5, 7, 9, 12, 14, 17, 19, 21, 23, 24, 25, 26, 26, 27, 27, 27, 28,
                28, 28, 29, 29, 30, 31, 32, 33, 35, 36, 38, 39, 41, 43, 44, 46, 47, 48, 49, 50, 50,
                51, 51, 51, 51, 52, 52, 53, 53, 54, 55, 57, 59, 61, 63, 65, 67, 69, 71, 72, 73, 73,
                73, 73, 73, 72, 72, 71, 71, 71, 72, 73, 75, 78, 81, 85, 88, 92, 95, 98, 100, 101,
                100, 98, 95, 90, 83, 76, 68, 59, 50, 41, 33, 25, 19, 13, 9, 6, 5, 4, 5, 6, 8, 9,
                11, 12, 12
            ]
        )
    }

    #[test]
    fn test_get_nodes_within_radius() {
        let mut rng = rng();
        let tile = &*TEST_GRAPH_TILE_WITH_FLOW;
        let tile_view = tile.borrow_dependent();
        let sw = tile_view.header().sw_corner();

        for (idx, node) in tile_view.nodes().into_iter().enumerate().filter(|_| {
            if cfg!(miri) {
                rng.random_bool(0.1)
            } else {
                true
            }
        }) {
            assert!(
                tile_view
                    .nodes_within_radius(|_| true, node.coordinate(sw).into(), 25.0)
                    .any(|(result_node, distance)| {
                        result_node.node_id
                            == tile
                                .header()
                                .graph_id()
                                .with_feature_index(idx as u64)
                                .unwrap()
                            && distance == 0.0
                    }),
                "Expected to find a match for the node"
            );
            assert!(
                tile_view
                    .nodes_within_radius(|_| true, node.coordinate(sw).into(), 25.0)
                    .all(|(_, distance)| { distance <= 25.0 }),
                "Expected all nodes to be within the search radius"
            );
        }
    }

    /// Values of the `node_type` field for transit nodes.
    const TRANSIT_EGRESS_NODE_TYPE: u8 = 4;
    const TRANSIT_STATION_NODE_TYPE: u8 = 5;
    const TRANSIT_PLATFORM_NODE_TYPE: u8 = 6;

    fn text_at<'a>(tile_view: &'a GraphTileView<'_>, offset: u32) -> Cow<'a, str> {
        tile_view.text_memory[offset as usize..].as_cow_str()
    }

    #[test]
    fn test_decode_all_transit_fixture_tiles() {
        let transit_level_dir = transit_fixture_dir().join("3");
        let mut tile_count = 0;
        for entry in WalkDir::new(transit_level_dir) {
            let entry = entry.expect("Unable to read fixture directory");
            if entry.path().extension().is_none_or(|ext| ext != "gph") {
                continue;
            }

            let bytes = std::fs::read(entry.path()).expect("Unable to read file");
            let tile_view = GraphTileView::try_from(bytes.as_slice())
                .unwrap_or_else(|e| panic!("Unable to decode {}: {e}", entry.path().display()));
            let header = tile_view.header();
            assert_eq!(header.graph_id().level(), 3);
            assert_eq!(
                tile_view.transit_departures.len(),
                header.departure_count() as usize
            );
            assert_eq!(tile_view.transit_stops.len(), header.stop_count() as usize);
            assert_eq!(
                tile_view.transit_routes.len(),
                header.route_count() as usize
            );
            assert_eq!(
                tile_view.transit_schedules.len(),
                header.schedule_count() as usize
            );
            assert_eq!(
                tile_view.transit_transfers.len(),
                header.transfer_count() as usize
            );
            tile_count += 1;
        }

        assert_eq!(tile_count, 1, "Expected one transit tile in the fixture");
    }

    #[test]
    fn test_unsupported_tile_level() {
        let mut bytes = TEST_TRANSIT_TILE_L3.borrow_owner().clone();
        // The level is in the 3 low bits of the graph ID at the start of the header.
        bytes[0] = (bytes[0] & !0b111) | 4;

        assert!(matches!(
            GraphTileView::try_from(bytes.as_slice()),
            Err(GraphTileDecodingError::UnsupportedTileLevel(4))
        ));
    }

    #[test]
    fn test_transit_stops() {
        let tile = &*TEST_TRANSIT_TILE_L3;
        let tile_view = tile.borrow_dependent();
        let sw = tile_view.header().sw_corner();

        // Valhalla makes a station node and an egress node for each GTFS stop
        // that has no parent station.
        assert_eq!(tile_view.nodes().len(), 12);
        assert_eq!(tile_view.transit_stops.len(), 12);

        let mut platforms = Vec::new();
        for node in tile_view.nodes() {
            let stop = &tile_view.transit_stops[node.transition_index() as usize];
            let name = text_at(tile_view, stop.name_offset());
            let one_stop_id = text_at(tile_view, stop.one_stop_offset());
            match node.node_type() {
                TRANSIT_PLATFORM_NODE_TYPE => {
                    assert!(!stop.generated());
                    let coordinate = node.coordinate(sw);
                    platforms.push((one_stop_id, name, coordinate.y, coordinate.x));
                }
                TRANSIT_STATION_NODE_TYPE => {
                    assert!(stop.generated());
                    assert!(one_stop_id.ends_with("_transit_station"));
                }
                TRANSIT_EGRESS_NODE_TYPE => {
                    assert!(stop.generated());
                    assert!(one_stop_id.ends_with("_transit_egress"));
                }
                other => panic!("Unexpected node type {other} in a transit tile"),
            }
        }
        platforms.sort_by(|a, b| a.0.cmp(&b.0));

        // The stops in the GTFS feed that built the fixture
        let expected = [
            ("andorra-test_S1", "Plaça U", 42.50655, 1.52100),
            ("andorra-test_S2", "Plaça Dos", 42.50655, 1.52300),
            ("andorra-test_S3", "Plaça Tres", 42.50655, 1.52500),
            ("andorra-test_S4", "Plaça Quatre", 42.50725, 1.52605),
        ];
        assert_eq!(platforms.len(), expected.len());
        for ((one_stop_id, name, lat, lon), (exp_id, exp_name, exp_lat, exp_lon)) in
            platforms.iter().zip(expected)
        {
            assert_eq!(one_stop_id, exp_id);
            assert_eq!(name, exp_name);
            // Node coordinates have 7 decimal digits, but f32 loses some of them at these values.
            assert!(
                (lat - exp_lat).abs() < 1e-5,
                "{name}: lat {lat} != {exp_lat}"
            );
            assert!(
                (lon - exp_lon).abs() < 1e-5,
                "{name}: lon {lon} != {exp_lon}"
            );
        }

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(tile_view.transit_stops);
        }
    }

    #[test]
    fn test_transit_routes() {
        let tile = &*TEST_TRANSIT_TILE_L3;
        let tile_view = tile.borrow_dependent();

        // The route and the agency in the GTFS feed that built the fixture
        let [route] = tile_view.transit_routes else {
            panic!("Expected one route in the transit tile")
        };
        assert_eq!(text_at(tile_view, route.short_name_offset()), "L1");
        assert_eq!(
            text_at(tile_view, route.long_name_offset()),
            "Línia de prova"
        );
        assert_eq!(
            text_at(tile_view, route.description_offset()),
            "Test route over the synthetic grid"
        );
        assert_eq!(
            text_at(tile_view, route.one_stop_offset()),
            "andorra-test_L1"
        );
        assert_eq!(
            text_at(tile_view, route.operator_one_stop_offset()),
            "andorra-test_VTA"
        );
        assert_eq!(
            text_at(tile_view, route.operator_name_offset()),
            "Valinor Test Agency"
        );
        assert_eq!(
            text_at(tile_view, route.operator_website_offset()),
            "https://example.com/valinor-test-agency"
        );
        // Bus
        assert_eq!(route.route_type(), 3);
        assert_eq!(route.route_color(), 0x00_55_A4);
        assert_eq!(route.route_text_color(), 0xFF_FF_FF);

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(tile_view.transit_routes);
        }
    }

    #[test]
    fn test_transit_departures() {
        let tile = &*TEST_TRANSIT_TILE_L3;
        let tile_view = tile.borrow_dependent();

        let mut departures: Vec<_> = tile_view
            .transit_departures
            .iter()
            .map(|departure| {
                assert_eq!(departure.route_index(), 0);
                assert!(
                    usize::from(departure.schedule_index()) < tile_view.transit_schedules.len()
                );
                (
                    departure.departure_time(),
                    departure.elapsed_time(),
                    departure.departure_type(),
                    departure.end_time(),
                    departure.frequency(),
                    text_at(tile_view, departure.headsign_offset()),
                    departure.wheelchair_accessible(),
                    departure.bicycle_accessible(),
                )
            })
            .collect();
        departures.sort_by_key(|departure| departure.0);

        // The trips in the GTFS feed that built the fixture.
        // The last stop of each trip has no departure.
        let fixed = |time, headsign, bicycle_accessible| {
            let headsign = Cow::from(headsign);
            (time, 120, 0, None, None, headsign, true, bicycle_accessible)
        };
        // Each stop of a frequency trip has the end time of the frequency entry.
        let frequency = |time| {
            let headsign = Cow::from("Plaça Quatre");
            (
                time,
                120,
                1,
                Some(12 * 3600),
                Some(900),
                headsign,
                false,
                true,
            )
        };
        let expected = vec![
            fixed(8 * 3600, "Plaça Quatre", true),
            fixed(8 * 3600 + 150, "Plaça Quatre", true),
            fixed(8 * 3600 + 300, "Plaça Quatre", true),
            fixed(8 * 3600 + 1800, "Plaça U", false),
            fixed(8 * 3600 + 1920, "Plaça U", false),
            fixed(8 * 3600 + 2040, "Plaça U", false),
            frequency(9 * 3600),
            frequency(9 * 3600 + 120),
            frequency(9 * 3600 + 240),
        ];
        assert_eq!(departures, expected);

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(tile_view.transit_departures);
        }
    }

    #[test]
    fn test_transit_schedules_and_transfers() {
        let tile = &*TEST_TRANSIT_TILE_L3;
        let tile_view = tile.borrow_dependent();

        assert!(!tile_view.transit_schedules.is_empty());
        for schedule in tile_view.transit_schedules {
            // Monday to Friday, from the calendar of the GTFS feed
            assert_eq!(schedule.days_of_week(), 0b011_1110);

            // The day bits start at the build date, so check the weekly pattern only.
            let end_day = u32::from(schedule.end_day());
            assert!((6..64).contains(&end_day));
            let days = schedule.days();
            let is_valid = |day: u32| days & (1 << day) != 0;
            assert_eq!((0..7).filter(|&day| is_valid(day)).count(), 5);
            for day in 7..=end_day {
                assert_eq!(is_valid(day), is_valid(day - 7), "Day {day}");
            }
            assert_eq!(days.checked_shr(end_day + 1).unwrap_or(0), 0);
        }

        // Valhalla does not write transfers into transit tiles
        assert!(tile_view.transit_transfers.is_empty());

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(tile_view.transit_schedules);
        }
    }

    #[test]
    fn test_transit_tile_bins() {
        let tile = &*TEST_TRANSIT_TILE_L3;
        let tile_view = tile.borrow_dependent();
        assert_eq!(tile_view.level, ValhallaLevel::Transit);
        assert_eq!(tile_view.edge_bins, []);

        assert_eq!(tile_view.bin_index_xy(0, 0), 0);
        assert_eq!(tile_view.bin_index_xy(1, 2), 11);
        assert_eq!(tile_view.bin_index_xy(4, 4), crate::BIN_COUNT - 1);
        for bin_index in 0..crate::BIN_COUNT {
            assert_eq!(tile_view.edges_in_bin(bin_index), []);
        }
    }

    #[test]
    fn test_local_tile_from_transit_build() {
        let local_tile = &*TEST_TRANSIT_TILE_L2;
        let transit_tile = &*TEST_TRANSIT_TILE_L3;
        assert_eq!(local_tile.header().graph_id().level(), 2);

        // Valhalla connects each of the 4 transit egress nodes
        // to both end nodes of the closest road edge, in both directions.
        let mut egress_ids: Vec<_> = local_tile
            .directed_edges()
            .iter()
            .filter(|edge| edge.road_use() == RoadUse::TransitConnection)
            .map(|edge| {
                let end_node = transit_tile
                    .get_node(edge.end_node_id())
                    .expect("A transit connection must end in the transit tile");
                assert_eq!(end_node.node_type(), TRANSIT_EGRESS_NODE_TYPE);
                edge.end_node_id()
            })
            .collect();
        assert_eq!(egress_ids.len(), 8);
        egress_ids.sort_by_key(GraphId::value);
        egress_ids.dedup();
        assert_eq!(egress_ids.len(), 4);

        let egress_to_road = transit_tile
            .directed_edges()
            .iter()
            .filter(|edge| edge.road_use() == RoadUse::TransitConnection)
            .inspect(|edge| assert!(local_tile.may_contain_id(edge.end_node_id())))
            .count();
        assert_eq!(egress_to_road, 8);
    }
}
