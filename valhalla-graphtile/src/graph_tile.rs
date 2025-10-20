use thiserror::Error;
use zerocopy::{FromBytes, I16, LE, U32, U64, transmute};

use enumset::EnumSet;
use self_cell::self_cell;
#[cfg(test)]
use std::sync::LazyLock;
// To keep files manageable, we will keep internal modules specific to each mega-struct,
// and publicly re-export the public type.
// Each struct should be tested on fixture tiles to a reasonable level of confidence.
// Leverage snapshot tests where possible, compare with Valhalla C++ results,
// and test the first and last elements of variable length vectors
// with snapshot tests.

mod access_restriction;
mod admin;
mod builder;
mod directed_edge;
mod edge_info;
mod header;
mod node;
pub mod predicted_speeds;
mod sign;
mod transit;
mod turn_lane;

use crate::graph_tile::predicted_speeds::{COEFFICIENT_COUNT, PredictedSpeeds};
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
pub enum GraphTileError {
    #[error("Unable to extract a slice of the correct length; the tile data is malformed.")]
    SliceArrayConversion(#[from] std::array::TryFromSliceError),
    #[error("Unable to extract a slice of the correct length; the tile data is malformed.")]
    SliceLength,
    #[error("The byte sequence is not valid for this type.")]
    ByteSequenceValidityError,
    #[error("Invalid graph ID.")]
    GraphIdParseError(#[from] InvalidGraphIdError),
    #[error("Data cast failed (this almost always means invalid data): {0}")]
    CastError(String),
    #[error(
        "Expected to have consumed all bytes in the graph tile, but we still have a leftover buffer of {0} bytes. This is either a tile reader implementation error, or the tile is invalid."
    )]
    LeftoverBytesAfterReading(usize),
    #[error("Tile level {0} is not currently supported by Valinor.")]
    UnsupportedTileLevel(u8),
}

#[derive(Debug, Error)]
pub enum LookupError {
    #[error("Mismatched base; the graph ID cannot exist in this tile.")]
    MismatchedBase,
    #[error("The feature at the index specified does not exist in this tile.")]
    InvalidIndex,
}

pub trait GraphTile {
    /// Gets the Graph ID of the tile.
    fn graph_id(&self) -> GraphId;

    /// Does the supplied graph ID belong in this tile?
    ///
    /// A true result does not necessarily guarantee that an object with this ID exists,
    /// but in that case, either you've cooked up an invalid ID for fun,
    /// or the graph is invalid.
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

    /// Gets a reference to the directed edge in this tile by graph ID.
    ///
    /// # Errors
    ///
    /// Returns an error if the graph ID cannot be contained in this tile
    /// or the index is invalid.
    fn get_directed_edge(&self, id: GraphId) -> Result<&DirectedEdge, LookupError>;

    /// Gets the index for the opposing index of a directed edge.
    ///
    /// # Errors
    ///
    /// Returns a [`LookupError`] if the graph ID is not present in the tile.
    fn get_opp_edge_index(&self, graph_id: GraphId) -> Result<u32, LookupError>;

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
    /// Note that this is NOT a zero-cost operation and involves parsing data
    /// from various parts of memory such as the text list.
    /// As such, it is recommended to avoid calling this during costing.
    ///
    /// # Errors
    ///
    /// Since this accepts a directed edge reference,
    /// any errors that arise are due to invalid/corrupt graph tiles.
    fn get_edge_info(&self, directed_edge: &DirectedEdge) -> Result<EdgeInfo<'_>, GraphTileError>;

    // Lower level "raw" accessors

    /// A raw slice of the tile's directed edges (i.e. for iteration).
    fn directed_edges(&self) -> &[DirectedEdge];

    /// Administrative regions covered in this tile.
    fn admins(&self) -> &[Admin];
}

self_cell! {
    /// A read-only owned view of a graph tile.
    ///
    /// This can be constructed from an owned byte array, `Vec<u8>`.
    pub struct GraphTileHandle {
        owner: Vec<u8>,
        #[covariant]
        dependent: GraphTileView,
    }
}

impl GraphTile for GraphTileHandle {
    #[inline]
    fn graph_id(&self) -> GraphId {
        self.borrow_dependent().graph_id()
    }

    #[inline]
    fn may_contain_id(&self, id: GraphId) -> bool {
        self.borrow_dependent().may_contain_id(id)
    }

    #[inline]
    fn header(&self) -> &GraphTileHeader {
        self.borrow_dependent().header()
    }

    #[inline]
    fn get_node(&self, id: GraphId) -> Result<&NodeInfo, LookupError> {
        self.borrow_dependent().get_node(id)
    }

    #[inline]
    fn get_directed_edge(&self, id: GraphId) -> Result<&DirectedEdge, LookupError> {
        self.borrow_dependent().get_directed_edge(id)
    }

    #[inline]
    fn get_opp_edge_index(&self, graph_id: GraphId) -> Result<u32, LookupError> {
        self.borrow_dependent().get_opp_edge_index(graph_id)
    }

    #[inline]
    fn get_ext_directed_edge(&self, id: GraphId) -> Result<&DirectedEdgeExt, LookupError> {
        self.borrow_dependent().get_ext_directed_edge(id)
    }

    #[inline]
    fn get_access_restrictions(
        &self,
        directed_edge_index: u32,
        access_modes: EnumSet<Access>,
    ) -> Vec<&AccessRestriction> {
        self.borrow_dependent()
            .get_access_restrictions(directed_edge_index, access_modes)
    }

    #[inline]
    fn get_predicted_speed(
        &self,
        directed_edge_index: usize,
        seconds_from_start_of_week: u32,
    ) -> Option<f32> {
        self.borrow_dependent()
            .get_predicted_speed(directed_edge_index, seconds_from_start_of_week)
    }

    #[inline]
    fn get_edge_info(&self, directed_edge: &DirectedEdge) -> Result<EdgeInfo<'_>, GraphTileError> {
        self.borrow_dependent().get_edge_info(directed_edge)
    }

    #[inline]
    fn directed_edges(&self) -> &[DirectedEdge] {
        self.borrow_dependent().directed_edges()
    }

    #[inline]
    fn admins(&self) -> &[Admin] {
        self.borrow_dependent().admins()
    }
}

impl TryFrom<Vec<u8>> for GraphTileHandle {
    type Error = GraphTileError;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        GraphTileHandle::try_new(value, |data| GraphTileView::try_from(data.as_ref()))
    }
}

/// An internal view over a single tile in the Valhalla hierarchical tile graph.
///
/// Access should normally go through the [``GraphTile``](GraphTile) trait.
struct GraphTileView<'a> {
    /// Header with various metadata about the tile and internal sizes.
    header: GraphTileHeader,
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
    edge_bins: Vec<GraphId>,
    complex_forward_restrictions_memory: &'a [u8],
    complex_reverse_restrictions_memory: &'a [u8],
    // Variable length byte arrays (indexed into at various other points; hidden with public safe accessors)...
    // These are all slices which DO have a known size at runtime, but not at compile time.
    edge_info_memory: &'a [u8],
    text_memory: &'a [u8],
    lane_connectivity_memory: &'a [u8],
    predicted_speeds: Option<PredictedSpeeds<'a>>,
    // TODO: Stop one stops(?)
    // TODO: Route one stops(?)
    // TODO: Operator one stops(?)
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
        &self.header
    }

    #[inline]
    fn get_node(&self, id: GraphId) -> Result<&NodeInfo, LookupError> {
        if self.may_contain_id(id) {
            self.nodes
                .get(id.index() as usize)
                .ok_or(LookupError::InvalidIndex)
        } else {
            Err(LookupError::MismatchedBase)
        }
    }

    /// Gets a reference to the directed edge in this tile by graph ID.
    ///
    /// # Errors
    ///
    /// Returns an error if the graph ID cannot be contained in this tile
    /// or the index is invalid.
    fn get_directed_edge(&self, id: GraphId) -> Result<&DirectedEdge, LookupError> {
        if self.may_contain_id(id) {
            self.directed_edges
                .get(id.index() as usize)
                .ok_or(LookupError::InvalidIndex)
        } else {
            Err(LookupError::MismatchedBase)
        }
    }

    fn get_opp_edge_index(&self, graph_id: GraphId) -> Result<u32, LookupError> {
        let edge = self.get_directed_edge(graph_id)?;

        // The edge might leave the tile, so we have to do a complicated lookup
        let end_node_id = edge.end_node_id();
        let opp_edge_index = edge.opposing_edge_index();

        // TODO: Probably a cleaner pattern here?
        let node_edge_index = self.get_node(end_node_id).map(NodeInfo::edge_index)?;

        Ok(node_edge_index + opp_edge_index)
    }

    fn get_ext_directed_edge(&self, id: GraphId) -> Result<&DirectedEdgeExt, LookupError> {
        if self.may_contain_id(id) {
            self.ext_directed_edges
                .get(id.index() as usize)
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
        self.predicted_speeds.and_then(|ps| {
            if self.directed_edges[directed_edge_index].has_predicted_speed() {
                ps.speed(directed_edge_index, seconds_from_start_of_week)
            } else {
                None
            }
        })
    }

    fn get_edge_info(&self, directed_edge: &DirectedEdge) -> Result<EdgeInfo<'_>, GraphTileError> {
        let edge_info_offset = directed_edge.edge_info_offset() as usize;

        EdgeInfo::try_from((&self.edge_info_memory[edge_info_offset..], self.text_memory))
    }

    #[inline]
    fn directed_edges(&self) -> &[DirectedEdge] {
        self.directed_edges
    }

    #[inline]
    fn admins(&self) -> &[Admin] {
        self.admins
    }
}

impl<'a> TryFrom<&'a [u8]> for GraphTileView<'a> {
    type Error = GraphTileError;

    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        // Get the byte range of the header so we can transmute it
        const HEADER_SIZE: usize = size_of::<GraphTileHeader>();

        let header_range = 0..HEADER_SIZE;

        // Fixed-size header
        let header_slice: [u8; HEADER_SIZE] = bytes[header_range].try_into()?;
        let header: GraphTileHeader = transmute!(header_slice);

        let level = header.graph_id().level();
        if level > 2 {
            // No transit tile support yet (see the end of this function for some more specific TODOs)
            return Err(GraphTileError::UnsupportedTileLevel(level));
        }

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

        // Reference to the slice which we'll keep re-binding as we go,
        // consuming the DSTs as we go.
        let bytes = &bytes[HEADER_SIZE..];

        // Basic features
        let (nodes, bytes) =
            <[NodeInfo]>::ref_from_prefix_with_elems(bytes, header.node_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transitions, bytes) = <[NodeTransition]>::ref_from_prefix_with_elems(
            bytes,
            header.transition_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (directed_edges, bytes) = <[DirectedEdge]>::ref_from_prefix_with_elems(
            bytes,
            header.directed_edge_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        // Extended directed edges
        let directed_edge_ext_count = if header.has_ext_directed_edge() {
            header.directed_edge_count() as usize
        } else {
            0
        };
        let (ext_directed_edges, bytes) =
            <[DirectedEdgeExt]>::ref_from_prefix_with_elems(bytes, directed_edge_ext_count)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        // Access restrictions
        let (access_restrictions, bytes) = <[AccessRestriction]>::ref_from_prefix_with_elems(
            bytes,
            header.access_restriction_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        // Transit features
        let (transit_departures, bytes) = <[TransitDeparture]>::ref_from_prefix_with_elems(
            bytes,
            header.departure_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transit_stops, bytes) =
            <[TransitStop]>::ref_from_prefix_with_elems(bytes, header.stop_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transit_routes, bytes) =
            <[TransitRoute]>::ref_from_prefix_with_elems(bytes, header.route_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transit_schedules, bytes) = <[TransitSchedule]>::ref_from_prefix_with_elems(
            bytes,
            header.schedule_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transit_transfers, bytes) = <[TransitTransfer]>::ref_from_prefix_with_elems(
            bytes,
            header.transfer_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (signs, bytes) =
            <[Sign]>::ref_from_prefix_with_elems(bytes, header.sign_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (turn_lanes, bytes) =
            <[TurnLane]>::ref_from_prefix_with_elems(bytes, header.turn_lane_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (admins, bytes) =
            <[Admin]>::ref_from_prefix_with_elems(bytes, header.admin_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (edge_bins, bytes) =
            <[U64<LE>]>::ref_from_prefix_with_elems(bytes, header.edge_bins_size())
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let edge_bins = edge_bins
            .into_iter()
            .map(|it| GraphId::try_from_id(it.get()))
            .collect::<Result<Vec<_>, _>>()?;

        let (complex_forward_restrictions_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.complex_forward_restrictions_size())
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (complex_reverse_restrictions_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.complex_reverse_restrictions_size())
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (edge_info_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.edge_info_size())
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (text_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.text_list_size())
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (lane_connectivity_memory, bytes) =
            <[u8]>::ref_from_prefix_with_elems(bytes, header.lane_connectivity_size())
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (predicted_speeds, bytes) = if header.predicted_speeds_count() > 0 {
            // Curiously, these seem to actually be unaligned in a Valhalla tile I generated!
            let (offsets, profile_data) = <[U32<LE>]>::ref_from_prefix_with_elems(
                bytes,
                header.directed_edge_count() as usize,
            )
            .map_err(|e| GraphTileError::CastError(e.to_string()))?;

            let (profiles, bytes) = <[I16<LE>]>::ref_from_prefix_with_elems(
                profile_data,
                header.predicted_speeds_count() as usize * COEFFICIENT_COUNT,
            )
            .map_err(|e| GraphTileError::CastError(e.to_string()))?;

            (Some(PredictedSpeeds::new(offsets, profiles)), bytes)
        } else {
            (None, bytes)
        };

        // TODO: Transit info
        // - Stop one stops(?)
        // - Route one stops(?)
        // - Operator one stops(?)

        if bytes.is_empty() {
            Ok(Self {
                header,
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
            Err(GraphTileError::LeftoverBytesAfterReading(bytes.len()))
        }
    }
}

#[cfg(test)]
const TEST_GRAPH_TILE_ID_L0: GraphId = unsafe { GraphId::from_components_unchecked(0, 3015, 0) };
#[cfg(test)]
const TEST_GRAPH_TILE_ID_L2: GraphId = unsafe { GraphId::from_components_unchecked(2, 762485, 0) };

#[cfg(test)]
static TEST_GRAPH_TILE_L0: LazyLock<GraphTileHandle> = LazyLock::new(|| {
    let relative_path = TEST_GRAPH_TILE_ID_L0
        .file_path("gph")
        .expect("Unable to get relative path");
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-tiles")
        .join(relative_path);
    let bytes = std::fs::read(path).expect("Unable to read file");

    GraphTileHandle::try_from(bytes).expect("Unable to get tile")
});

#[cfg(test)]
static TEST_GRAPH_TILE_L2: LazyLock<GraphTileHandle> = LazyLock::new(|| {
    let relative_path = TEST_GRAPH_TILE_ID_L2
        .file_path("gph")
        .expect("Unable to get relative path");
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-tiles")
        .join(relative_path);
    let bytes = std::fs::read(path).expect("Unable to read file");

    GraphTileHandle::try_from(bytes).expect("Unable to get tile")
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
static TEST_GRAPH_TILE_WITH_FLOW: LazyLock<GraphTileHandle> = LazyLock::new(|| {
    let relative_path = TEST_GRAPH_TILE_ID_L0
        .file_path("gph")
        .expect("Unable to get relative path");
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-tiles-with-traffic")
        .join(relative_path);
    let bytes = std::fs::read(path).expect("Unable to read file");

    GraphTileHandle::try_from(bytes).expect("Unable to get tile")
});

#[cfg(test)]
mod tests {
    use crate::Access;
    use crate::graph_tile::predicted_speeds::BUCKETS_PER_WEEK;
    use crate::graph_tile::{
        GraphTile, TEST_GRAPH_TILE_ID_L0, TEST_GRAPH_TILE_L0, TEST_GRAPH_TILE_L2,
        TEST_GRAPH_TILE_WITH_FLOW,
    };
    use enumset::{EnumSet, enum_set};

    #[test]
    fn test_get_opp_edge_index() {
        let tile = &*TEST_GRAPH_TILE_L0;

        let edges: Vec<_> = (0..u64::from(tile.header().directed_edge_count()))
            .map(|index| {
                let edge_id = TEST_GRAPH_TILE_ID_L0
                    .with_index(index)
                    .expect("Invalid graph ID.");
                let opp_edge_index = tile
                    .get_opp_edge_index(edge_id)
                    .expect("Unable to get opp edge index.");
                opp_edge_index
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
    fn test_edge_info() {
        let tile = &*TEST_GRAPH_TILE_L0;

        let first_edge_info = tile
            .get_edge_info(&tile.directed_edges().first().unwrap())
            .expect("Unable to get edge info.");

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!("first_edge_info", first_edge_info);
            insta::assert_debug_snapshot!("first_edge_info_decoded_shape", first_edge_info.shape());
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
}
