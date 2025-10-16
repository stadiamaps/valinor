use thiserror::Error;
use zerocopy::{FromBytes, LE, U64, transmute};

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
    ValidityError,
    #[error("Invalid graph ID.")]
    GraphIdParseError(#[from] InvalidGraphIdError),
    #[error("Data cast failed (this almost always means invalid data): {0}")]
    CastError(String),
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
    /// An owned graph tile.
    ///
    /// An owned graph tile can be constructed from an owned byte array, `Vec<u8>`.
    pub struct OwnedGraphTile {
        owner: Vec<u8>,
        #[covariant]
        dependent: GraphTileView,
    }
}

impl GraphTile for OwnedGraphTile {
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

impl TryFrom<Vec<u8>> for OwnedGraphTile {
    type Error = GraphTileError;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        OwnedGraphTile::try_new(value, |data| GraphTileView::try_from(data.as_ref()))
    }
}

/// An internal view over a single tile in the Valhalla hierarchical tile graph.
///
/// Access should normally go through the [``GraphTile``](GraphTile) trait.
struct GraphTileView<'a> {
    memory: &'a [u8],
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
    edge_bins: GraphId,
    // TODO: Complex forward restrictions
    // TODO: Complex reverse restrictions
    // TODO: Street names (names here)
    // TODO: Lane connectivity
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
        let edge_info_start = self.header.edge_info_offset.get() as usize;
        let edge_info_offset = directed_edge.edge_info_offset() as usize;

        // TODO: Text slice as a separate property or a function?
        let text_start = self.header.text_list_offset.get() as usize;
        let text_size = self.header.lane_connectivity_offset.get() as usize - text_start;

        EdgeInfo::try_from((
            &self.memory[edge_info_start + edge_info_offset..],
            &self.memory[text_start..text_start + text_size],
        ))
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

// TODO: Feels like this could be a macro
impl<'a> TryFrom<&'a [u8]> for GraphTileView<'a> {
    type Error = GraphTileError;

    fn try_from(bytes: &'a [u8]) -> Result<Self, Self::Error> {
        const U64_SIZE: usize = size_of::<u64>();
        // Get the byte range of the header so we can transmute it
        const HEADER_SIZE: usize = size_of::<GraphTileHeader>();

        // Immutable reference to the slice which we'll keep re-binding as we go,
        // consuming the DSTs as we go.
        let buffer = bytes;
        let header_range = 0..HEADER_SIZE;

        // Header
        let header_slice: [u8; HEADER_SIZE] = buffer[header_range].try_into()?;
        let header: GraphTileHeader = transmute!(header_slice);

        // All the variably sized data arrays...
        // The basic pattern here is to use ref_from_prefix_with_elems to consume a known number of elements
        // from the byte slice, returning a reference to the tail.
        // In this way, we don't need to track manual offsets; we just consume the known number of elements
        // sequentially.

        let (nodes, buffer) = <[NodeInfo]>::ref_from_prefix_with_elems(
            &buffer[HEADER_SIZE..],
            header.node_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transitions, buffer) = <[NodeTransition]>::ref_from_prefix_with_elems(
            buffer,
            header.transition_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (directed_edges, buffer) = <[DirectedEdge]>::ref_from_prefix_with_elems(
            buffer,
            header.directed_edge_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let directed_edge_ext_count = if header.has_ext_directed_edge() {
            header.directed_edge_count() as usize
        } else {
            0
        };
        let (ext_directed_edges, buffer) =
            <[DirectedEdgeExt]>::ref_from_prefix_with_elems(buffer, directed_edge_ext_count)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (access_restrictions, buffer) = <[AccessRestriction]>::ref_from_prefix_with_elems(
            buffer,
            header.access_restriction_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (transit_departures, buffer) = <[TransitDeparture]>::ref_from_prefix_with_elems(
            buffer,
            header.departure_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transit_stops, buffer) =
            <[TransitStop]>::ref_from_prefix_with_elems(buffer, header.stop_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transit_routes, buffer) =
            <[TransitRoute]>::ref_from_prefix_with_elems(buffer, header.route_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transit_schedules, buffer) = <[TransitSchedule]>::ref_from_prefix_with_elems(
            buffer,
            header.schedule_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;
        let (transit_transfers, buffer) = <[TransitTransfer]>::ref_from_prefix_with_elems(
            buffer,
            header.transfer_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (signs, buffer) =
            <[Sign]>::ref_from_prefix_with_elems(buffer, header.sign_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (turn_lanes, buffer) =
            <[TurnLane]>::ref_from_prefix_with_elems(buffer, header.turn_lane_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let (admins, buffer) =
            <[Admin]>::ref_from_prefix_with_elems(buffer, header.admin_count() as usize)
                .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let slice: [u8; U64_SIZE] = (&buffer[0..U64_SIZE]).try_into()?;
        let raw_graph_id: U64<LE> = transmute!(slice);
        let edge_bins = GraphId::try_from_id(raw_graph_id.get())?;

        // TODO: Complex forward restrictions
        // TODO: Complex reverse restrictions
        // TODO: Street names (names here)
        // TODO: Lane connectivity

        let predicted_speeds = if header.predicted_speeds_count() > 0 {
            let predicted_speed_offset = header.predicted_speeds_offset.get() as usize;
            let (offsets, profile_data) = <[u32]>::ref_from_prefix_with_elems(
                &bytes[predicted_speed_offset..],
                header.directed_edge_count() as usize,
            )
            .map_err(|e| GraphTileError::CastError(e.to_string()))?;

            let (profiles, _) = <[i16]>::ref_from_prefix_with_elems(
                profile_data,
                header.predicted_speeds_count() as usize * COEFFICIENT_COUNT,
            )
            .map_err(|e| GraphTileError::CastError(e.to_string()))?;

            Some(PredictedSpeeds::new(offsets, profiles))
        } else {
            None
        };

        // TODO: Stop one stops(?)
        // TODO: Route one stops(?)
        // TODO: Operator one stops(?)

        Ok(Self {
            memory: bytes,
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
            predicted_speeds,
        })
    }
}

#[cfg(test)]
const TEST_GRAPH_TILE_ID: GraphId = unsafe { GraphId::from_components_unchecked(0, 3015, 0) };

#[cfg(test)]
static TEST_GRAPH_TILE: LazyLock<OwnedGraphTile> = LazyLock::new(|| {
    let relative_path = TEST_GRAPH_TILE_ID
        .file_path("gph")
        .expect("Unable to get relative path");
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-tiles")
        .join(relative_path);
    let bytes = std::fs::read(path).expect("Unable to read file");

    OwnedGraphTile::try_from(bytes).expect("Unable to get tile")
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
static TEST_GRAPH_TILE_WITH_FLOW: LazyLock<OwnedGraphTile> = LazyLock::new(|| {
    let relative_path = TEST_GRAPH_TILE_ID
        .file_path("gph")
        .expect("Unable to get relative path");
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("andorra-tiles-with-traffic")
        .join(relative_path);
    let bytes = std::fs::read(path).expect("Unable to read file");

    OwnedGraphTile::try_from(bytes).expect("Unable to get tile")
});

#[cfg(test)]
mod tests {
    use crate::Access;
    use crate::graph_tile::predicted_speeds::BUCKETS_PER_WEEK;
    use crate::graph_tile::{
        GraphTile, TEST_GRAPH_TILE, TEST_GRAPH_TILE_ID, TEST_GRAPH_TILE_WITH_FLOW,
    };
    use enumset::{EnumSet, enum_set};

    #[test]
    fn test_get_opp_edge_index() {
        let tile = &*TEST_GRAPH_TILE;

        let edges: Vec<_> = (0..u64::from(tile.header().directed_edge_count()))
            .map(|index| {
                let edge_id = TEST_GRAPH_TILE_ID
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
        let tile = &*TEST_GRAPH_TILE;

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
        // TODO: TBH I don't actually understand how this is a valid graph tile. Clearly some black bit magic.
        let tile = &*TEST_GRAPH_TILE;
        let tile_view = tile.borrow_dependent();

        assert_eq!(tile_view.edge_bins.level(), 0);
        assert_eq!(tile_view.edge_bins.tile_id(), 0);
        assert_eq!(tile_view.edge_bins.index(), 32000);
    }

    #[test]
    fn test_edge_info() {
        let tile = &*TEST_GRAPH_TILE;

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
        let tile = &*TEST_GRAPH_TILE;
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

        // A few predicted speed samples.
        // See predicted_speeds.rs for the array of speeds that we expected to encode.
        let speeds: [i64; BUCKETS_PER_WEEK] = std::array::from_fn(|i| {
            tile_view
                .get_predicted_speed(EDGE_INDEX, (i as u32) * 300)
                .unwrap() as i64
        });

        insta::assert_yaml_snapshot!(speeds.to_vec());
    }
}
