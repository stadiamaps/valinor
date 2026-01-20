use super::{
    AccessRestriction, Admin, DirectedEdge, DirectedEdgeExt, GraphTileBuildError, GraphTileHeader,
    GraphTileView, NodeInfo, NodeTransition, OwnedGraphTileHandle, Sign, TransitDeparture,
    TransitRoute, TransitSchedule, TransitStop, TransitTransfer, TurnLane,
};
use crate::GraphId;
use crate::graph_tile::header::{GraphTileHeaderBuilder, VERSION_LEN};
use crate::graph_tile::predicted_speeds::{
    BUCKETS_PER_WEEK, COEFFICIENT_COUNT, compress_speed_buckets, decode_base64_speed_coefficients,
};
use chrono::{DateTime, Utc};
use geo::Coord;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::borrow::Cow;
use std::collections::HashMap;
use zerocopy::{I16, Immutable, IntoBytes, LE, U32};

/// The writer version.
///
/// Historically this meant the version of baldr/mjolnir and was stored as a simple semver string,
/// but this is a bit fuzzy now that there are multiple writer implementations ;)
const DEFAULT_WRITER_VERSION: [u8; VERSION_LEN] = {
    const VERSION: &str = env!("CARGO_PKG_VERSION");
    const BYTES: [&[u8]; 2] = ["valinor-".as_bytes(), VERSION.as_bytes()];

    let mut out = [0u8; 16];
    let mut i = 0;
    let mut l = 0;
    while l < BYTES.len() {
        let mut c = 0;
        while c < BYTES[l].len() {
            out[i] = BYTES[l][c];
            i += 1;
            c += 1;
        }
        l += 1;
    }
    out
};

fn writer_version_to_bytes(version: &str) -> Option<[u8; 16]> {
    let bytes = version.as_bytes();
    if bytes.len() <= 16 {
        let mut out = [0u8; 16];
        out[..bytes.len()].copy_from_slice(bytes);
        Some(out)
    } else {
        None
    }
}

/// A builder for constructing new / modified graph tiles.
///
/// # Design principles
///
/// We made some conscious design choices when building this.
/// Here is a brief discussion of these and their rationale for posterity.
///
/// ## Use of copy-on-write internal fields
///
/// One of the more common usage patterns is to construct the builder
/// from an existing graph tile handle.
/// To avoid needless copying (especially when the edits are localized to a small section of the tile),
/// we lazily copy as needed.
///
/// ## Late materialization of derived structures
///
/// Things like headers are not computed every time.
/// Rather, we keep enough information around to derive what the header fields should be.
pub struct GraphTileBuilder<'a> {
    writer_version: [u8; VERSION_LEN],
    graph_id: GraphId,
    dataset_id: u64,
    sw_corner: Coord<f32>,
    create_date: DateTime<Utc>,
    // TODO: Remove this eventually. Currently referenced for a few properties like binning which we don't edit yet anyways.
    remove_me_header: GraphTileHeader,
    nodes: Cow<'a, [NodeInfo]>,
    transitions: Cow<'a, [NodeTransition]>,
    directed_edges: Cow<'a, [DirectedEdge]>,
    ext_directed_edges: Cow<'a, [DirectedEdgeExt]>,
    access_restrictions: Cow<'a, [AccessRestriction]>,
    transit_departures: Cow<'a, [TransitDeparture]>,
    transit_stops: Cow<'a, [TransitStop]>,
    transit_routes: Cow<'a, [TransitRoute]>,
    transit_schedules: Cow<'a, [TransitSchedule]>,
    transit_transfers: Cow<'a, [TransitTransfer]>,
    signs: Cow<'a, [Sign]>,
    turn_lanes: Cow<'a, [TurnLane]>,
    admins: Cow<'a, [Admin]>,
    edge_bins: Cow<'a, [GraphId]>,
    complex_forward_restrictions_memory: Cow<'a, [u8]>,
    complex_reverse_restrictions_memory: Cow<'a, [u8]>,
    edge_info_memory: Cow<'a, [u8]>,
    text_memory: Cow<'a, [u8]>,
    lane_connectivity_memory: Cow<'a, [u8]>,
    predicted_speed_offsets: Cow<'a, [U32<LE>]>,
    /// Raw profile memory (`n_profiles x COEFFICIENT_COUNT` entries back to back)
    predicted_speed_profile_memory: Cow<'a, [I16<LE>]>,
    /// Lazily initialized map for deduplicating speed profiles.
    /// None = not yet initialized; Some = ready for use.
    speed_profile_dedup: Option<HashMap<[i16; COEFFICIENT_COUNT], u32>>,
}

/// Builds a deduplication map from predicted speed profile memory.
///
/// Scans the flat profile memory (semantically a 2D array with fixed-width rows)
/// and creates a HashMap mapping each unique profile to its offset.
/// If duplicate profiles exist in the input, only the first occurrence is retained.
fn build_speed_profile_dedup_map(memory: &[I16<LE>]) -> HashMap<[i16; COEFFICIENT_COUNT], u32> {
    let mut map = HashMap::new();

    for (chunk_idx, chunk) in memory.chunks_exact(COEFFICIENT_COUNT).enumerate() {
        let offset = (chunk_idx * COEFFICIENT_COUNT) as u32;

        // Convert the chunk to a native array for HashMap key
        let mut profile = [0i16; COEFFICIENT_COUNT];
        for (i, v) in chunk.iter().enumerate() {
            profile[i] = v.get();
        }

        // Only insert if this profile hasn't been seen before
        map.entry(profile).or_insert(offset);
    }

    map
}

impl<'a> From<&'a OwnedGraphTileHandle> for GraphTileBuilder<'a> {
    fn from(value: &'a OwnedGraphTileHandle) -> Self {
        let GraphTileView {
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
        } = value.borrow_dependent();

        let (predicted_speed_offsets, predicted_speed_profile_memory) = match predicted_speeds {
            Some(ps) => {
                let (offsets, profiles) = ps.as_offsets_and_profiles();
                (Cow::Borrowed(offsets), Cow::Borrowed(profiles))
            }
            None => Default::default(),
        };

        GraphTileBuilder {
            writer_version: header.version,
            graph_id: header.graph_id(),
            dataset_id: header.dataset_id.get(),
            sw_corner: header.sw_corner(),
            create_date: header.create_date(),
            remove_me_header: (*header).clone(),
            nodes: Cow::Borrowed(nodes),
            transitions: Cow::Borrowed(transitions),
            directed_edges: Cow::Borrowed(directed_edges),
            ext_directed_edges: Cow::Borrowed(ext_directed_edges),
            access_restrictions: Cow::Borrowed(access_restrictions),
            transit_departures: Cow::Borrowed(transit_departures),
            transit_stops: Cow::Borrowed(transit_stops),
            transit_routes: Cow::Borrowed(transit_routes),
            transit_schedules: Cow::Borrowed(transit_schedules),
            transit_transfers: Cow::Borrowed(transit_transfers),
            signs: Cow::Borrowed(signs),
            turn_lanes: Cow::Borrowed(turn_lanes),
            admins: Cow::Borrowed(admins),
            edge_bins: Cow::Borrowed(edge_bins),
            complex_forward_restrictions_memory: Cow::Borrowed(complex_forward_restrictions_memory),
            complex_reverse_restrictions_memory: Cow::Borrowed(complex_reverse_restrictions_memory),
            edge_info_memory: Cow::Borrowed(edge_info_memory),
            text_memory: Cow::Borrowed(text_memory),
            lane_connectivity_memory: Cow::Borrowed(lane_connectivity_memory),
            predicted_speed_offsets,
            predicted_speed_profile_memory,
            speed_profile_dedup: None,
        }
    }
}

impl GraphTileBuilder<'_> {
    /// The Graph ID for the tile.
    ///
    /// This is guaranteed to always be a base ID.
    pub fn graph_id(&self) -> GraphId {
        self.graph_id
    }

    /// Sets the version string to encode in the graph tile.
    ///
    /// This is purely metadata and is not used by Valhalla to determine compatibility.
    ///
    /// # Errors
    ///
    /// The string must be <= 16 bytes when encoded as UTF-8.
    /// If it is longer, this will return an error.
    pub fn with_version(self, version: &str) -> Result<Self, GraphTileBuildError> {
        let writer_version = writer_version_to_bytes(version)
            .ok_or_else(|| GraphTileBuildError::InvalidVersionString(version.to_string()))?;

        Ok(Self {
            writer_version,
            ..self
        })
    }

    /// Adds historical average (coarse granularity) speed information to a directed edge.
    ///
    /// Zero indicates that no data is available.
    ///
    /// # Errors
    ///
    /// Fails if the directed edge index is out of bounds.
    pub fn with_average_speeds(
        self,
        directed_edge_index: usize,
        free_flow_speed: u8,
        constrained_speed: u8,
    ) -> Result<Self, GraphTileBuildError> {
        let mut result = self;
        if directed_edge_index >= result.directed_edges.len() {
            return Err(GraphTileBuildError::InvalidIndex(format!(
                "Attempted to set historical average speeds for directed edge index {directed_edge_index}, but tile only has {} edges",
                result.directed_edges.len()
            )));
        }

        let edge = &mut result.directed_edges.to_mut()[directed_edge_index];
        edge.set_free_flow_speed(free_flow_speed);
        edge.set_constrained_speed(constrained_speed);

        Ok(result)
    }

    /// Adds predicted speeds to a directed edge using pre-encoded DCT-II coefficients.
    ///
    /// This method is probably the least ergonomic in the family of predicted speed APIs,
    /// but it's also the most efficient (if you can use it directly)
    /// since it doesn't need to do any format shifting.
    /// All other predicted speed methods are convenience wrappers around this.
    ///
    /// See the [`crate::graph_tile::predicted_speeds`] module for more details
    /// on predicted speeds.
    ///
    /// # Errors
    ///
    /// Fails if the directed edge index is invalid,
    /// or you somehow managed to add more than 2 billion speed profiles to a single tile.
    pub fn with_predicted_speed_coefficients(
        self,
        directed_edge_index: usize,
        coefficients: &[i16; COEFFICIENT_COUNT],
    ) -> Result<Self, GraphTileBuildError> {
        let mut result = self.grow_predicted_speeds_if_needed(true);
        if directed_edge_index >= result.directed_edges.len() {
            return Err(GraphTileBuildError::InvalidIndex(format!(
                "Attempted to set predicted speeds for directed edge index {directed_edge_index}, but tile only has {} edges",
                result.directed_edges.len()
            )));
        }

        // Set the flag indicating that we have predicted speeds for this edge.
        let edge = &mut result.directed_edges.to_mut()[directed_edge_index];
        edge.set_has_predicted_speed(true);

        // Lazy initialization: populate the dedup map from existing profiles if needed
        let dedup_map = result.speed_profile_dedup.get_or_insert_with(|| {
            build_speed_profile_dedup_map(&result.predicted_speed_profile_memory)
        });
        let offset = if let Some(&existing_offset) = dedup_map.get(coefficients) {
            // Profile already exists; reuse the existing offset
            existing_offset
        } else {
            // New profile; append it to the memory and record the offset
            let new_offset = u32::try_from(result.predicted_speed_profile_memory.len())?;

            let predicted_speed_profiles = result.predicted_speed_profile_memory.to_mut();
            predicted_speed_profiles
                .extend::<[I16<LE>; COEFFICIENT_COUNT]>(coefficients.map(Into::into));

            dedup_map.insert(*coefficients, new_offset);
            new_offset
        };

        // Set the offset for this directed edge
        let predicted_speed_offsets = result.predicted_speed_offsets.to_mut();
        predicted_speed_offsets[directed_edge_index] = offset.into();

        Ok(result)
    }

    /// Adds predicted speeds to a directed edge from a base64 encoded string
    /// containing the DCT-II coefficients.
    ///
    /// This is slightly less efficient than directly setting the coefficients using
    /// [`with_predicted_speed_coefficients`](GraphTileBuilder::with_predicted_speed_coefficients),
    /// but if you're working with text files or some other situation where you'd prefer not to use binary data,
    /// base64 encoding is a happy middle ground.
    ///
    /// See the [`crate::graph_tile::predicted_speeds`] module for more details
    /// on predicted speeds.
    ///
    /// # Errors
    ///
    /// This will fail if the directed edge index is out of bounds,
    /// the compressed speeds string doesn't decode to exactly 400 bytes,
    /// or you somehow managed to add more than 2 billion speed profiles to a single tile.
    pub fn with_predicted_encoded_speeds(
        self,
        directed_edge_index: usize,
        compressed_speeds: &str,
    ) -> Result<Self, GraphTileBuildError> {
        self.with_predicted_speed_coefficients(
            directed_edge_index,
            &decode_base64_speed_coefficients(compressed_speeds)?,
        )
    }

    /// Adds predicted speeds to a directed edge from a list of samples
    /// representing evenly spaced intervals throughout a week.
    ///
    /// See the [`crate::graph_tile::predicted_speeds`] module for more details
    /// on predicted speeds.
    ///
    /// # Errors
    ///
    /// Fails if the directed edge index is invalid,
    /// or you somehow managed to add more than 2 billion speed profiles to a single tile.
    pub fn with_predicted_speeds(
        self,
        directed_edge_index: usize,
        speeds: &[f32; BUCKETS_PER_WEEK],
    ) -> Result<Self, GraphTileBuildError> {
        self.with_predicted_speed_coefficients(directed_edge_index, &compress_speed_buckets(speeds))
    }

    fn grow_predicted_speeds_if_needed(self, force_create_offsets_array: bool) -> Self {
        assert!(
            self.predicted_speed_offsets.len() <= self.directed_edges.len(),
            "There are currently more predicted speeds than directed edges. That's not supposed to happen!"
        );

        // Don't need to grow unless there are actually speed profiles
        if !force_create_offsets_array
            && self.predicted_speed_offsets.is_empty()
            && self.predicted_speed_profile_memory.is_empty()
        {
            return self;
        }

        let mut result = self;
        if result.predicted_speed_offsets.len() != result.directed_edges.len() {
            let predicted_speed_offsets = result.predicted_speed_offsets.to_mut();
            let delta = result.directed_edges.len() - predicted_speed_offsets.len();

            predicted_speed_offsets.extend(std::iter::repeat_n(U32::<LE>::from(0), delta));
        }

        result
    }

    /// Yields the raw bytes of a full tile in the order they should be stored on disk.
    ///
    /// This API is produces each section of the file
    /// (e.g. nodes, directed edges, names, etc.) lazily as requested.
    /// Thus, the most memory it will need at one time is bounded
    /// by the size of the largest section.
    ///
    /// # Errors
    ///
    /// Fails if anything is amiss in the tile.
    /// This should be pretty uncommon, but the following kinds of situations could theoretically
    /// trigger an error:
    ///
    /// * Including than the allowed number of some feature type (e.g. more than 2^24 access restrictions)
    /// * Managing to create a single tile larger than 4 gigabytes
    /// * Setting a creation date more than 11,758,979.59 years after January 1, 2014
    ///
    /// TL;DR, things that you really shouldn't do, or are a clear programming error.
    ///
    /// # Panics
    ///
    /// This function includes several assertions.
    /// These do _not_ introduce noticeable runtime overhead
    /// and should not trigger during regular operation.
    /// The assertions exist to verify invariants of the generated tile.
    ///
    /// If you hit any of these, it is a bug in Valinor, not your code.
    pub fn into_byte_iter(self) -> Result<impl Iterator<Item = Box<[u8]>>, GraphTileBuildError> {
        // Validate and finalize predicted speeds arrays (sizes and counts)
        let intermediate = self.grow_predicted_speeds_if_needed(false);
        if intermediate.predicted_speed_profile_memory.is_empty() {
            assert!(
                intermediate.predicted_speed_offsets.is_empty(),
                "Expected an empty offset array as there are no speed profiles"
            );
        } else {
            assert_eq!(
                intermediate.predicted_speed_offsets.len(),
                intermediate.directed_edges.len(),
                "Expected to have one predicted speed offset per directed edge"
            );
            assert!(
                intermediate
                    .predicted_speed_profile_memory
                    .len()
                    .is_multiple_of(COEFFICIENT_COUNT),
                "Expected the speed profile memory size to be some multiple of {COEFFICIENT_COUNT} (this is a bug in the builder)."
            );
        }

        // Build the header from the finalized state, then own the header bytes.
        let header = GraphTileHeaderBuilder {
            version: intermediate.writer_version,
            graph_id: intermediate.graph_id,
            density: intermediate.remove_me_header.density(),
            has_elevation: intermediate.remove_me_header.has_elevation(),
            has_ext_directed_edges: !intermediate.ext_directed_edges.is_empty(),
            sw_corner: intermediate.sw_corner,
            dataset_id: intermediate.dataset_id,
            node_count: intermediate.nodes.len(),
            directed_edge_count: intermediate.directed_edges.len(),
            predicted_speed_profile_count: intermediate.predicted_speed_profile_memory.len()
                / COEFFICIENT_COUNT,
            transition_count: intermediate.transitions.len(),
            turn_lane_count: intermediate.turn_lanes.len(),
            transfer_count: intermediate.transit_transfers.len(),
            departure_count: intermediate.transit_departures.len(),
            stop_count: intermediate.transit_stops.len(),
            route_count: intermediate.transit_routes.len(),
            schedule_count: intermediate.transit_schedules.len(),
            sign_count: intermediate.signs.len(),
            access_restriction_count: intermediate.access_restrictions.len(),
            admin_count: intermediate.admins.len(),
            create_date: intermediate.create_date,
            bin_offsets: intermediate.remove_me_header.bin_offsets.map(Into::into),
            complex_forward_restrictions_size: intermediate
                .complex_forward_restrictions_memory
                .len(),
            complex_reverse_restrictions_size: intermediate
                .complex_reverse_restrictions_memory
                .len(),
            edge_info_size: intermediate.edge_info_memory.len(),
            text_list_size: intermediate.text_memory.len(),
            lane_connectivity_size: intermediate.lane_connectivity_memory.len(),
        };
        // Meh extra alloc...
        let header_bytes = header.build()?.as_bytes().to_vec();

        Ok(TileByteIter {
            header: header_bytes,
            stage: TileBuildStage::Header,
            nodes: intermediate.nodes,
            transitions: intermediate.transitions,
            directed_edges: intermediate.directed_edges,
            ext_directed_edges: intermediate.ext_directed_edges,
            access_restrictions: intermediate.access_restrictions,
            transit_departures: intermediate.transit_departures,
            transit_stops: intermediate.transit_stops,
            transit_routes: intermediate.transit_routes,
            transit_schedules: intermediate.transit_schedules,
            transit_transfers: intermediate.transit_transfers,
            signs: intermediate.signs,
            turn_lanes: intermediate.turn_lanes,
            admins: intermediate.admins,
            edge_bins: intermediate.edge_bins,
            complex_forward_restrictions_memory: intermediate.complex_forward_restrictions_memory,
            complex_reverse_restrictions_memory: intermediate.complex_reverse_restrictions_memory,
            edge_info_memory: intermediate.edge_info_memory,
            text_memory: intermediate.text_memory,
            lane_connectivity_memory: intermediate.lane_connectivity_memory,
            predicted_speed_offsets: intermediate.predicted_speed_offsets,
            predicted_speed_profile_memory: intermediate.predicted_speed_profile_memory,
        })
    }

    /// Serializes the tile as owned bytes.
    ///
    /// NOTE: This allocates somewhere on the order of 2x the final tile size
    /// while building the tile.
    /// Use other build methods if you need to conserve RAM.
    ///
    /// # Errors
    ///
    /// Refer to the documentation for [`GraphTileBuilder::into_byte_iter`] for error conditions.
    pub fn into_bytes(self) -> Result<Vec<u8>, GraphTileBuildError> {
        Ok(self.into_byte_iter()?.flatten().collect())
    }
}

/// An iterator that lazily produces a full graph tile without too many extra allocations.
///
/// Specifically, while this iterator is not zero-cost,
/// it will only allocate one section (e.g., nodes, directed edges, etc.)
/// at a time.
///
/// This dramatically reduces the peak memory usage when serializing a tile directly
/// to an output stream (file, network, etc.).
struct TileByteIter<'a> {
    header: Vec<u8>,

    /// The current stage of production.
    stage: TileBuildStage,

    // Body sections (matching into_bytes order)
    nodes: Cow<'a, [NodeInfo]>,
    transitions: Cow<'a, [NodeTransition]>,
    directed_edges: Cow<'a, [DirectedEdge]>,
    ext_directed_edges: Cow<'a, [DirectedEdgeExt]>,
    access_restrictions: Cow<'a, [AccessRestriction]>,
    transit_departures: Cow<'a, [TransitDeparture]>,
    transit_stops: Cow<'a, [TransitStop]>,
    transit_routes: Cow<'a, [TransitRoute]>,
    transit_schedules: Cow<'a, [TransitSchedule]>,
    transit_transfers: Cow<'a, [TransitTransfer]>,
    signs: Cow<'a, [Sign]>,
    turn_lanes: Cow<'a, [TurnLane]>,
    admins: Cow<'a, [Admin]>,
    edge_bins: Cow<'a, [GraphId]>,
    complex_forward_restrictions_memory: Cow<'a, [u8]>,
    complex_reverse_restrictions_memory: Cow<'a, [u8]>,
    edge_info_memory: Cow<'a, [u8]>,
    text_memory: Cow<'a, [u8]>,
    lane_connectivity_memory: Cow<'a, [u8]>,
    predicted_speed_offsets: Cow<'a, [U32<LE>]>,
    predicted_speed_profile_memory: Cow<'a, [I16<LE>]>,
}

/// The stage of the tile production.
///
/// Stages are rendered in the order specified below
/// (variant order matters!!).
#[derive(Copy, Clone, Debug, IntoPrimitive, TryFromPrimitive)]
#[repr(u8)]
enum TileBuildStage {
    Header,
    Nodes,
    Transitions,
    DirectedEdges,
    ExtDirectedEdges,
    AccessRestrictions,
    TransitDepartures,
    TransitStops,
    TransitRoutes,
    TransitSchedules,
    TransitTransfers,
    Signs,
    TurnLanes,
    Admins,
    EdgeBins,
    ComplexForwardRestrictions,
    ComplexReverseRestrictions,
    EdgeInfo,
    TextMemory,
    LaneConnectivity,
    PredictedSpeedOffsets,
    PredictedSpeedProfiles,
    Done,
}

impl TileBuildStage {
    fn next(self) -> TileBuildStage {
        let current: u8 = self.into();

        TileBuildStage::try_from(current + 1).unwrap_or(TileBuildStage::Done)
    }
}

impl Iterator for TileByteIter<'_> {
    type Item = Box<[u8]>;

    fn next(&mut self) -> Option<Self::Item> {
        let bytes = match self.stage {
            TileBuildStage::Header => std::mem::take(&mut self.header).into_boxed_slice(),
            TileBuildStage::Nodes => bytes_from_items(std::mem::take(&mut self.nodes)),
            TileBuildStage::Transitions => bytes_from_items(std::mem::take(&mut self.transitions)),
            TileBuildStage::DirectedEdges => {
                bytes_from_items(std::mem::take(&mut self.directed_edges))
            }
            TileBuildStage::ExtDirectedEdges => {
                bytes_from_items(std::mem::take(&mut self.ext_directed_edges))
            }
            TileBuildStage::AccessRestrictions => {
                bytes_from_items(std::mem::take(&mut self.access_restrictions))
            }
            TileBuildStage::TransitDepartures => {
                bytes_from_items(std::mem::take(&mut self.transit_departures))
            }
            TileBuildStage::TransitStops => {
                bytes_from_items(std::mem::take(&mut self.transit_stops))
            }
            TileBuildStage::TransitRoutes => {
                bytes_from_items(std::mem::take(&mut self.transit_routes))
            }
            TileBuildStage::TransitSchedules => {
                bytes_from_items(std::mem::take(&mut self.transit_schedules))
            }
            TileBuildStage::TransitTransfers => {
                bytes_from_items(std::mem::take(&mut self.transit_transfers))
            }
            TileBuildStage::Signs => bytes_from_items(std::mem::take(&mut self.signs)),
            TileBuildStage::TurnLanes => bytes_from_items(std::mem::take(&mut self.turn_lanes)),
            TileBuildStage::Admins => bytes_from_items(std::mem::take(&mut self.admins)),
            TileBuildStage::EdgeBins => bytes_from_items(std::mem::take(&mut self.edge_bins)),
            TileBuildStage::ComplexForwardRestrictions => bytes_from_items(std::mem::take(
                &mut self.complex_forward_restrictions_memory,
            )),
            TileBuildStage::ComplexReverseRestrictions => bytes_from_items(std::mem::take(
                &mut self.complex_reverse_restrictions_memory,
            )),
            TileBuildStage::EdgeInfo => {
                bytes_from_items(std::mem::take(&mut self.edge_info_memory))
            }
            TileBuildStage::TextMemory => bytes_from_items(std::mem::take(&mut self.text_memory)),
            TileBuildStage::LaneConnectivity => {
                bytes_from_items(std::mem::take(&mut self.lane_connectivity_memory))
            }
            TileBuildStage::PredictedSpeedOffsets => {
                bytes_from_items(std::mem::take(&mut self.predicted_speed_offsets))
            }
            TileBuildStage::PredictedSpeedProfiles => {
                bytes_from_items(std::mem::take(&mut self.predicted_speed_profile_memory))
            }
            TileBuildStage::Done => {
                // No more sections
                return None;
            }
        };

        self.stage = self.stage.next();
        Some(bytes)
    }
}

fn bytes_from_items<T: IntoBytes + Immutable>(items: Cow<'_, [T]>) -> Box<[u8]>
where
    [T]: ToOwned,
{
    let items = items.as_ref();
    // Reserve an estimated capacity to minimize reallocations
    let mut buf = Vec::with_capacity(size_of_val(items));
    for v in items {
        buf.extend(v.as_bytes());
    }

    buf.into_boxed_slice()
}

#[cfg(test)]
mod tests {
    use crate::graph_tile::predicted_speeds::COEFFICIENT_COUNT;
    use crate::graph_tile::{GraphTileBuilder, GraphTileHeader, OwnedGraphTileHandle};
    use std::path::Path;
    use walkdir::WalkDir;

    fn assert_round_trip_unmodified_equals_original(path: &Path) {
        const HEADER_SIZE: usize = size_of::<GraphTileHeader>();

        let in_bytes = std::fs::read(path).expect("Unable to read file");
        let tile_handle =
            OwnedGraphTileHandle::try_from(in_bytes.clone()).expect("Unable to get tile handle");

        let builder = GraphTileBuilder::from(&tile_handle);
        let out_bytes = builder.into_bytes().expect("Unable to serialize tile");

        let in_header_slice: [u8; HEADER_SIZE] = in_bytes[0..HEADER_SIZE]
            .try_into()
            .expect("oops; couldn't parse header?");
        let in_header: GraphTileHeader = zerocopy::transmute!(in_header_slice);

        let out_header_slice: [u8; HEADER_SIZE] = out_bytes[0..HEADER_SIZE]
            .try_into()
            .expect("oops; couldn't parse header?");
        let out_header: GraphTileHeader = zerocopy::transmute!(out_header_slice);

        assert_eq!(
            in_header, out_header,
            "Failed round-trip builder test (header) for fixture at {:?}",
            path
        );

        assert_eq!(
            in_header_slice, out_header_slice,
            "Failed round-trip builder test (header; slice) for fixture at {:?}",
            path
        );

        assert_eq!(
            in_bytes, out_bytes,
            "Failed round-trip builder test (whole tile) for fixture at {:?}",
            path
        );
    }

    #[test]
    fn round_trip_from_builder_without_changes() {
        let base_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        for entry in WalkDir::new(base_dir) {
            let entry = entry.expect("Unable to traverse directory");

            if entry.file_type().is_file()
                && entry
                    .path()
                    .extension()
                    .is_some_and(|ext| ext.eq_ignore_ascii_case("gph"))
            {
                assert_round_trip_unmodified_equals_original(entry.path());

                if cfg!(miri) {
                    // Only run a single tile test under miri; it's too expensive.
                    return;
                }
            }
        }
    }

    #[test]
    fn round_trip_from_builder_without_changes_including_traffic() {
        let base_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles-with-traffic");
        for entry in WalkDir::new(base_dir) {
            let entry = entry.expect("Unable to traverse directory");

            if entry.file_type().is_file()
                && entry
                    .path()
                    .extension()
                    .is_some_and(|ext| ext.eq_ignore_ascii_case("gph"))
            {
                assert_round_trip_unmodified_equals_original(entry.path());

                if cfg!(miri) {
                    // Only run a single tile test under miri; it's too expensive.
                    return;
                }
            }
        }
    }

    #[test]
    fn add_predicted_speeds() {
        let base_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");

        let in_bytes = std::fs::read(base_dir.join("0").join("003").join("015.gph"))
            .expect("Unable to read file");
        let tile_handle =
            OwnedGraphTileHandle::try_from(in_bytes.clone()).expect("Unable to get tile handle");

        // Enrich the tile with the exact same speed information that we did using the Valhalla CSV tools.
        //
        // 0/3015/0,50,40,
        // 0/3015/42,100,42,BcUACQAEACEADP/7/9sAGf/fAAwAGwARAAX/+AAAAB0AFAAS//AAF//+ACwACQAqAAAAKP/6AEMABABsAAsBBAAq/rcAAP+bAAz/zv/s/9MABf/Y//X/8//9/+wACf/P//EADv/8//L//P/y//H////7AAwAFf/5//oADgAZAAQAFf/3/+8AB//yAB8ABv/0AAUAEf/8//QAFAAG//b////j//v//QAT//7/+f/kABMABwABAAv/6//8//cAEwAAABT/8v/6//wAAAAQ//cACwAFAAT/1//sAAEADAABAAYAE//9AAn/7gAH/+AAFQAB//4AC//o/+gAE//+AAAAFf/l//kABP/+//kACAAG//cAHv/qAB0AAv/4/+v/+wALAAMABP/3AAT/8wAIAAr/9wAK//j/+wAEAAD/+P/8//v/8f/2//L//AALAAcABgAG//gAAv/5AAoAHv//AAcAFf/zABD/7AAUAAv/7v/8AAgACAAN//0ADP/iABD/9f/3//7/+P/3AAQADP//AAMABw==
        // 0/3015/7,12,34,CKD/4f/r/+H/6//g/+v/4P/q/9//6v/f/+r/3v/q/93/6f/b/+n/2v/o/9f/5//V/+b/0f/l/8z/4//G/+D/vf/d/67/1/+V/8z/Xf+u/nz+GwLJAEcAqwAWAFwABwA8AAAAK//8ACD/+AAZ//YAE//0AA//8gAM//AACf/uAAb/7AAE/+kAAv/m////4v/9/93/+f/U//T/xf/q/5//y/6PAQMAngApADkAFwAfABAAEwAMAAwACQAHAAcAAwAGAAAABf/9AAT/+wAD//kAA//2AAL/9AAC//EAAf/tAAH/6AAA/+EAAP/U////tv///x8AFADL//8AQ///ACf//gAa//4AE//+AA7//QAL//0ACP/9AAb//AAE//wAAv/8AAD/+//+//v//P/6//r/+v/2//n/8v/4/+v/9f/b/+//nP+TALoADAAyAAMAHgAAABX//gAQ//0ADf/9AAv//AAJ//sAB//7AAb/+gAF//kABP/4AAP/9wAC//YAAf/1AAD/8//+//D//P/q//f/2w==
        let out_bytes = GraphTileBuilder::from(&tile_handle)
            // Typical flow speeds
            .with_average_speeds(0, 50, 40).unwrap()
            .with_average_speeds(42, 100, 42).unwrap()
            // No, this isn't supposed to make sense; it's test data :P
            .with_average_speeds(7, 12, 34).unwrap()
            // Granular predicted (historical) speeds
            .with_predicted_encoded_speeds(7, "CKD/4f/r/+H/6//g/+v/4P/q/9//6v/f/+r/3v/q/93/6f/b/+n/2v/o/9f/5//V/+b/0f/l/8z/4//G/+D/vf/d/67/1/+V/8z/Xf+u/nz+GwLJAEcAqwAWAFwABwA8AAAAK//8ACD/+AAZ//YAE//0AA//8gAM//AACf/uAAb/7AAE/+kAAv/m////4v/9/93/+f/U//T/xf/q/5//y/6PAQMAngApADkAFwAfABAAEwAMAAwACQAHAAcAAwAGAAAABf/9AAT/+wAD//kAA//2AAL/9AAC//EAAf/tAAH/6AAA/+EAAP/U////tv///x8AFADL//8AQ///ACf//gAa//4AE//+AA7//QAL//0ACP/9AAb//AAE//wAAv/8AAD/+//+//v//P/6//r/+v/2//n/8v/4/+v/9f/b/+//nP+TALoADAAyAAMAHgAAABX//gAQ//0ADf/9AAv//AAJ//sAB//7AAb/+gAF//kABP/4AAP/9wAC//YAAf/1AAD/8//+//D//P/q//f/2w==").unwrap()
            .with_predicted_encoded_speeds(42, "BcUACQAEACEADP/7/9sAGf/fAAwAGwARAAX/+AAAAB0AFAAS//AAF//+ACwACQAqAAAAKP/6AEMABABsAAsBBAAq/rcAAP+bAAz/zv/s/9MABf/Y//X/8//9/+wACf/P//EADv/8//L//P/y//H////7AAwAFf/5//oADgAZAAQAFf/3/+8AB//yAB8ABv/0AAUAEf/8//QAFAAG//b////j//v//QAT//7/+f/kABMABwABAAv/6//8//cAEwAAABT/8v/6//wAAAAQ//cACwAFAAT/1//sAAEADAABAAYAE//9AAn/7gAH/+AAFQAB//4AC//o/+gAE//+AAAAFf/l//kABP/+//kACAAG//cAHv/qAB0AAv/4/+v/+wALAAMABP/3AAT/8wAIAAr/9wAK//j/+wAEAAD/+P/8//v/8f/2//L//AALAAcABgAG//gAAv/5AAoAHv//AAcAFf/zABD/7AAUAAv/7v/8AAgACAAN//0ADP/iABD/9f/3//7/+P/3AAQADP//AAMABw==").unwrap()
            .into_bytes().unwrap();

        let base_dir_with_traffic = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles-with-traffic");
        let expected_out_bytes =
            std::fs::read(base_dir_with_traffic.join("0").join("003").join("015.gph"))
                .expect("Unable to read file");

        if out_bytes != expected_out_bytes {
            std::fs::write("/tmp/failed.gph", &out_bytes).expect("Failed to write failed output");
        }

        assert_eq!(out_bytes, expected_out_bytes);
    }

    #[test]
    fn predicted_speeds_deduplication() {
        let base_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");

        let in_bytes = std::fs::read(base_dir.join("0").join("003").join("015.gph"))
            .expect("Unable to read file");
        let tile_handle =
            OwnedGraphTileHandle::try_from(in_bytes.clone()).expect("Unable to get tile handle");

        // Define two different speed profiles
        let profile_a: [i16; COEFFICIENT_COUNT] = [1; 200];
        let profile_b: [i16; COEFFICIENT_COUNT] = [2; 200];

        // Add the same profile to multiple edges
        let builder = GraphTileBuilder::from(&tile_handle)
            .with_predicted_speed_coefficients(0, &profile_a)
            .unwrap()
            .with_predicted_speed_coefficients(1, &profile_a)
            .unwrap() // Duplicate of edge 0
            .with_predicted_speed_coefficients(2, &profile_b)
            .unwrap()
            .with_predicted_speed_coefficients(3, &profile_a)
            .unwrap() // Duplicate of edge 0
            .with_predicted_speed_coefficients(4, &profile_b)
            .unwrap(); // Duplicate of edge 2

        let out_bytes = builder.into_bytes().unwrap();
        let out_handle =
            OwnedGraphTileHandle::try_from(out_bytes).expect("Unable to get output tile handle");
        let out_view = out_handle.borrow_dependent();

        // Verify that we have predicted speeds
        let predicted_speeds = out_view
            .predicted_speeds
            .as_ref()
            .expect("Expected predicted speeds to be present");

        // Verify that edges 0, 1, and 3 share the same offset (profile_a)
        let (offsets, profiles) = predicted_speeds.as_offsets_and_profiles();

        // We added 5 edges but only 2 unique profiles (profile_a and profile_b)
        // So we should have exactly 2 profiles in memory
        let profile_count = profiles.len() / COEFFICIENT_COUNT;
        assert_eq!(
            profile_count, 2,
            "Expected exactly 2 unique speed profiles to be stored"
        );
        assert_eq!(
            offsets[0].get(),
            offsets[1].get(),
            "Edges 0 and 1 should share the same speed profile offset"
        );
        assert_eq!(
            offsets[0].get(),
            offsets[3].get(),
            "Edges 0 and 3 should share the same speed profile offset"
        );

        // Verify that edges 2 and 4 share the same offset (profile_b)
        assert_eq!(
            offsets[2].get(),
            offsets[4].get(),
            "Edges 2 and 4 should share the same speed profile offset"
        );

        // Verify that the two profiles have different offsets
        assert_ne!(
            offsets[0].get(),
            offsets[2].get(),
            "Edges 0 and 2 have different profiles, so they should have different offsets"
        );
    }
}
