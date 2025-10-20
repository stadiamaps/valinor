use super::{
    FirstBitfield, GraphTileHeader, MiscCountsBitFieldOne, MiscCountsBitFieldTwo, SecondBitfield,
    TransitRecordBitfield, TransitionCountBitfield, TurnLaneCountBitfield, VALHALLA_EPOCH,
    VERSION_LEN,
};
use crate::graph_tile::GraphTileError::CastError;
use crate::graph_tile::predicted_speeds::COEFFICIENT_COUNT;
use crate::graph_tile::{
    AccessRestriction, Admin, DirectedEdge, DirectedEdgeExt, GraphTileError, NodeInfo,
    NodeTransition, Sign, TransitDeparture, TransitRoute, TransitSchedule, TransitStop,
    TransitTransfer, TurnLane,
};
use crate::{BIN_COUNT, GraphId};
use chrono::{DateTime, Utc};
use geo::Coord;

/// A builder struct that helps us build correct graph tile headers.
///
/// This is not exposed in the public API by design at the moment,
/// because it is unstable and not as safe as it could be.
/// This can theoretically be made public if we figure out a way to make it a bit safer.
/// The main point of unsafety is that it requires the caller to self-report a lot of data
/// in header-friendly formats rather than user-friendly ones.
///
/// An alternate approach to the present would be moving most of the fields to the build method,
/// and requiring a dozen or more parameters there.
/// This feels a bit more unwieldy than a large struct init,
/// but perhaps it's the easiest way to make this safer long-term.
///
/// The main reason to make this public would be to enable use of the reserved fields.
/// However, we can probably figure out a way to enable that upstream in the [`crate::graph_tile::GraphTileBuilder`].
pub(crate) struct GraphTileHeaderBuilder {
    pub version: [u8; VERSION_LEN],
    pub graph_id: GraphId,
    /// The relative road density within this tile (0-15).
    ///
    /// NOTE: Valhalla doesn't typically set this when writing initial tiles.
    /// It sets them during a final validation step.
    pub density: u8,
    pub has_elevation: bool,
    pub has_ext_directed_edges: bool,
    pub sw_corner: Coord<f32>,
    /// The dataset ID (canonically, the OSM changeset ID).
    pub dataset_id: u64,
    pub node_count: usize,
    pub directed_edge_count: usize,
    pub predicted_speed_profile_count: usize,
    pub transition_count: usize,
    pub turn_lane_count: usize,
    pub transfer_count: usize,
    pub departure_count: usize,
    pub stop_count: usize,
    pub route_count: usize,
    pub schedule_count: usize,
    pub sign_count: usize,
    pub access_restriction_count: usize,
    pub admin_count: usize,
    pub create_date: DateTime<Utc>,
    // FIXME: This deserves a better interface
    pub bin_offsets: [u32; BIN_COUNT],
    /// Raw memory size in bytes
    pub complex_forward_restrictions_size: usize,
    /// Raw memory size in bytes
    pub complex_reverse_restrictions_size: usize,
    /// Raw memory size in bytes
    pub edge_info_size: usize,
    /// Raw memory size in bytes
    pub text_list_size: usize,
    /// Raw memory size in bytes
    pub lane_connectivity_size: usize,
}

impl GraphTileHeaderBuilder {
    pub(crate) fn build(self) -> Result<GraphTileHeader, GraphTileError> {
        let bit_field_1 = FirstBitfield::default()
            // Guaranteed to be valid
            // (can theoretically be out of the accepted bounds, but this requires unsafe raw init,
            // and it won't corrupt the tile).
            .with_graph_id(self.graph_id.value().into())
            .with_density_checked(self.density.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid density {} must be less than 16",
                    self.density
                ))
            })?
            // NOTE: name_quality, speed_quality, and exit_quality intentionally omitted
            // Guaranteed to be 0 or 1 by the Rust standard
            .with_has_elevation(self.has_elevation.into())
            .with_has_ext_directed_edge(self.has_ext_directed_edges.into());

        let bit_field_2 = SecondBitfield::default()
            .with_node_count_checked(u32::try_from(self.node_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid node count {} does not fit into 21 bits",
                    self.node_count
                ))
            })?
            .with_directed_edge_count_checked(u32::try_from(self.directed_edge_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid directed edge count {} does not fit into 21 bits",
                    self.directed_edge_count
                ))
            })?
            .with_predicted_speeds_count_checked(
                u32::try_from(self.predicted_speed_profile_count)?.into(),
            )
            .map_err(|_| {
                CastError(format!(
                    "Invalid predicted speeds count {} does not fit into 21 bits",
                    self.predicted_speed_profile_count
                ))
            })?;

        let transition_count_bitfield = TransitionCountBitfield::default()
            .with_transition_count_checked(u32::try_from(self.transition_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid transition count {} does not fit into 21 bits",
                    self.transition_count
                ))
            })?;

        let turn_lane_count_bitfield = TurnLaneCountBitfield::default()
            .with_turn_lane_count_checked(u32::try_from(self.turn_lane_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid turn lane count {} does not fit into 21 bits",
                    self.turn_lane_count
                ))
            })?;

        let transit_record_bitfield = TransitRecordBitfield::default()
            .with_transfer_count_checked(u16::try_from(self.transfer_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid transfer count {} does not fit into 16 bits",
                    self.transfer_count
                ))
            })?
            .with_departure_count_checked(u32::try_from(self.departure_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid departure count {} does not fit into 24 bits",
                    self.departure_count
                ))
            })?
            .with_stop_count_checked(u16::try_from(self.stop_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid stop count {} does not fit into 16 bits",
                    self.stop_count
                ))
            })?;

        let misc_counts_bit_field_one = MiscCountsBitFieldOne::default()
            .with_route_count_checked(u16::try_from(self.route_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid route count {} does not fit into 12 bits",
                    self.route_count
                ))
            })?
            .with_schedule_count_checked(u16::try_from(self.schedule_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid schedule count {} does not fit into 12 bits",
                    self.schedule_count
                ))
            })?
            .with_sign_count_checked(u32::try_from(self.sign_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid sign count {} does not fit into 24 bits",
                    self.sign_count
                ))
            })?;

        let misc_counts_bit_field_two = MiscCountsBitFieldTwo::default()
            .with_access_restriction_count_checked(
                u32::try_from(self.access_restriction_count)?.into(),
            )
            .map_err(|_| {
                CastError(format!(
                    "Invalid access restriction count {} does not fit into 24 bits",
                    self.access_restriction_count
                ))
            })?
            .with_admin_count_checked(u16::try_from(self.admin_count)?.into())
            .map_err(|_| {
                CastError(format!(
                    "Invalid admin count {} does not fit into 16 bits",
                    self.admin_count
                ))
            })?;

        // Calculate the starting offset of the variable sized data areas
        let dst_base_offset = size_of::<GraphTileHeader>()
            + (self.node_count * size_of::<NodeInfo>())
            + (self.transition_count * size_of::<NodeTransition>())
            + (self.directed_edge_count * size_of::<DirectedEdge>())
            + (if self.has_ext_directed_edges {
                self.directed_edge_count * size_of::<DirectedEdgeExt>()
            } else {
                0
            })
            + (self.access_restriction_count * size_of::<AccessRestriction>())
            + (self.departure_count * size_of::<TransitDeparture>())
            + (self.stop_count * size_of::<TransitStop>())
            + (self.route_count * size_of::<TransitRoute>())
            + (self.schedule_count * size_of::<TransitSchedule>())
            + (self.transfer_count * size_of::<TransitTransfer>())
            + (self.sign_count * size_of::<Sign>())
            + (self.turn_lane_count * size_of::<TurnLane>())
            + (self.admin_count * size_of::<Admin>())
            // Cross reference with edge_bins_size in header.rs...
            // The interface for this will improve at some point.
            + (usize::try_from(self.bin_offsets[BIN_COUNT - 1])? * size_of::<GraphId>());
        let complex_reverse_restrictions_offset =
            dst_base_offset + self.complex_forward_restrictions_size;
        let edge_info_offset =
            complex_reverse_restrictions_offset + self.complex_reverse_restrictions_size;
        let text_list_offset = edge_info_offset + self.edge_info_size;
        let lane_connectivity_offset = text_list_offset + self.text_list_size;
        let predicted_speed_offset = if self.predicted_speed_profile_count > 0 {
            lane_connectivity_offset + self.lane_connectivity_size
        } else {
            0
        };

        let tile_size = if self.predicted_speed_profile_count > 0 {
            predicted_speed_offset +
            // Offsets
            (self.directed_edge_count * size_of::<u32>())
                // Profile data
                + (self.predicted_speed_profile_count * size_of::<i16>() * COEFFICIENT_COUNT)
        } else {
            lane_connectivity_offset + self.lane_connectivity_size
        };

        Ok(GraphTileHeader {
            bit_field_1,
            base_lon_lat: [self.sw_corner.x.into(), self.sw_corner.y.into()],
            version: self.version,
            dataset_id: self.dataset_id.into(),
            bit_field_2,
            transition_count_bitfield,
            turn_lane_count_bitfield,
            transit_record_bitfield,
            misc_counts_bit_field_one,
            misc_counts_bit_field_two,
            _reserved_1: Default::default(),
            _reserved_2: Default::default(),
            complex_restriction_forward_offset: u32::try_from(dst_base_offset)?.into(),
            complex_restriction_reverse_offset: u32::try_from(complex_reverse_restrictions_offset)?
                .into(),
            edge_info_offset: u32::try_from(edge_info_offset)?.into(),
            text_list_offset: u32::try_from(text_list_offset)?.into(),
            create_date: ((self.create_date - VALHALLA_EPOCH).num_days().max(0) as u32).into(),
            bin_offsets: self.bin_offsets.map(|offset| offset.into()),
            lane_connectivity_offset: u32::try_from(lane_connectivity_offset)?.into(),
            predicted_speeds_offset: u32::try_from(predicted_speed_offset)?.into(),
            tile_size: u32::try_from(tile_size)?.into(),
            _empty_slots: [0.into(); _],
        })
    }
}
