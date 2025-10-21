use crate::{Access, GraphId, RoadClass, RoadUse, Surface};
use bitfield_struct::bitfield;
use enumset::EnumSet;
#[cfg(feature = "serde")]
use serde::{Serialize, Serializer, ser::SerializeStruct};
use std::fmt::{Debug, Formatter};
use zerocopy::{LE, U16, U32, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct FirstBitfield {
    #[bits(46, from = bit_twiddling_helpers::conv_u64le::from_inner, into = bit_twiddling_helpers::conv_u64le::into_inner)]
    end_node: U64<LE>,
    #[bits(8)]
    restrictions: u8,
    #[bits(7, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    opposing_edge_index: U32<LE>,
    // Booleans represented this way for infailability.
    // See comment in node_info.rs for details.
    #[bits(1)]
    forward: u8,
    #[bits(1)]
    leaves_tile: u8,
    #[bits(1)]
    country_crossing: u8,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct SecondBitfield {
    #[bits(25, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    edge_info_offset: U32<LE>,
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    access_restrictions: U16<LE>,
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    start_restriction: U16<LE>,
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    end_restriction: U16<LE>,
    // Booleans represented this way for infailability.
    // See comment in node_info.rs for details.
    #[bits(1)]
    complex_restriction: u8,
    #[bits(1)]
    dest_only: u8,
    #[bits(1)]
    no_thru: u8,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct ThirdBitfield {
    #[bits(8)]
    speed: u8,
    #[bits(8)]
    free_flow_speed: u8,
    #[bits(8)]
    constrained_flow_speed: u8,
    #[bits(8)]
    truck_speed: u8,
    #[bits(8)]
    name_consistency: u8,
    #[bits(6)]
    edge_use: RoadUse,
    #[bits(4)]
    lane_count: u8,
    #[bits(4)]
    density: u8,
    #[bits(3)]
    classification: RoadClass,
    #[bits(3)]
    surface: Surface,
    // Booleans represented this way for infailability.
    // See comment in node_info.rs for details.
    #[bits(1)]
    toll: u8,
    #[bits(1)]
    roundabout: u8,
    #[bits(1)]
    truck_route: u8,
    #[bits(1)]
    has_predicted_speed: u8,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct FourthBitfield {
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    forward_access: U16<LE>,
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    reverse_access: U16<LE>,
    #[bits(5)]
    max_up_slope: u8,
    #[bits(5)]
    max_down_slope: u8,
    #[bits(3)]
    sac_scale: u8,
    #[bits(2)]
    cycle_lane: u8,
    // Booleans represented this way for infailability.
    // See comment in node_info.rs for details.
    #[bits(1)]
    is_bike_network: u8,
    #[bits(1)]
    use_sidepath: u8,
    #[bits(1)]
    bicycle_dismount: u8,
    #[bits(1)]
    has_sidewalk_left: u8,
    #[bits(1)]
    has_sidewalk_right: u8,
    #[bits(1)]
    has_shoulder: u8,
    #[bits(1)]
    has_lane_connectivity: u8,
    #[bits(1)]
    has_turn_lanes: u8,
    #[bits(1)]
    has_exit_signs: u8,
    #[bits(1)]
    is_intersection_internal: u8,
    #[bits(1)]
    is_tunnel: u8,
    #[bits(1)]
    is_bridge: u8,
    #[bits(1)]
    has_traffic_signal: u8,
    #[bits(1)]
    is_seasonal: u8,
    #[bits(1)]
    is_dead_end: u8,
    #[bits(1)]
    has_bss_connection: u8,
    #[bits(1)]
    has_stop_sign: u8,
    #[bits(1)]
    has_yield_sign: u8,
    #[bits(1)]
    hov_type: u8,
    #[bits(1)]
    is_indoor: u8,
    #[bits(1)]
    is_lit: u8,
    #[bits(1)]
    is_dest_only_hgv: u8,
    #[bits(3)]
    _spare: u8,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct FifthBitfield {
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    turn_type: U32<LE>,
    #[bits(8)]
    edge_to_left: u8,
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    length: U32<LE>,
    #[bits(4)]
    weighted_grade: u8,
    #[bits(4)]
    curvature: u8,
}

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct StopImpact {
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    impact_between_edges: U32<LE>,
    #[bits(8)]
    edge_to_right: u8,
}

/// Stores either the stop impact or the transit line identifier.
/// Since transit lines are schedule-based, they have no need for edge transition logic,
/// so we can freely share this field.
#[repr(C)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Copy, Clone)]
union StopOrLine {
    stop_impact: StopImpact,
    line_id: U32<LE>,
}

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct SeventhBitField {
    #[bits(7)]
    local_level_edge_index: u8,
    #[bits(7)]
    local_level_opp_edge_index: u8,
    #[bits(7)]
    shortcut: u8,
    #[bits(7)]
    superseded: u8,
    // Booleans represented this way for infailability.
    // See comment in node_info.rs for details.
    #[bits(1)]
    is_shortcut: u8,
    #[bits(1)]
    speed_type: u8,
    #[bits(1)]
    is_named: u8,
    #[bits(1)]
    link_tag: u8,
}

impl Debug for StopOrLine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // Safety: It doesn't matter if we interpret this wrong as both fields are
        // packed into a u32.
        unsafe { f.write_fmt(format_args!("StopOrLine {{ raw_value: {} }}", self.line_id)) }
    }
}

/// A directed edge within the routing graph.
///
/// This struct contains only the essential edge information
/// which is needed for routing calculations.
/// Additional details can be found in the [`EdgeInfo`](super::EdgeInfo) struct,
/// which contains things like the encoded shape, OSM way ID,
/// and other info that is not necessary for making routing decisions.
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Clone)]
#[repr(C)]
pub struct DirectedEdge {
    first_bitfield: FirstBitfield,
    second_bitfield: SecondBitfield,
    third_bitfield: ThirdBitfield,
    fourth_bitfield: FourthBitfield,
    fifth_bitfield: FifthBitfield,
    stop_impact_or_line: StopOrLine,
    seventh_bitfield: SeventhBitField,
}

impl DirectedEdge {
    // TODO: Dozens of access helpers :)

    /// Is this a transit line (buss or rail)?
    #[inline]
    pub const fn end_node_id(&self) -> GraphId {
        // Safety: We know the number of bits is limited
        unsafe { GraphId::from_id_unchecked(self.first_bitfield.end_node().get()) }
    }

    /// Gets the index of the opposing directed edge at the end node of this directed edge.
    ///
    /// Can be used to find the start node of this directed edge.
    #[inline]
    pub const fn opposing_edge_index(&self) -> u32 {
        self.first_bitfield.opposing_edge_index().get()
    }

    /// Is this edge a shortcut?
    #[inline]
    pub const fn is_shortcut(&self) -> bool {
        self.seventh_bitfield.is_shortcut() != 0
    }

    /// Gets the offset into the variable sized edge info field.
    #[inline]
    pub const fn edge_info_offset(&self) -> u32 {
        self.second_bitfield.edge_info_offset().get()
    }

    /// Is the edge info forward or reverse?
    ///
    /// TODO: Determine the practical implications of this
    #[inline]
    pub const fn forward(&self) -> bool {
        self.first_bitfield.forward() != 0
    }

    /// Does the edge cross into a new country?
    #[inline]
    pub const fn country_crossing(&self) -> bool {
        self.first_bitfield.country_crossing() != 0
    }

    /// Is the edge destination-only (ex: private roads)?
    #[inline]
    pub const fn dest_only(&self) -> bool {
        self.second_bitfield.dest_only() != 0
    }

    /// Does the edge lead to a "no-through" region?
    #[inline]
    pub const fn no_thru(&self) -> bool {
        self.second_bitfield.no_thru() != 0
    }

    /// The estimated edge speed, in kph.
    ///
    /// NOTE: Values above 250 are special, and zero means no data.
    /// TODO: Reflect this in types?
    #[inline]
    pub const fn speed(&self) -> u8 {
        self.third_bitfield.speed()
    }

    /// The estimated speed of the edge when there is no traffic, in kph.
    ///
    /// NOTE: Values above 250 are special, and zero means no data.
    /// TODO: Reflect this in types?
    #[inline]
    pub const fn free_flow_speed(&self) -> u8 {
        self.third_bitfield.free_flow_speed()
    }

    /// Set the estimated speed of the edge when there is no traffic, in kph.
    ///
    /// NOTE: Values above 250 are special, and zero means no data.
    /// TODO: Reflect this in types?
    #[inline]
    pub const fn set_free_flow_speed(&mut self, speed: u8) {
        self.third_bitfield.set_free_flow_speed(speed)
    }

    /// The estimated speed of the edge when there is traffic, in kph.
    ///
    /// NOTE: Values above 250 are special, and zero means no data.
    /// TODO: Reflect this in types?
    #[inline]
    pub const fn constrained_flow_speed(&self) -> u8 {
        self.third_bitfield.constrained_flow_speed()
    }

    /// Set the estimated speed of the edge when there is traffic, in kph.
    ///
    /// NOTE: Values above 250 are special, and zero means no data.
    /// TODO: Reflect this in types?
    #[inline]
    pub const fn set_constrained_speed(&mut self, speed: u8) {
        self.third_bitfield.set_constrained_flow_speed(speed)
    }

    /// The estimated speed of the edge for trucks, in kph.
    ///
    /// NOTE: Values above 250 are special, and zero means no data.
    /// TODO: Reflect this in types?
    #[inline]
    pub const fn truck_speed(&self) -> u8 {
        self.third_bitfield.truck_speed()
    }

    /// Set the estimated speed of the edge for trucks, in kph.
    ///
    /// NOTE: Values above 250 are special, and zero means no data.
    /// TODO: Reflect this in types?
    #[inline]
    pub const fn set_truck_speed(mut self, speed: u8) {
        self.third_bitfield.set_truck_speed(speed)
    }

    /// The way the edge is used.
    #[inline]
    pub fn edge_use(&self) -> RoadUse {
        self.third_bitfield.edge_use()
    }

    /// Is this a transit line (bus or rail)?
    ///
    /// # Panics
    ///
    /// Can panic as a result of the issues noted in [`Self::edge_use`].
    #[inline]
    pub fn is_transit_line(&self) -> bool {
        let edge_use = self.edge_use();
        edge_use == RoadUse::Rail || edge_use == RoadUse::Bus
    }

    /// The number of lanes.
    #[inline]
    pub const fn lane_count(&self) -> u8 {
        self.third_bitfield.lane_count()
    }

    /// The relative density along the edge.
    #[inline]
    pub const fn density(&self) -> u8 {
        self.third_bitfield.density()
    }

    /// The classification of the road.
    #[inline]
    pub const fn classification(&self) -> RoadClass {
        self.third_bitfield.classification()
    }

    /// The generalized road surface type.
    #[inline]
    pub const fn surface(&self) -> Surface {
        self.third_bitfield.surface()
    }

    /// Is this edge part of a toll road?
    #[inline]
    pub const fn toll(&self) -> bool {
        self.third_bitfield.toll() != 0
    }

    /// Is this edge part of a roundabout?
    #[inline]
    pub const fn roundabout(&self) -> bool {
        self.third_bitfield.roundabout() != 0
    }

    /// Is this edge part of a truck route?
    #[inline]
    pub const fn truck_route(&self) -> bool {
        self.third_bitfield.truck_route() != 0
    }

    /// Does this edge have predicted speeds?
    #[inline]
    pub const fn has_predicted_speed(&self) -> bool {
        self.third_bitfield.has_predicted_speed() != 0
    }

    /// Sets whether the edge has predicted speed information.
    ///
    /// This should ALWAYS be called in tandem with [`crate::graph_tile::GraphTileBuilder::with_predicted_speeds`]
    /// or [`crate::graph_tile::GraphTileBuilder::with_predicted_encoded_speeds`],
    #[inline]
    pub(crate) fn set_has_predicted_speed(&mut self, value: bool) {
        self.third_bitfield.set_has_predicted_speed(value.into());
    }

    /// Gets the forward access modes.
    ///
    /// TODO: Determine the impact of [`self.forward`] on this
    #[inline]
    pub fn forward_access(&self) -> EnumSet<Access> {
        // Safety: The access bits are length 12, so invalid representations are impossible.
        unsafe { EnumSet::from_repr_unchecked(self.fourth_bitfield.forward_access().get()) }
    }

    /// Gets the reverse access modes.
    ///
    /// TODO: Determine the impact of `forward` on this
    #[inline]
    pub fn reverse_access(&self) -> EnumSet<Access> {
        // Safety: The access bits are length 12, so invalid representations are impossible.
        unsafe { EnumSet::from_repr_unchecked(self.fourth_bitfield.reverse_access().get()) }
    }
}

// The bitfield struct macros break serde field attributes, so we roll our own for now.
#[cfg(feature = "serde")]
impl Serialize for DirectedEdge {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let num_fields = 22;

        #[cfg(not(feature = "serialize_predicted_speed"))]
        let num_fields = num_fields - 3;

        let mut state = serializer.serialize_struct("DirectedEdge", num_fields)?;

        state.serialize_field("forward", &self.forward())?;
        state.serialize_field("country_crossing", &self.country_crossing())?;

        state.serialize_field(
            "access_restrictions",
            &self.second_bitfield.access_restrictions().get(),
        )?;
        state.serialize_field(
            "start_restriction",
            &self.second_bitfield.start_restriction().get(),
        )?;
        state.serialize_field(
            "end_restriction",
            &self.second_bitfield.end_restriction().get(),
        )?;
        state.serialize_field(
            "complex_restriction",
            &self.second_bitfield.complex_restriction(),
        )?;
        state.serialize_field("dest_only", &self.dest_only())?;
        state.serialize_field("no_thru", &self.no_thru())?;

        state.serialize_field("speed", &self.speed())?;
        #[cfg(feature = "serialize_predicted_speed")]
        state.serialize_field("free_flow_speed", &self.free_flow_speed())?;
        #[cfg(feature = "serialize_predicted_speed")]
        state.serialize_field("constrained_flow_speed", &self.constrained_flow_speed())?;

        // TODO: Name consistency
        state.serialize_field("use", &self.edge_use())?;
        state.serialize_field("lane_count", &self.lane_count())?;
        state.serialize_field("density", &self.density())?;
        state.serialize_field("classification", &self.classification())?;
        state.serialize_field("surface", &self.surface())?;
        state.serialize_field("toll", &self.toll())?;
        state.serialize_field("roundabout", &self.roundabout())?;
        state.serialize_field("truck_route", &self.truck_route())?;
        #[cfg(feature = "serialize_predicted_speed")]
        state.serialize_field("has_predicted_speed", &self.has_predicted_speed())?;

        state.serialize_field(
            "forward_access",
            &self
                .forward_access()
                .iter()
                .map(|v| v.as_char())
                .collect::<String>(),
        )?;
        state.serialize_field(
            "reverse_access",
            &self
                .reverse_access()
                .iter()
                .map(|v| v.as_char())
                .collect::<String>(),
        )?;

        state.end()
    }
}

/// Extended directed edge attributes.
///
/// This is extra space to add directed edge attributes without breaking backward compatibility.
#[repr(C)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Clone)]
pub struct DirectedEdgeExt(U64<LE>);

#[cfg(test)]
mod test {
    use crate::graph_tile::{GraphTile, TEST_GRAPH_TILE_L0};

    #[test]
    fn test_parse_directed_edges_count() {
        let tile = &*TEST_GRAPH_TILE_L0;

        assert_eq!(
            tile.directed_edges().len(),
            tile.header().directed_edge_count() as usize
        );
    }

    #[test]
    fn test_parse_nodes() {
        let tile = &*TEST_GRAPH_TILE_L0;

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!("first_directed_edge", tile.directed_edges()[0]);
            insta::assert_debug_snapshot!(
                "last_directed_edge",
                tile.directed_edges().last().unwrap()
            );
        }

        // TODO: Other sanity checks after we add some more advanced methods
    }
}
