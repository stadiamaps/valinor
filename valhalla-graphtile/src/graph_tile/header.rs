use crate::{AsCowStr, BIN_COUNT, GraphId};
use bitfield_struct::bitfield;
use geo::{Coord, coord};
use std::borrow::Cow;
use zerocopy::{F32, LE, U16, U32, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

/// Remaining variable offset slots for growth.
/// See valhalla/balder/graphtileheader.h for details.
const EMPTY_SLOTS: usize = 11;

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct FirstBitfield {
    #[bits(46, from = bit_twiddling_helpers::conv_u64le::from_inner, into = bit_twiddling_helpers::conv_u64le::into_inner)]
    graph_id: U64<LE>,
    #[bits(4)]
    density: u8,
    #[bits(4)]
    name_quality: u8,
    #[bits(4)]
    speed_quality: u8,
    #[bits(4)]
    exit_quality: u8,
    // NOTE: We don't use bool, because that doesn't have a `FromBytes` implementation.
    // We are only using a single bit though, so we *can* guarantee that the bit pattern is valid.
    // This will probably change once we have the ability to assume bit validity.
    // This is currently in beta: https://doc.rust-lang.org/beta/std/mem/trait.TransmuteFrom.html.
    #[bits(1)]
    has_elevation: u8,
    #[bits(1)]
    has_ext_directed_edge: u8,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct SecondBitfield {
    #[bits(21, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    node_count: U32<LE>,
    #[bits(21, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    directed_edge_count: U32<LE>,
    #[bits(21, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    predicted_speeds_count: U32<LE>,
    #[bits(1)]
    _spare: u8,
}

// NOTE: There are a lot of weird paddings which arose because of an incompatibility in padding
// between x86 and amd64 architectures.
// This was entirely accidental upstream and will eventually be cleaned up in v4.

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct TransitionCountBitfield {
    #[bits(22, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    transition_count: U32<LE>,
    // Deprecated; scheduled for deletion in v4
    #[bits(10)]
    _spare: U16<LE>,
}

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct TurnLaneCountBitfield {
    #[bits(21, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    turn_lane_count: U32<LE>,
    #[bits(11)]
    _spare: u16,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct TransitRecordBitfield {
    #[bits(16, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    transfer_count: U16<LE>,
    #[bits(7)]
    _spare: U8<LE>,
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    departure_count: U32<LE>,
    #[bits(16, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    stop_count: U16<LE>,
    #[bits(1)]
    _spare: u8,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct MiscCountsBitFieldOne {
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    route_count: U16<LE>,
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    schedule_count: U16<LE>,
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    sign_count: U32<LE>,
    #[bits(16)]
    _spare: Ui6<LE>,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct MiscCountsBitFieldTwo {
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    access_restriction_count: U32<LE>,
    #[bits(16, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    admin_count: U16<LE>,
    #[bits(24)]
    _spare: U32<LE>,
}

// TODO: Unsure if packed is needed as well.
// Seems like it's technically not, since Valhalla is explicit about padding
/// Summary information about the graph tile.
///
/// This contains metadata like version,
/// number of nodes and edges,
/// and pointer offsets to other data.
#[derive(Copy, Clone, FromBytes, IntoBytes, Immutable, Unaligned, Debug)]
#[repr(C)]
pub struct GraphTileHeader {
    bit_field_1: FirstBitfield,
    base_lon_lat: [F32<LE>; 2],
    version: [u8; 16],
    /// The dataset ID (canonically, the last OSM changeset ID).
    pub dataset_id: U64<LE>,
    bit_field_2: SecondBitfield,
    transition_count_bitfield: TransitionCountBitfield,
    turn_lane_count_bitfield: TurnLaneCountBitfield,
    transit_record_bitfield: TransitRecordBitfield,
    misc_counts_bit_field_one: MiscCountsBitFieldOne,
    misc_counts_bit_field_two: MiscCountsBitFieldTwo,
    /// These can be used for custom information while retaining Valhalla compatibility.
    /// However, you must uphold the following invariants:
    ///
    /// - The header size doesn't change.
    /// - The ordering of *existing* fields in the data structure doesn't change.
    _reserved_1: U64<LE>,
    _reserved_2: U64<LE>,
    // Internal offsets that help us size the variable length data fields.
    complex_restriction_forward_offset: U32<LE>,
    complex_restriction_reverse_offset: U32<LE>,
    edge_info_offset: U32<LE>,
    text_list_offset: U32<LE>,
    /// The date the tile was created (since pivot date).
    /// TODO: Figure out what pivot date means; probably hide the raw value
    pub create_date: U32<LE>,
    /// Offsets for each bin of the grid (for search/lookup)
    bin_offsets: [U32<LE>; BIN_COUNT],
    /// Offset to the beginning of the variable sized data.
    lane_connectivity_offset: U32<LE>,
    /// Offset to the beginning of the variable sized data.
    predicted_speeds_offset: U32<LE>,
    /// The size of the tile (in bytes)
    pub tile_size: U32<LE>,
    /// See valhalla/balder/graphtileheader.h for details.
    _empty_slots: [U32<LE>; EMPTY_SLOTS],
}

impl GraphTileHeader {
    /// The full Graph ID of this tile.
    #[inline]
    pub const fn graph_id(&self) -> GraphId {
        // Safety: We know that the bit field cannot contain a value
        // larger than the max allowed value.
        unsafe { GraphId::from_id_unchecked(self.bit_field_1.graph_id().get()) }
    }

    /// The relative road density within this tile (0-15).
    #[inline]
    pub const fn density(&self) -> u8 {
        self.bit_field_1.density()
    }

    /// The relative quality of name assignment for this tile (0-15).
    #[inline]
    pub const fn name_quality(&self) -> u8 {
        self.bit_field_1.name_quality()
    }

    /// The relative quality of speed assignment for this tile (0-15).
    #[inline]
    pub const fn speed_quality(&self) -> u8 {
        self.bit_field_1.speed_quality()
    }

    /// The relative quality of exit signs for this tile (0-15).
    #[inline]
    pub const fn exit_quality(&self) -> u8 {
        self.bit_field_1.exit_quality()
    }

    /// Does this tile include elevation data?
    #[inline]
    pub const fn has_elevation(&self) -> bool {
        self.bit_field_1.has_elevation() != 0
    }

    /// Does this tile include extended directed edge attributes?
    #[inline]
    pub const fn has_ext_directed_edge(&self) -> bool {
        self.bit_field_1.has_ext_directed_edge() != 0
    }

    /// The coordinate of the southwest corner of this graph tile.
    #[inline]
    pub const fn sw_corner(&self) -> Coord<f32> {
        coord! {x: self.base_lon_lat[0].get(), y: self.base_lon_lat[1].get()}
    }

    /// Gets the version of Baldr used to generate this graph tile.
    pub fn version(&self) -> Cow<'_, str> {
        self.version.as_cow_str()
    }

    #[inline]
    pub const fn node_count(&self) -> u32 {
        self.bit_field_2.node_count().get()
    }

    /// The number of directed edges in this graph tile.
    #[inline]
    pub const fn directed_edge_count(&self) -> u32 {
        self.bit_field_2.directed_edge_count().get()
    }

    /// The number of predicted speed records in this graph tile.
    #[inline]
    pub const fn predicted_speeds_count(&self) -> u32 {
        self.bit_field_2.predicted_speeds_count().get()
    }

    /// The number of node transitions in this graph tile.
    #[inline]
    pub const fn transition_count(&self) -> u32 {
        self.transition_count_bitfield.transition_count().get()
    }

    /// The number of turn lanes in this graph tile.
    #[inline]
    pub const fn turn_lane_count(&self) -> u32 {
        self.turn_lane_count_bitfield.turn_lane_count().get()
    }

    /// The number of transit transfers in this graph tile.
    #[inline]
    pub const fn transfer_count(&self) -> u16 {
        self.transit_record_bitfield.transfer_count().get()
    }

    /// The number of transit departures in this graph tile.
    #[inline]
    pub const fn departure_count(&self) -> u32 {
        self.transit_record_bitfield.departure_count().get()
    }

    /// The number of transit stops in this graph tile.
    #[inline]
    pub const fn stop_count(&self) -> u16 {
        self.transit_record_bitfield.stop_count().get()
    }

    /// The number of transit routes in this graph tile.
    #[inline]
    pub const fn route_count(&self) -> u16 {
        self.misc_counts_bit_field_one.route_count().get()
    }

    /// The number of transit schedules in this graph tile.
    #[inline]
    pub const fn schedule_count(&self) -> u16 {
        self.misc_counts_bit_field_one.schedule_count().get()
    }

    /// The number of signs in this graph tile.
    #[inline]
    pub const fn sign_count(&self) -> u32 {
        self.misc_counts_bit_field_one.sign_count().get()
    }

    /// The number of access restrictions in this graph tile.
    #[inline]
    pub const fn access_restriction_count(&self) -> u32 {
        self.misc_counts_bit_field_two
            .access_restriction_count()
            .get()
    }

    /// The number of admin records in this graph tile.
    #[inline]
    pub const fn admin_count(&self) -> u16 {
        self.misc_counts_bit_field_two.admin_count().get()
    }

    // These size calculation helpers avoid exposing the raw offsets.
    // The calculations come from graphtile.cc, where they do the same math in `GraphTile::Initialize`
    // directly.

    /// The size (in bytes) occupied by the edge bins structure.
    #[inline]
    pub const fn edge_bins_size(&self) -> usize {
        self.bin_offsets[BIN_COUNT - 1].get() as usize
    }

    /// The size (in bytes) occupied by the complex forward restrictions.
    #[inline]
    pub const fn complex_forward_restrictions_size(&self) -> usize {
        (self.complex_restriction_reverse_offset.get()
            - self.complex_restriction_forward_offset.get()) as usize
    }

    /// The size (in bytes) occupied by the complex reverse restrictions.
    #[inline]
    pub const fn complex_reverse_restrictions_size(&self) -> usize {
        (self.edge_info_offset.get() - self.complex_restriction_reverse_offset.get()) as usize
    }

    /// The size (in bytes) occupied by the edge info data structure.
    #[inline]
    pub const fn edge_info_size(&self) -> usize {
        (self.text_list_offset.get() - self.edge_info_offset.get()) as usize
    }

    /// The size (in bytes) occupied by the text list.
    #[inline]
    pub const fn text_list_size(&self) -> usize {
        (self.lane_connectivity_offset.get() - self.text_list_offset.get()) as usize
    }

    /// The size (in bytes) occupied by the lane connectivity data.
    #[inline]
    pub const fn lane_connectivity_size(&self) -> usize {
        if self.predicted_speeds_count() > 0 {
            (self.predicted_speeds_offset.get() - self.lane_connectivity_offset.get()) as usize
        } else {
            (self.tile_size.get() - self.lane_connectivity_offset.get()) as usize
        }
    }
}

#[cfg(test)]
mod test {
    use crate::graph_tile::{GraphTile, TEST_GRAPH_TILE_L0, TEST_GRAPH_TILE_L2};

    #[test]
    fn test_parse_header() {
        let tile = &*TEST_GRAPH_TILE_L0;

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(tile.header());
        }
    }

    #[test]
    fn test_parse_header_L2() {
        let tile = &*TEST_GRAPH_TILE_L2;

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(tile.header());
        }
    }
}
