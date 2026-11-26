use super::predicted_speeds::COEFFICIENT_COUNT;
use super::{GraphTileBuildError, GraphTileDecodingError};
use crate::{AsCowStr, BIN_COUNT, GraphId};
use bitfield_struct::bitfield;
use chrono::{DateTime, FixedOffset, NaiveDate, NaiveDateTime, NaiveTime, TimeDelta, Utc};
use geo::{Coord, coord};
use std::borrow::Cow;
use zerocopy::{F32, LE, U16, U32, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, KnownLayout, Unaligned};

mod builder;

pub(super) use builder::GraphTileHeaderBuilder;

/// Expansion slots for future variable-length section offsets.
/// See valhalla/baldr/graphtileheader.h for details.
const EMPTY_SLOTS: usize = 10;

/// The number of UTF-8 bytes in the fixed size version field.
pub(crate) const VERSION_LEN: usize = 16;

/// The Valhalla epoch: Midnight Jan 1, 2014, Eastern Standard Time.
const VALHALLA_EPOCH: DateTime<Utc> = DateTime::<FixedOffset>::from_naive_utc_and_offset(
    NaiveDateTime::new(
        NaiveDate::from_ymd_opt(2014, 1, 1).unwrap(),
        NaiveTime::from_num_seconds_from_midnight_opt(0, 0).unwrap(),
    ),
    FixedOffset::west_opt(5 * 3600).unwrap(),
)
.to_utc();

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq)]
struct FirstBitfield {
    #[bits(46, from = bit_twiddling_helpers::conv_u64le::from_inner, into = bit_twiddling_helpers::conv_u64le::into_inner)]
    graph_id: U64<LE>,
    #[bits(4)]
    density: u8,
    // More relative statistics (0 - 15); name, speed, and exit quality seem unused in Valhalla?
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
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq)]
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
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq)]
struct TransitionCountBitfield {
    /// No, this is not a typo. This bit field has 22 bits.
    ///
    /// There can only be twice as many transitions as there are nodes,
    /// but in practice there are far fewer than this limit.
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
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq)]
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
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq)]
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
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq)]
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
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq)]
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
#[derive(Clone, FromBytes, IntoBytes, Immutable, Unaligned, KnownLayout, Debug, PartialEq)]
#[repr(C)]
pub struct GraphTileHeader {
    bit_field_1: FirstBitfield,
    base_lon_lat: [F32<LE>; 2],
    pub(super) version: [u8; VERSION_LEN],
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
    /// The date the tile was created, expressed as the number of days (rounded down)
    /// since midnight of Jan 1, 2014, Eastern Standard Time.
    create_date: U32<LE>,
    /// Offsets for each bin of the grid
    ///
    /// This is used for search/lookup from a geographic location.
    /// By dividing the tile into a 5x5 grid, we can reduce the number of iterations
    /// to find a specific edge.
    ///
    /// NOTE: Valhalla only actually does binning at level 2,
    /// so these values will be zeroes for other levels.
    pub(super) bin_offsets: [U32<LE>; BIN_COUNT],
    /// Offset to the beginning of the variable length data.
    lane_connectivity_offset: U32<LE>,
    /// Offset to the beginning of the variable length data.
    predicted_speeds_offset: U32<LE>,
    /// The size of the tile (in bytes)
    pub tile_size: U32<LE>,
    bounding_circle_offset: U32<LE>,
    /// Empty expansion slots.
    ///
    /// See valhalla/balder/graphtileheader.h for details.
    expansion_offsets: [U32<LE>; EMPTY_SLOTS],
}

const _: () = assert!(
    size_of::<GraphTileHeader>() == 272,
    "Valhalla header differs from the expected size. Are you sure you know what you're doing?"
);

/// Byte lengths derived from the ordered section boundaries in a tile header.
///
/// The only constructor is failable, and guarantees validity by construction.
pub(super) struct VariableSectionSizes {
    forward_restrictions: usize,
    reverse_restrictions: usize,
    edge_info: usize,
    text_list: usize,
    lane_connectivity: usize,
}

impl VariableSectionSizes {
    pub(super) const fn forward_restrictions(&self) -> usize {
        self.forward_restrictions
    }

    pub(super) const fn reverse_restrictions(&self) -> usize {
        self.reverse_restrictions
    }

    pub(super) const fn edge_info(&self) -> usize {
        self.edge_info
    }

    pub(super) const fn text_list(&self) -> usize {
        self.text_list
    }

    pub(super) const fn lane_connectivity(&self) -> usize {
        self.lane_connectivity
    }
}

impl TryFrom<&GraphTileHeader> for VariableSectionSizes {
    type Error = GraphTileDecodingError;

    fn try_from(header: &GraphTileHeader) -> Result<Self, Self::Error> {
        let section_size = |name: &str, start: u32, end: u32| {
            end.checked_sub(start)
                .map(|size| size as usize)
                .ok_or_else(|| GraphTileDecodingError::CastError {
                    field: "section_offsets".to_string(),
                    error_description: format!(
                        "{name} start at byte {start} but end at byte {end}"
                    ),
                })
        };

        let forward = header.complex_restriction_forward_offset.get();
        let reverse = header.complex_restriction_reverse_offset.get();
        let edge_info = header.edge_info_offset.get();
        let text_list = header.text_list_offset.get();
        let lane_connectivity = header.lane_connectivity_offset.get();
        let lane_connectivity_end = header.lane_connectivity_end();
        // The counted speed records must start within the declared tile.
        section_size(
            "predicted speeds",
            lane_connectivity_end,
            header.tile_size.get(),
        )?;

        Ok(Self {
            forward_restrictions: section_size("forward restrictions", forward, reverse)?,
            reverse_restrictions: section_size("reverse restrictions", reverse, edge_info)?,
            edge_info: section_size("edge info records", edge_info, text_list)?,
            text_list: section_size("text records", text_list, lane_connectivity)?,
            lane_connectivity: section_size(
                "lane connectivity records",
                lane_connectivity,
                lane_connectivity_end,
            )?,
        })
    }
}

impl GraphTileHeader {
    /// The full Graph ID of this tile.
    #[inline]
    pub const fn graph_id(&self) -> GraphId {
        // SAFETY: We know that the bit field cannot contain a value
        // larger than the max allowed value (it's limited to 46 bits).
        unsafe { GraphId::from_id_unchecked(self.bit_field_1.graph_id()) }
    }

    /// The relative road density within this tile (0-15).
    #[inline]
    pub const fn density(&self) -> u8 {
        self.bit_field_1.density()
    }

    /// The date this tile was created.
    #[inline]
    pub fn create_date(&self) -> DateTime<Utc> {
        VALHALLA_EPOCH + TimeDelta::days(i64::from(self.create_date.get()))
    }

    /// Does this tile include elevation data?
    #[inline]
    pub const fn has_elevation(&self) -> bool {
        self.bit_field_1.has_elevation() != 0
    }

    /// Does this tile include extended directed edge attributes?
    ///
    /// If true, read one extended directed edge for every regular directed edge.
    #[inline]
    pub const fn has_ext_directed_edge(&self) -> bool {
        self.bit_field_1.has_ext_directed_edge() != 0
    }

    /// The coordinate of the southwest corner of this graph tile.
    #[inline]
    pub const fn sw_corner(&self) -> Coord<f32> {
        coord! {x: self.base_lon_lat[0].get(), y: self.base_lon_lat[1].get()}
    }

    /// Gets the writer version used to generate this graph tile.
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

    /// The size (in units) occupied by the edge bins structure.
    #[inline]
    pub const fn edge_bins_count(&self) -> usize {
        self.bin_offsets[BIN_COUNT - 1].get() as usize
    }

    pub(super) fn with_expansion_offsets_from(
        mut self,
        source: &Self,
        opaque_suffix_size: usize,
    ) -> Result<Self, GraphTileBuildError> {
        if opaque_suffix_size != 0 && self.tile_size != source.tile_size {
            // Opaque data may contain absolute references into the original tile.
            return Err(GraphTileBuildError::WouldShiftOpaqueData {
                offset: source.tile_size.get() as usize - opaque_suffix_size,
            });
        }
        // Rewrites keep the existing sections in place.
        // Only the older sentinel moves when the tile grows,
        // because older writers used the tile end for absent sections.
        self.bounding_circle_offset = source.bounding_circle_offset;
        self.expansion_offsets = source.expansion_offsets;
        for offset in
            core::iter::once(&mut self.bounding_circle_offset).chain(&mut self.expansion_offsets)
        {
            if *offset == source.tile_size {
                *offset = self.tile_size;
            }
        }
        Ok(self)
    }

    /// Splits the remaining tile bytes after the edge bins at the forward restrictions offset.
    pub(super) fn split_bin_extensions<'a>(
        &self,
        bytes: &'a [u8],
        edge_bins_end: usize,
    ) -> Result<(&'a [u8], &'a [u8]), GraphTileDecodingError> {
        let forward = self.complex_restriction_forward_offset.get() as usize;
        let Some(size) = forward.checked_sub(edge_bins_end) else {
            return Err(GraphTileDecodingError::CastError {
                field: "edge_bin_extensions".to_string(),
                error_description: format!(
                    "forward restrictions start at byte {forward} before the edge bins end at byte {edge_bins_end}"
                ),
            });
        };

        let (extensions, remaining) = bytes.split_at_checked(size).ok_or_else(|| {
            GraphTileDecodingError::CastError {
                field: "edge_bin_extensions".to_string(),
                error_description: format!(
                    "the extension section requires {size} bytes, but only {} remain after the edge bins",
                    bytes.len()
                ),
            }
        })?;

        let circles = self.bounding_circle_offset.get();
        if circles != 0 && circles != self.tile_size.get() {
            let circle_size = self.edge_bins_count() * size_of::<U32<LE>>();
            let circle_tail = (circles as usize)
                .checked_sub(edge_bins_end)
                .and_then(|start| extensions.get(start..));
            if circle_tail.is_none_or(|tail| tail.len() < circle_size) {
                return Err(GraphTileDecodingError::CastError {
                    field: "bounding_circles".to_string(),
                    error_description: format!(
                        "section at byte {circles} does not fit between the edge bins and forward restrictions"
                    ),
                });
            }
        }
        Ok((extensions, remaining))
    }

    /// Gets the start and end offset for the given bin index.
    /// This offset can be used to index into the array of edge IDs in the `GraphTile` struct.
    ///
    /// The returned tuple is in `(start, end)` order.
    /// The end index is "one past the end" (the start of the next bin).
    ///
    /// # Panics
    ///
    /// Panics if the bin index is illegal (25 or greater).
    #[inline]
    pub const fn edge_bin_offsets(&self, bin_index: usize) -> (usize, usize) {
        assert!(bin_index < BIN_COUNT, "Invalid bin index");
        let start = if bin_index == 0 {
            0usize
        } else {
            self.bin_offsets[bin_index - 1].get() as usize
        };
        let end = self.bin_offsets[bin_index].get() as usize;
        (start, end)
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
        (self.lane_connectivity_end() - self.lane_connectivity_offset.get()) as usize
    }

    const fn lane_connectivity_end(&self) -> u32 {
        if self.predicted_speeds_count() > 0 {
            self.predicted_speeds_offset.get()
        } else {
            self.tile_size.get()
        }
    }

    /// The bytes between the end of the counted speed records and the declared tile end.
    pub(super) fn opaque_suffix_size(&self) -> Result<usize, GraphTileDecodingError> {
        let profile_count = self.predicted_speeds_count() as usize;
        if profile_count == 0 {
            return Ok(0);
        }

        let offsets_size = self.directed_edge_count() as usize * size_of::<u32>();
        let profiles_size = profile_count * size_of::<[i16; COEFFICIENT_COUNT]>();
        let predicted_size = offsets_size + profiles_size;
        let predicted_start = self.predicted_speeds_offset.get() as usize;
        let tile_end = self.tile_size.get() as usize;
        if predicted_start > tile_end || predicted_size > tile_end - predicted_start {
            return Err(GraphTileDecodingError::CastError {
                field: "predicted_speeds".to_string(),
                error_description: format!(
                    "the {predicted_size}-byte speed block at byte {predicted_start} exceeds the declared tile end at byte {tile_end}"
                ),
            });
        }
        Ok(tile_end - predicted_start - predicted_size)
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
    fn test_parse_header_l2() {
        let tile = &*TEST_GRAPH_TILE_L2;

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(tile.header());
        }
    }
}
