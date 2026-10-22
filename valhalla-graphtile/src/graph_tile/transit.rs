//! # Transit data structures
//!
//! These records are in transit (level 3) tiles.
//! Text offsets point into the text list of the same tile.
//! Raw enum values (such as the route type) use the numbering in Valhalla's
//! [`graphconstants.h`](https://github.com/valhalla/valhalla/blob/b77d5987ed13562454681fc06a81b39d33d97abf/valhalla/baldr/graphconstants.h).

use bitfield_struct::bitfield;
use core::fmt;
use zerocopy::{LE, U16, U32, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

const FIXED_DEPARTURE_TYPE: u8 = 0;

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct DepartureFirstBitfield {
    #[bits(20, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    line_id: U32<LE>,
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    route_index: U16<LE>,
    #[bits(32, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    trip_id: U32<LE>,
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct DepartureSecondBitfield {
    #[bits(20, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    block_id: U32<LE>,
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    schedule_index: U16<LE>,
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    headsign_offset: U32<LE>,
    #[bits(2)]
    departure_type: u8,
    #[bits(1)]
    wheelchair_accessible: u8,
    #[bits(1)]
    bicycle_accessible: u8,
    #[bits(4)]
    _spare: u8,
}

/// The departure times of a [`TransitDeparture`].
///
/// A fixed departure uses only `departure_time`,
/// and stores its elapsed time in the bits of `end_time`.
#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct DepartureTimes {
    #[bits(17, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    departure_time: U32<LE>,
    #[bits(17, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    end_time: U32<LE>,
    #[bits(13, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    frequency: U16<LE>,
    #[bits(17, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    frequency_elapsed_time: U32<LE>,
}

/// A scheduled departure of a transit line from a stop.
///
/// All times are in seconds.
/// Departure and end times count from midnight local time.
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Clone)]
#[repr(C)]
pub struct TransitDeparture {
    first_bitfield: DepartureFirstBitfield,
    second_bitfield: DepartureSecondBitfield,
    departure_times: DepartureTimes,
}

impl TransitDeparture {
    /// Gets the line ID.
    ///
    /// A line is a unique pair of a route and a destination stop.
    #[inline]
    pub const fn line_id(&self) -> u32 {
        self.first_bitfield.line_id().get()
    }

    /// Gets the index of the route in the [`TransitRoute`] list of the tile.
    #[inline]
    pub const fn route_index(&self) -> u16 {
        self.first_bitfield.route_index().get()
    }

    /// Gets the internal trip ID.
    #[inline]
    pub const fn trip_id(&self) -> u32 {
        self.first_bitfield.trip_id().get()
    }

    /// Gets the block ID.
    #[inline]
    pub const fn block_id(&self) -> u32 {
        self.second_bitfield.block_id().get()
    }

    /// Gets the index of the [`TransitSchedule`] in the tile
    /// that tells on which days this departure is valid.
    #[inline]
    pub const fn schedule_index(&self) -> u16 {
        self.second_bitfield.schedule_index().get()
    }

    /// Gets the offset of the headsign in the text list of the tile.
    #[inline]
    pub const fn headsign_offset(&self) -> u32 {
        self.second_bitfield.headsign_offset().get()
    }

    /// Gets the raw departure type (0 = fixed, 1 = frequency).
    ///
    /// A fixed departure leaves at one time.
    /// A frequency departure leaves at an interval from the departure time to the end time.
    #[inline]
    pub const fn departure_type(&self) -> u8 {
        self.second_bitfield.departure_type()
    }

    /// Can a wheelchair use this departure?
    #[inline]
    pub const fn wheelchair_accessible(&self) -> bool {
        self.second_bitfield.wheelchair_accessible() != 0
    }

    /// Can a passenger take a bicycle on this departure?
    #[inline]
    pub const fn bicycle_accessible(&self) -> bool {
        self.second_bitfield.bicycle_accessible() != 0
    }

    /// Gets the departure time.
    ///
    /// For a frequency departure, this is the time of the first departure.
    #[inline]
    pub const fn departure_time(&self) -> u32 {
        self.departure_times.departure_time().get()
    }

    /// Gets the time from the departure to the arrival at the next stop.
    #[inline]
    pub const fn elapsed_time(&self) -> u32 {
        if self.departure_type() == FIXED_DEPARTURE_TYPE {
            self.departure_times.end_time().get()
        } else {
            self.departure_times.frequency_elapsed_time().get()
        }
    }

    /// Gets the time of the last departure.
    ///
    /// Returns `None` for a fixed departure.
    #[inline]
    pub const fn end_time(&self) -> Option<u32> {
        if self.departure_type() == FIXED_DEPARTURE_TYPE {
            None
        } else {
            Some(self.departure_times.end_time().get())
        }
    }

    /// Gets the interval between departures.
    ///
    /// Returns `None` for a fixed departure.
    #[inline]
    pub const fn frequency(&self) -> Option<u16> {
        if self.departure_type() == FIXED_DEPARTURE_TYPE {
            None
        } else {
            Some(self.departure_times.frequency().get())
        }
    }
}

// The frequency bits of a fixed departure can hold stale data,
// so the output shows only the fields of the departure type.
impl fmt::Debug for TransitDeparture {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut debug = f.debug_struct("TransitDeparture");
        debug
            .field("line_id", &self.line_id())
            .field("route_index", &self.route_index())
            .field("trip_id", &self.trip_id())
            .field("block_id", &self.block_id())
            .field("schedule_index", &self.schedule_index())
            .field("headsign_offset", &self.headsign_offset())
            .field("departure_type", &self.departure_type())
            .field("wheelchair_accessible", &self.wheelchair_accessible())
            .field("bicycle_accessible", &self.bicycle_accessible())
            .field("departure_time", &self.departure_time())
            .field("elapsed_time", &self.elapsed_time());
        if let (Some(end_time), Some(frequency)) = (self.end_time(), self.frequency()) {
            debug
                .field("end_time", &end_time)
                .field("frequency", &frequency);
        }
        debug.finish()
    }
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct StopBitfield {
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    one_stop_offset: U32<LE>,
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    name_offset: U32<LE>,
    #[bits(1)]
    generated: u8,
    #[bits(2)]
    traversability: u8,
    #[bits(13)]
    _spare: u16,
}

/// A transit stop.
///
/// Each node in a transit tile has one stop.
/// The stop index of a node is in [`NodeInfo::transition_index`](super::NodeInfo::transition_index).
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Clone)]
#[repr(C)]
pub struct TransitStop {
    bitfield: StopBitfield,
}

impl TransitStop {
    /// Gets the offset of the stop ID (a Onestop ID) in the text list of the tile.
    #[inline]
    pub const fn one_stop_offset(&self) -> u32 {
        self.bitfield.one_stop_offset().get()
    }

    /// Gets the offset of the stop name in the text list of the tile.
    #[inline]
    pub const fn name_offset(&self) -> u32 {
        self.bitfield.name_offset().get()
    }

    /// Did the tile builder make this stop (and not the transit feed)?
    #[inline]
    pub const fn generated(&self) -> bool {
        self.bitfield.generated() != 0
    }

    /// Gets the raw traversability value (0 = none, 1 = forward, 2 = backward, 3 = both).
    #[inline]
    pub const fn traversability(&self) -> u8 {
        self.bitfield.traversability()
    }
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct RouteFirstBitfield {
    #[bits(8)]
    route_type: u8,
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    one_stop_offset: U32<LE>,
    #[bits(32)]
    _spare: u32,
}

/// A pair of text offsets in one 64-bit word.
#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct RouteOffsetPair {
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    first: U32<LE>,
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    second: U32<LE>,
    #[bits(16)]
    _spare: u16,
}

/// A transit route.
///
/// All offsets point into the text list of the tile.
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Clone)]
#[repr(C)]
pub struct TransitRoute {
    route_color: U32<LE>,
    route_text_color: U32<LE>,
    first_bitfield: RouteFirstBitfield,
    /// The operator Onestop ID and the operator name.
    operator_offsets: RouteOffsetPair,
    /// The operator website and the short route name.
    website_and_short_name_offsets: RouteOffsetPair,
    /// The long route name and the route description.
    long_name_and_description_offsets: RouteOffsetPair,
}

impl TransitRoute {
    /// Gets the route color as `0xRRGGBB`.
    #[inline]
    pub const fn route_color(&self) -> u32 {
        self.route_color.get()
    }

    /// Gets the route text color as `0xRRGGBB`.
    #[inline]
    pub const fn route_text_color(&self) -> u32 {
        self.route_text_color.get()
    }

    /// Gets the raw route type.
    ///
    /// The value is a Valhalla `TransitType` (0 = tram, 1 = metro, 2 = rail, 3 = bus,
    /// 4 = ferry, 5 = cable car, 6 = gondola, 7 = funicular).
    #[inline]
    pub const fn route_type(&self) -> u8 {
        self.first_bitfield.route_type()
    }

    /// Gets the offset of the route Onestop ID.
    #[inline]
    pub const fn one_stop_offset(&self) -> u32 {
        self.first_bitfield.one_stop_offset().get()
    }

    /// Gets the offset of the Onestop ID of the operator.
    #[inline]
    pub const fn operator_one_stop_offset(&self) -> u32 {
        self.operator_offsets.first().get()
    }

    /// Gets the offset of the operator name.
    #[inline]
    pub const fn operator_name_offset(&self) -> u32 {
        self.operator_offsets.second().get()
    }

    /// Gets the offset of the operator website.
    #[inline]
    pub const fn operator_website_offset(&self) -> u32 {
        self.website_and_short_name_offsets.first().get()
    }

    /// Gets the offset of the short route name.
    #[inline]
    pub const fn short_name_offset(&self) -> u32 {
        self.website_and_short_name_offsets.second().get()
    }

    /// Gets the offset of the long route name.
    #[inline]
    pub const fn long_name_offset(&self) -> u32 {
        self.long_name_and_description_offsets.first().get()
    }

    /// Gets the offset of the route description.
    #[inline]
    pub const fn description_offset(&self) -> u32 {
        self.long_name_and_description_offsets.second().get()
    }
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct ScheduleBitfield {
    #[bits(7)]
    days_of_week: u8,
    #[bits(6)]
    end_day: u8,
    #[bits(51)]
    _spare: u64,
}

/// The days on which a group of departures is valid.
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Clone)]
#[repr(C)]
pub struct TransitSchedule {
    days: U64<LE>,
    bitfield: ScheduleBitfield,
}

impl TransitSchedule {
    /// Gets the bit mask of valid days.
    ///
    /// Bit `n` is for the day `n` days after the creation date of the tile.
    #[inline]
    pub const fn days(&self) -> u64 {
        self.days.get()
    }

    /// Gets the bit mask of valid days of the week.
    ///
    /// Bit 0 is Sunday and bit 6 is Saturday.
    #[inline]
    pub const fn days_of_week(&self) -> u8 {
        self.bitfield.days_of_week()
    }

    /// Gets the last day in [`days`](Self::days) that has data.
    #[inline]
    pub const fn end_day(&self) -> u8 {
        self.bitfield.end_day()
    }
}

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct TransferBitfield {
    #[bits(4)]
    transfer_type: u8,
    #[bits(16, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    min_time: U16<LE>,
    #[bits(12)]
    _spare: u16,
}

/// A transfer between two stops.
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Clone)]
#[repr(C)]
pub struct TransitTransfer {
    from_stop_id: U32<LE>,
    to_stop_id: U32<LE>,
    bitfield: TransferBitfield,
}

impl TransitTransfer {
    /// Gets the internal ID of the stop where the transfer starts.
    #[inline]
    pub const fn from_stop_id(&self) -> u32 {
        self.from_stop_id.get()
    }

    /// Gets the internal ID of the stop where the transfer ends.
    #[inline]
    pub const fn to_stop_id(&self) -> u32 {
        self.to_stop_id.get()
    }

    /// Gets the raw transfer type (0 = recommended, 1 = timed, 2 = minimum time,
    /// 3 = not possible).
    #[inline]
    pub const fn transfer_type(&self) -> u8 {
        self.bitfield.transfer_type()
    }

    /// Gets the minimum transfer time in seconds.
    #[inline]
    pub const fn min_time(&self) -> u16 {
        self.bitfield.min_time().get()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::size_of;
    use zerocopy::FromBytes;

    #[test]
    fn test_record_sizes() {
        assert_eq!(size_of::<TransitDeparture>(), 24);
        assert_eq!(size_of::<TransitStop>(), 8);
        assert_eq!(size_of::<TransitRoute>(), 40);
        assert_eq!(size_of::<TransitSchedule>(), 16);
        assert_eq!(size_of::<TransitTransfer>(), 12);
    }

    fn departure_from_words(words: [u64; 3]) -> TransitDeparture {
        let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        TransitDeparture::read_from_bytes(&bytes).expect("Invalid departure bytes")
    }

    #[test]
    fn test_fixed_departure() {
        let (line_id, route_index, trip_id): (u64, u64, u64) = (7, 11, 123_456);
        let first = line_id | (route_index << 20) | (trip_id << 32);
        let (block_id, schedule_index, headsign_offset): (u64, u64, u64) = (5, 3, 99);
        let second = block_id | (schedule_index << 20) | (headsign_offset << 32) | (0b11 << 58);
        // The spare bits (34 to 63) are set to make sure that no accessor reads them.
        let (departure_time, elapsed_time): (u64, u64) = (28_800, 120);
        let times = departure_time | (elapsed_time << 17) | (u64::MAX << 34);
        let departure = departure_from_words([first, second, times]);

        assert_eq!(departure.line_id(), 7);
        assert_eq!(departure.route_index(), 11);
        assert_eq!(departure.trip_id(), 123_456);
        assert_eq!(departure.block_id(), 5);
        assert_eq!(departure.schedule_index(), 3);
        assert_eq!(departure.headsign_offset(), 99);
        assert_eq!(departure.departure_type(), FIXED_DEPARTURE_TYPE);
        assert!(departure.wheelchair_accessible());
        assert!(departure.bicycle_accessible());
        assert_eq!(departure.departure_time(), 28_800);
        assert_eq!(departure.elapsed_time(), 120);
        assert_eq!(departure.end_time(), None);
        assert_eq!(departure.frequency(), None);
    }

    #[test]
    fn test_frequency_departure() {
        let second = 1 << 56;
        let (departure_time, end_time, frequency, elapsed_time): (u64, u64, u64, u64) =
            (32_400, 43_200, 900, 150);
        let times = departure_time | (end_time << 17) | (frequency << 34) | (elapsed_time << 47);
        let departure = departure_from_words([0, second, times]);

        assert_eq!(departure.departure_type(), 1);
        assert!(!departure.wheelchair_accessible());
        assert!(!departure.bicycle_accessible());
        assert_eq!(departure.departure_time(), 32_400);
        assert_eq!(departure.elapsed_time(), 150);
        assert_eq!(departure.end_time(), Some(43_200));
        assert_eq!(departure.frequency(), Some(900));
    }
}
