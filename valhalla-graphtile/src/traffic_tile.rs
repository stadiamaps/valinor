//! # Traffic tile support
//!
//! This module provides data structures for working with Valhalla live traffic tiles.
//! These follow a different format from the routing graph.

use bitfield_struct::bitfield;
use thiserror::Error;
use zerocopy::{FromBytes, LE, U32, U64, transmute};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

/// The bit-level reperesentation signaling that the live speed is not known
/// (max value of a 7-bit number)
const UNKNOWN_TRAFFIC_SPEED_RAW: u8 = (1 << 7) - 1;

/// The maximum allowable traffic speed
// const MAX_TRAFFIC_SPEED_KPH: u32 = (UNKNOWN_TRAFFIC_SPEED_RAW - 1) << 1;

/// The value (in kph) that signifies a traffic speed is unknown
// const UNKNOWN_TRAFFIC_SPEED_KPH: u32 = UNKNOWN_TRAFFIC_SPEED_RAW << 1;

const UNKNOWN_CONGESTION_VAL: u8 = 0;
const MAX_CONGESTION_VAL: u8 = 63;

/// The Valhalla traffic tile version.
/// See the note on the `traffic_tile_version` field.
/// In Valhalla, this is currently tied to the Valhalla major version.
const TRAFFIC_TILE_VERSION: u8 = 3;

#[derive(Debug, Error)]
pub enum TrafficTileDecodingError {
    #[error("Unable to extract a slice of the correct length; the tile data is malformed.")]
    SliceArrayConversion(#[from] std::array::TryFromSliceError),
    #[error("Unable to extract a slice of the correct length; the tile data is malformed.")]
    SliceLength,
    #[error("The byte sequence is not valid for this type.")]
    ByteSequenceValidityError,
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
}

/// The header for a traffic tile.
///
/// Every tile starts off with one of these.
#[derive(FromBytes, IntoBytes, Unaligned)]
#[repr(C)]
pub struct TrafficTileHeader {
    tile_id: U64<LE>,
    /// The last update date, in seconds since the epoch.
    last_update: U64<LE>,
    directed_edge_count: U32<LE>,
    /// An indicative version number of the traffic tile format.
    ///
    /// This is *not* intended to allow for easy migration between incompatible data formats.
    /// Changes are still expected to be applied in a backward-compatible way by using
    /// the spare bits available.
    ///
    /// This is more of a break-the-glass escape hatch for when the current format has
    /// reached its limits.
    traffic_tile_version: U32<LE>,
    // The traffic tile version used to be in the spare1 field ages ago.
    // I've kept the naming here to remain consistent with Valhalla.
    _spare2: U32<LE>,
    _spare3: U32<LE>,
}

impl TrafficTileHeader {
    pub fn directed_edge_count(&self) -> u32 {
        self.directed_edge_count.get()
    }
}

/// Traffic speeds over an edge.
///
/// This structure allows for an edge to be divided into up to 3 smaller segments
/// with more granular detail.
#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
pub struct TrafficSpeed {
    // The overall speed, with a representable range of 0-255 kph, in 2kph increments.
    #[bits(7)]
    overall_encoded_speed: u8,
    // Segment encoded speeds, which divide the edge into (up to) 3 segments.
    // These use the same 0-255kph range with 2kph increments
    #[bits(7)]
    encoded_speed1: u8,
    #[bits(7)]
    encoded_speed2: u8,
    #[bits(7)]
    encoded_speed3: u8,
    // Breakpoints. The position = length * (breakpointN / 255)
    #[bits(8)]
    breakpoint1: u8,
    #[bits(8)]
    breakpoint2: u8,
    // Congestion info per segment.
    // 0 = unknown
    // 1 = no congestion
    // 63 = max congestion
    #[bits(6)]
    congestion1: u8,
    #[bits(6)]
    congestion2: u8,
    #[bits(6)]
    congestion3: u8,
    // Are there incidents on this edge in the corresponding incident tile?
    #[bits(1)]
    has_incidents: u8,
    #[bits(1)]
    _spare: u8,
}

// FIXME: These APIs are straight ports, but they kinda suck.
impl TrafficSpeed {
    /// Returns true if the edge has a valid speed value.
    #[inline]
    pub const fn has_valid_speed(&self) -> bool {
        self.breakpoint1() != 0 && self.overall_encoded_speed() != UNKNOWN_TRAFFIC_SPEED_RAW
    }

    /// Gets the overall speed, in kph.
    ///
    /// Returns `None` if no speed value is encoded for this edge.
    #[inline]
    pub const fn overall_speed(&self) -> Option<u8> {
        if self.has_valid_speed() {
            Some(self.overall_encoded_speed() << 1)
        } else {
            None
        }
    }

    /// Gets the speed for a sub-segment in kph.
    ///
    /// Returns `None` if no speed value is encoded for the given segment.
    ///
    /// # Panics
    ///
    /// Panics if `segment_index` is greater than 2.
    #[inline]
    pub const fn segment_speed(&self, segment_index: u8) -> Option<u8> {
        if !self.has_valid_speed() {
            return None;
        }

        match segment_index {
            0 => Some(self.encoded_speed1() << 1),
            1 => Some(self.encoded_speed2() << 1),
            2 => Some(self.encoded_speed3() << 1),
            _ => panic!("Illegal segment index; must be less than 3"),
        }
    }

    /// Returns true if the edge is totally closed.
    ///
    /// Note that it may be partially closed, so check [`TrafficSpeed::is_segment_closed`] too!
    #[inline]
    pub const fn is_completely_closed(&self) -> bool {
        self.breakpoint1() != 0 && self.overall_encoded_speed() != UNKNOWN_TRAFFIC_SPEED_RAW
    }

    /// Returns true if a specific segment is closed.
    ///
    /// Note that it may be partially closed, so check [`TrafficSpeed::is_completely_closed`] too!
    ///
    /// # Panics
    ///
    /// Panics if `segment_index` is greater than 2.
    #[inline]
    pub const fn is_segment_closed(&self, segment_index: u8) -> bool {
        if !self.has_valid_speed() {
            return false;
        }

        match segment_index {
            0 => self.encoded_speed1() == 0 || self.congestion1() == MAX_CONGESTION_VAL,
            1 => {
                self.breakpoint1() < 255
                    && (self.encoded_speed2() == 0 || self.congestion2() == MAX_CONGESTION_VAL)
            }
            2 => {
                self.breakpoint2() < 255
                    && (self.encoded_speed3() == 0 || self.congestion3() == MAX_CONGESTION_VAL)
            }
            _ => panic!("Illegal segment index; must be less than 3"),
        }
    }
}

#[cfg(test)]
mod test {
    use std::mem::transmute;
    use crate::traffic_tile::TrafficSpeed;
    use zerocopy::{transmute, IntoBytes};

    #[test]
    fn test_round_trip() {
        const DESIRED_SPEED: u8 = 42;

        let speed = TrafficSpeed::new()
            .with_overall_encoded_speed(DESIRED_SPEED >> 1)
            .with_breakpoint1(255)
            .with_has_incidents(1);

        let speed_as_bytes = speed.as_bytes();
        assert_eq!(
            speed_as_bytes,
            [DESIRED_SPEED >> 1, 0, 0, 240, 15, 0, 0, 64]
        );
        let speed_as_u64 = speed.into_bits().get();
        assert_eq!(speed_as_u64.to_le_bytes(), speed_as_bytes);

        let mut x: u64 = 0;
        let ptr = &mut x as *mut u64;

        let round_tripped_speed: TrafficSpeed = unsafe {
            // Explicit LE write
            core::ptr::write(ptr, speed_as_u64.to_le());
            // Simulates a read from the memory map
            std::ptr::read_volatile(ptr as *const TrafficSpeed)
        };

        assert_eq!(round_tripped_speed.has_valid_speed(), true);
        assert_eq!(round_tripped_speed.overall_speed(), Some(DESIRED_SPEED));
        assert_eq!(round_tripped_speed.breakpoint1(), 255);
        assert_eq!(round_tripped_speed.has_incidents(), 1);
    }
}
