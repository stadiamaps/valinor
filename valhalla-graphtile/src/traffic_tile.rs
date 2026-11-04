//! # Traffic tile support
//!
//! This module provides data structures for working with Valhalla live traffic tiles.
//! These follow a different format from the routing graph.

use crate::traffic_tile::TrafficSpeedBuilderError::{SectionLengthExceedsEdge, TooManySegments};
use bitfield_struct::bitfield;
use nutype::nutype;
#[cfg(feature = "serde")]
use serde::{Serialize, Serializer, ser::SerializeStruct};
use thiserror::Error;
use zerocopy::{LE, U32, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

/// The bit-level representation signaling that the live speed is not known
/// (max value of a 7-bit number)
const UNKNOWN_TRAFFIC_SPEED_RAW: u8 = (1 << 7) - 1;
const UNKNOWN_TRAFFIC_SPEED_KPH: u8 = UNKNOWN_TRAFFIC_SPEED_RAW << 1;

/// The maximum allowed traffic speed, in kph.
///
/// Values larger than this are reserved, so you should cap speeds here.
pub const MAX_TRAFFIC_SPEED_KPH: u8 = (UNKNOWN_TRAFFIC_SPEED_RAW - 1) << 1;

/// The bit-level representation signaling that the road is closed
const CLOSED_TRAFFIC_SPEED_RAW: u8 = 0;

pub const UNKNOWN_CONGESTION_VAL: u8 = 0;
pub const MAX_CONGESTION_VAL: u8 = 63;

/// The Valhalla traffic tile version.
/// See the note on the `traffic_tile_version` field.
/// In Valhalla, this is currently tied to the Valhalla major version.
pub const TRAFFIC_TILE_VERSION: u32 = 3;

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

    /// Gets the traffic tile version number.
    ///
    /// This is currently tied to the Valhalla major version number,
    /// and can be verified against [`TRAFFIC_TILE_VERSION`] to ensure that we understand the file.
    pub fn traffic_tile_version(&self) -> u32 {
        self.traffic_tile_version.get()
    }
}

/// A measurement of moving vehicle speed.
/// Use this when the road is not closed.
///
/// # Examples
///
/// ```
/// # use valhalla_graphtile::traffic_tile::{SpeedValue, MAX_TRAFFIC_SPEED_KPH};
/// let valid_speed = SpeedValue::try_new(42).expect("This is a valid value");
/// assert!(SpeedValue::try_new(0).is_err(), "Zero is a reserved value (use closed helpers on TrafficSpeed and TrafficSpeedBuilder).");
/// assert!(SpeedValue::try_new(MAX_TRAFFIC_SPEED_KPH + 1).is_err(), "Values above this speed are reserved.");
/// ```
///
/// # Indicating closed segments
///
/// Values must be non-zero. To indicate a closed segment,
/// use helpers like [`TrafficSpeed::closed`] or [`TrafficSpeedBuilder::with_closed_segment`]
#[cfg_attr(feature = "serde", nutype(const_fn, derive(Copy, Clone, Eq, PartialEq, Debug, Serialize, Deserialize), validate(greater=0, less_or_equal=MAX_TRAFFIC_SPEED_KPH)))]
#[cfg_attr(not(feature = "serde"), nutype(const_fn, derive(Copy, Clone, Eq, PartialEq, Debug), validate(greater=0, less_or_equal=MAX_TRAFFIC_SPEED_KPH)))]
pub struct SpeedValue(u8);

impl SpeedValue {
    /// Converts the speed value in kph to the encoded format for storage in a traffic tile.
    ///
    /// The encoding uses 7 bits of precision and quantizes to a resolution of 2kph.
    pub const fn into_encoded_value(self) -> u8 {
        self.into_inner() >> 1
    }
}

/// A measure of congestion along a segment.
/// Use this to indicate a known congestion level.
///
/// # Examples
///
/// ```
/// # use valhalla_graphtile::traffic_tile::{CongestionValue, MAX_CONGESTION_VAL};
/// let valid_congestion = CongestionValue::try_new(1).expect("This is the minimum allowed value");
/// assert!(CongestionValue::try_new(0).is_err(), "Zero is a reserved value (None signifies unknown congestion in the TrafficSpeed and TrafficSpeedBuilder)");
/// assert!(CongestionValue::try_new(MAX_CONGESTION_VAL + 1).is_err(), "Values above this are not supported");
/// ```
#[cfg_attr(feature = "serde", nutype(const_fn, derive(Copy, Clone, Eq, PartialEq, Debug, Serialize, Deserialize), validate(greater=0, less_or_equal=MAX_CONGESTION_VAL)))]
#[cfg_attr(not(feature = "serde"), nutype(const_fn, derive(Copy, Clone, Eq, PartialEq, Debug), validate(greater=0, less_or_equal=MAX_CONGESTION_VAL)))]
pub struct CongestionValue(u8);

/// The traffic conditions along a single segment in a traffic tile.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize))]
pub enum SegmentTrafficInfo {
    /// There is no data for this segment.
    ///
    /// If the breakpoint is 0 or 255, this also indicates there is no data for any future segment.
    NoData { breakpoint: u8 },
    /// The segment is closed.
    Closed { breakpoint: u8 },
    /// Traffic is flowing at the given speed.
    Speed {
        /// The traffic speed in kph.
        speed_kph: u8,
        /// An optional congestion value ranging from 1 to 63.
        congestion: Option<u8>,
        /// The breakpoint along the edge.
        ///
        /// This is a value between 1 and 255, where 255 is the end of the edge.
        breakpoint: u8,
    },
}

/// Traffic speeds over an edge.
///
/// This stores speed and optional congestion and incident information for a single edge in the graph.
/// For long edges with variable traffic conditions (e.g., motorways),
/// this structure allows breaking the edge up into 3 segments,
/// each with their own speed and congestion info.
#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq, Eq)]
pub struct TrafficSpeed {
    /// The overall speed, with a representable range of 0-255 kph, in 2kph increments.
    /// This is stored as a convenience to keep the pathfinding loop tight.
    /// (When traversing an entire edge, it just uses the overall speed
    /// and doesn't need to compute from the individual sections.)
    ///
    /// Magic values:
    /// * 0 - road closed
    /// * 127 (the max 7-bit number = 255 if it were a real speed) - unknown speed
    ///
    /// This value is assumed to be invalid (unknown speed) if `breakpoint1` is 0.
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
    /// Returns true if the edge has valid speed information.
    /// NB: This information may indicate that the road is closed!
    #[inline]
    pub const fn has_valid_speed(&self) -> bool {
        self.breakpoint1() != 0 && self.overall_encoded_speed() != UNKNOWN_TRAFFIC_SPEED_RAW
    }

    /// Gets the overall speed (the weighted average speed when traversing the full edge), in kph.
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

    /// Gets the traffic flow information for a segment within the tile.
    /// Use this when traversing only part of the segment.
    ///
    /// # Panics
    ///
    /// Panics if `segment_index` is greater than 2.
    #[inline]
    pub const fn segment_info(&self, segment_index: u8) -> SegmentTrafficInfo {
        let (raw, breakpoint, congestion) = match segment_index {
            0 => (
                self.encoded_speed1(),
                self.breakpoint1(),
                self.congestion1(),
            ),
            1 => (
                self.encoded_speed2(),
                self.breakpoint2(),
                self.congestion2(),
            ),
            2 => (
                self.encoded_speed3(),
                if self.breakpoint2() != 0 && self.breakpoint2() != 255 {
                    255
                } else {
                    0
                },
                self.congestion3(),
            ),
            _ => panic!("Illegal segment index; must be less than 3"),
        };

        if breakpoint == 0 || raw == UNKNOWN_TRAFFIC_SPEED_RAW {
            SegmentTrafficInfo::NoData { breakpoint }
        } else if raw == CLOSED_TRAFFIC_SPEED_RAW {
            SegmentTrafficInfo::Closed { breakpoint }
        } else {
            SegmentTrafficInfo::Speed {
                speed_kph: raw << 1,
                congestion: match congestion {
                    UNKNOWN_CONGESTION_VAL => None,
                    value => Some(value),
                },
                breakpoint,
            }
        }
    }

    /// Returns true if the edge is completely closed.
    ///
    /// Note that this does not mean all segments are passable!
    /// See [`TrafficSpeed::is_segment_closed`] to get segment-level detail.
    ///
    /// TODO: I'm still a bit fuzzy on the validity of partial closures.
    /// See `test_builder_no_data_and_closure_edge_case` for documentation of at least one edge case.
    #[inline]
    pub const fn is_completely_closed(&self) -> bool {
        self.breakpoint1() != 0 && self.overall_encoded_speed() == CLOSED_TRAFFIC_SPEED_RAW
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
            0 => {
                self.encoded_speed1() == CLOSED_TRAFFIC_SPEED_RAW
                    || self.congestion1() == MAX_CONGESTION_VAL
            }
            1 => {
                self.breakpoint1() < 255
                    && self.breakpoint1() > 0
                    && (self.encoded_speed2() == CLOSED_TRAFFIC_SPEED_RAW
                        || self.congestion2() == MAX_CONGESTION_VAL)
            }
            2 => {
                self.breakpoint2() < 255
                    && self.breakpoint2() > 0
                    && (self.encoded_speed3() == CLOSED_TRAFFIC_SPEED_RAW
                        || self.congestion3() == MAX_CONGESTION_VAL)
            }
            _ => panic!("Illegal segment index; must be less than 3"),
        }
    }

    // Builder methods

    /// Constructs a new [`TrafficSpeed`] where a single speed is applied to the entire edge.
    ///
    /// For more complex cases where you want to break the edge up into segments
    /// with different speeds, use [`TrafficSpeedBuilder`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use valhalla_graphtile::traffic_tile::{CongestionValue, SpeedValue, TrafficSpeed};
    /// let speed = SpeedValue::try_new(42).expect("This is a valid speed");
    /// let tile_with_speed = TrafficSpeed::single_speed(speed, None);
    /// let tile_with_congestion = TrafficSpeed::single_speed(speed, Some(CongestionValue::try_new(12).expect("This should be a valid moderate congestion value")));
    /// ```
    #[inline]
    pub const fn single_speed(speed: SpeedValue, congestion: Option<CongestionValue>) -> Self {
        let encoded_speed = speed.into_encoded_value();
        Self::new()
            .with_overall_encoded_speed(encoded_speed)
            .with_encoded_speed1(encoded_speed)
            .with_congestion1(match congestion {
                None => 0,
                Some(congestion) => congestion.into_inner(),
            })
            .with_breakpoint1(255)
    }

    /// Constructs a new [`TrafficSpeed`] indicating that the entire edge is closed.
    ///
    /// For more complex cases where you want to break the edge up so it's only partially closed,
    /// use [`TrafficSpeedBuilder`].
    #[inline]
    pub const fn closed() -> Self {
        Self::new()
            .with_overall_encoded_speed(CLOSED_TRAFFIC_SPEED_RAW)
            .with_breakpoint1(255)
    }

    /// Returns a new instance indicating that there is an incident tile containing this edge.
    #[inline]
    #[must_use]
    pub const fn with_incident_tile_bit(self) -> Self {
        self.with_has_incidents(1)
    }
}

#[cfg(feature = "serde")]
impl Serialize for TrafficSpeed {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let num_fields = 7;
        let mut state = serializer.serialize_struct("TrafficSpeed", num_fields)?;

        state.serialize_field("has_valid_speed", &self.has_valid_speed())?;
        state.serialize_field("is_completely_closed", &self.is_completely_closed())?;
        state.serialize_field("overall_speed", &self.overall_speed())?;
        state.serialize_field("segment_info_0", &self.segment_info(0))?;
        state.serialize_field("segment_info_1", &self.segment_info(1))?;
        state.serialize_field("segment_info_2", &self.segment_info(2))?;
        state.serialize_field("has_incident_tile", &self.has_incidents())?;

        state.end()
    }
}

#[derive(Error, Debug)]
pub enum TrafficSpeedBuilderError {
    #[error(
        "At least one segment is required, but there were no segments in the traffic speed builder"
    )]
    NoSegments,
    #[error("Tried to add too many segments (the max is 3)")]
    TooManySegments,
    #[error(
        "Section lengths would total longer than the underlying edge: {current_length} (current length) + {new_section_length} (new length) > {edge_length} (edge length)"
    )]
    SectionLengthExceedsEdge {
        current_length: u32,
        new_section_length: u32,
        edge_length: u32,
    },
    #[error(
        "Section lengths are shorter than the underlying edge; you should specify unknown regions explicitly"
    )]
    IncompleteCoverage,
}

/// An incremental builder interface for [`TrafficSpeed`].
///
/// This builder does the work of transforming speed information into the Valhalla format,
/// and enforces that the lengths add up and you stay within the Valhalla constraints.
///
/// # Examples
///
/// You can use this builder to  mark an entire edge as either a single speed or completely closed,
/// but the [`TrafficSpeed::single_speed`] or [`TrafficSpeed::closed`] constructors
/// may be more convenient.
///
/// ```
/// # use valhalla_graphtile::traffic_tile::{TrafficSpeedBuilder, TrafficSpeed, SpeedValue};
/// const DESIRED_SPEED: u8 = 42;
/// // You can build a speed like this.
/// // Many steps are failable, so you'll get quick feedback when you try to do something illegal.
/// let built_speed = TrafficSpeedBuilder::with_edge_length(9000)
///     .with_speed_segment(SpeedValue::try_new(DESIRED_SPEED).unwrap(), None, 9000).unwrap()
///     .build().unwrap();
///
/// // If you're creating a single value that covers the whole edge,
/// // this is probably an easier method.
/// let speed = TrafficSpeed::single_speed(SpeedValue::try_new(DESIRED_SPEED).unwrap(), None);
/// assert_eq!(built_speed, speed);
/// ```
pub struct TrafficSpeedBuilder {
    edge_length: u32,
    // (speed, congestion, length) tuples
    speeds: Vec<(u8, u8, u32)>,
}

impl TrafficSpeedBuilder {
    /// Constructs a new builder for an edge of the given length (in meters).
    pub fn with_edge_length(edge_length: u32) -> Self {
        Self {
            edge_length,
            speeds: Vec::with_capacity(3),
        }
    }

    fn test_can_add_segment_of_length(&self, length: u32) -> Result<(), TrafficSpeedBuilderError> {
        if self.speeds.len() == 3 {
            return Err(TooManySegments);
        }

        let current_length = self.current_length();
        if current_length + length > self.edge_length {
            return Err(SectionLengthExceedsEdge {
                current_length,
                new_section_length: length,
                edge_length: self.edge_length,
            });
        }

        Ok(())
    }

    /// Adds a new segment to the builder with traffic flowing at some non-zero rate.
    ///
    /// The congestion information is optional;
    /// a `None` value indicates unknown/missing data.
    /// Use a value of 1 to indicate no congestion.
    ///
    /// # Errors
    ///
    /// This will fail under the following conditions:
    ///
    /// - The `length` makes the accumulated total greater than the edge length
    /// - There are already 3 segments (Valhalla limit)
    pub fn with_speed_segment(
        self,
        speed: SpeedValue,
        congestion: Option<CongestionValue>,
        length: u32,
    ) -> Result<Self, TrafficSpeedBuilderError> {
        self.test_can_add_segment_of_length(length)?;
        let mut speeds = self.speeds;

        let congestion = match congestion {
            Some(value) => value.into_inner(),
            None => UNKNOWN_CONGESTION_VAL,
        };

        speeds.push((speed.into_inner(), congestion, length));
        Ok(Self { speeds, ..self })
    }

    /// Adds a new segment to the builder where traffic is completely stationary or the road is closed.
    ///
    /// # Errors
    ///
    /// This will fail under the following conditions:
    ///
    /// - The `length` makes the accumulated total greater than the edge length
    /// - There are already 3 segments (Valhalla limit)
    pub fn with_closed_segment(self, length: u32) -> Result<Self, TrafficSpeedBuilderError> {
        self.test_can_add_segment_of_length(length)?;
        let mut speeds = self.speeds;

        speeds.push((CLOSED_TRAFFIC_SPEED_RAW, UNKNOWN_CONGESTION_VAL, length));
        Ok(Self { speeds, ..self })
    }

    pub fn with_unknown_segment(self, length: u32) -> Result<Self, TrafficSpeedBuilderError> {
        self.test_can_add_segment_of_length(length)?;
        let mut speeds = self.speeds;

        speeds.push((UNKNOWN_TRAFFIC_SPEED_KPH, UNKNOWN_CONGESTION_VAL, length));
        Ok(Self { speeds, ..self })
    }

    /// The length of segments added so far (in meters).
    pub fn current_length(&self) -> u32 {
        self.speeds.iter().map(|(_, _, length)| length).sum()
    }

    /// Creates a [`TrafficSpeed`] from the builder.
    pub fn build(self) -> Result<TrafficSpeed, TrafficSpeedBuilderError> {
        if self.speeds.is_empty() {
            return Err(TrafficSpeedBuilderError::NoSegments);
        }

        let len = self.current_length();
        if len < self.edge_length {
            return Err(TrafficSpeedBuilderError::IncompleteCoverage);
        }

        // Compute a weighted average overall speed.
        // The fold computes the numerator as the sum of `speed * len`,
        // and the denominator as the total length covered.
        let (num, denom) = self
            .speeds
            .iter()
            .fold((0, 0), |(acc_s, acc_l), (speed, _, len)| {
                if *speed == UNKNOWN_TRAFFIC_SPEED_KPH {
                    // Don't accumulate unknown sections
                    (acc_s, acc_l)
                } else {
                    (acc_s + (u32::from(*speed) * len), acc_l + len)
                }
            });

        if denom == 0 {
            // This is a bit special; this can only happen if the entire area is marked as unknown.
            // This is valid, so we return a blank speed tile.
            return Ok(TrafficSpeed::default());
        }

        let overall_speed = (num / denom) as u8;

        let mut result = TrafficSpeed::new().with_overall_encoded_speed(overall_speed >> 1);

        // Loop over segments
        let mut acc_seg_len = 0;
        for (idx, (segment_speed, congestion, segment_len)) in self.speeds.into_iter().enumerate() {
            acc_seg_len += segment_len;
            let encoded_speed = segment_speed >> 1;

            // breakpointN = acc_seg_len / self.edge_length.... but in the range 0-255!
            let breakpoint = normalize_progress(acc_seg_len, self.edge_length);

            match idx {
                0 => {
                    result = result
                        .with_encoded_speed1(encoded_speed)
                        .with_congestion1(congestion)
                        .with_breakpoint1(breakpoint);
                }
                1 => {
                    result = result
                        .with_encoded_speed2(encoded_speed)
                        .with_congestion2(congestion)
                        .with_breakpoint2(breakpoint);
                }
                2 => {
                    result = result
                        .with_encoded_speed3(encoded_speed)
                        .with_congestion3(congestion);
                }
                _ => unreachable!(
                    "Should never hit this, as we ensure that builder methods fail when adding too many segments."
                ),
            }
        }

        Ok(result)
    }
}

/// Helper that normalizes progress along the edge into the range (0, 255).
#[inline]
fn normalize_progress(pos: u32, len: u32) -> u8 {
    assert!(pos <= len, "Invalid progress {pos} must be <= length {len}");
    if len == 0 {
        // Prevent division by zero
        return 0;
    }

    // Scale 0..len into 0..255
    ((u64::from(pos) * 255) / u64::from(len)) as u8
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::proptest;
    use zerocopy::IntoBytes;

    #[test]
    fn test_traffic_speed_round_trip() {
        const DESIRED_SPEED: u8 = 42;

        let speed = TrafficSpeed::single_speed(SpeedValue::try_new(DESIRED_SPEED).unwrap(), None)
            .with_incident_tile_bit();

        let speed_as_bytes = speed.as_bytes();
        assert_eq!(speed_as_bytes, [149, 10, 0, 240, 15, 0, 0, 64]);
        let speed_as_u64 = speed.into_bits().get();
        assert_eq!(speed_as_u64.to_le_bytes(), speed_as_bytes);

        let mut x: u64 = 0;
        let ptr = &mut x as *mut u64;

        let round_tripped_speed: TrafficSpeed = unsafe {
            // Explicit LE write
            core::ptr::write(ptr, speed_as_u64.to_le());
            // Simulates a read from the memory map
            core::ptr::read_volatile(ptr as *const TrafficSpeed)
        };

        assert_eq!(round_tripped_speed.has_valid_speed(), true);
        assert_eq!(round_tripped_speed.overall_speed(), Some(DESIRED_SPEED));
        assert_eq!(round_tripped_speed.breakpoint1(), 255);
        assert_eq!(round_tripped_speed.has_incidents(), 1);
    }

    #[test]
    fn test_builder_two_segments() {
        let speed = TrafficSpeedBuilder::with_edge_length(1000)
            // The first half of the edge is moving at 42kph with light congestion
            .with_speed_segment(
                SpeedValue::try_new(42).unwrap(),
                Some(CongestionValue::try_new(12).unwrap()),
                500,
            )
            .unwrap()
            // Higher speed now with less congestion
            .with_speed_segment(
                SpeedValue::try_new(86).unwrap(),
                Some(CongestionValue::try_new(1).unwrap()),
                500,
            )
            .unwrap()
            .build()
            .unwrap();

        assert!(!speed.is_completely_closed());
        // The overall speed will be in the middle
        assert_eq!(speed.overall_speed(), Some(64));

        assert_eq!(
            speed.segment_info(0),
            SegmentTrafficInfo::Speed {
                speed_kph: 42,
                congestion: Some(12),
                breakpoint: 127,
            }
        );
        assert_eq!(
            speed.segment_info(1),
            SegmentTrafficInfo::Speed {
                speed_kph: 86,
                congestion: Some(1),
                breakpoint: 255,
            }
        );
        assert_eq!(
            speed.segment_info(2),
            SegmentTrafficInfo::NoData {
                breakpoint: 0, // This segment doesn't exist
            }
        );

        // No segments are closed
        assert!(!speed.is_segment_closed(0));
        assert!(!speed.is_segment_closed(1));
        assert!(!speed.is_segment_closed(2));

        assert_eq!(speed.as_bytes(), &[160, 202, 10, 240, 247, 207, 4, 0]);
    }

    #[test]
    fn test_builder_two_segments_partial_closure() {
        let speed = TrafficSpeedBuilder::with_edge_length(1000)
            // The first half of the edge is moving at 42kph with light congestion
            .with_speed_segment(
                SpeedValue::try_new(42).unwrap(),
                Some(CongestionValue::try_new(12).unwrap()),
                500,
            )
            .unwrap()
            .with_closed_segment(500)
            .unwrap()
            .build()
            .unwrap();

        assert!(!speed.is_completely_closed());
        // The overall speed will be ~half (quantization error means we can't represent odd values)
        assert_eq!(speed.overall_speed(), Some(20));

        assert_eq!(
            speed.segment_info(0),
            SegmentTrafficInfo::Speed {
                speed_kph: 42,
                congestion: Some(12),
                breakpoint: 127,
            }
        );
        assert_eq!(
            speed.segment_info(1),
            SegmentTrafficInfo::Closed { breakpoint: 255 }
        );
        assert_eq!(
            speed.segment_info(2),
            SegmentTrafficInfo::NoData {
                breakpoint: 0, // This segment doesn't exist
            }
        );

        // The first segment is open, but the second segment (index 1) is closed
        assert!(!speed.is_segment_closed(0));
        assert!(speed.is_segment_closed(1));
        assert!(!speed.is_segment_closed(2));

        assert_eq!(speed.as_bytes(), &[138, 10, 0, 240, 247, 207, 0, 0]);
    }

    #[test]
    fn test_builder_three_segments() {
        let speed = TrafficSpeedBuilder::with_edge_length(1000)
            // The first half of the edge is moving at 42kph with light congestion
            .with_speed_segment(
                SpeedValue::try_new(42).unwrap(),
                Some(CongestionValue::try_new(12).unwrap()),
                500,
            )
            .unwrap()
            // Higher speed now with less congestion
            .with_speed_segment(
                SpeedValue::try_new(86).unwrap(),
                Some(CongestionValue::try_new(1).unwrap()),
                250,
            )
            .unwrap()
            // And a third segment for good measure...
            .with_speed_segment(
                SpeedValue::try_new(34).unwrap(),
                Some(CongestionValue::try_new(47).unwrap()),
                250,
            )
            .unwrap()
            .build()
            .unwrap();

        assert!(!speed.is_completely_closed());
        // The overall speed will be in the middle
        assert_eq!(speed.overall_speed(), Some(50));

        assert_eq!(
            speed.segment_info(0),
            SegmentTrafficInfo::Speed {
                speed_kph: 42,
                congestion: Some(12),
                breakpoint: 127,
            }
        );
        assert_eq!(
            speed.segment_info(1),
            SegmentTrafficInfo::Speed {
                speed_kph: 86,
                congestion: Some(1),
                breakpoint: 191,
            }
        );
        assert_eq!(
            speed.segment_info(2),
            SegmentTrafficInfo::Speed {
                speed_kph: 34,
                congestion: Some(47),
                breakpoint: 255,
            }
        );

        // No segments are closed
        assert!(!speed.is_segment_closed(0));
        assert!(!speed.is_segment_closed(1));
        assert!(!speed.is_segment_closed(2));

        assert_eq!(speed.as_bytes(), &[153, 202, 42, 242, 247, 203, 4, 47]);
    }

    #[test]
    fn test_builder_no_data() {
        let speed = TrafficSpeedBuilder::with_edge_length(1000)
            .with_unknown_segment(1000)
            .unwrap()
            .build()
            .unwrap();

        assert_eq!(speed, TrafficSpeed::default());
    }

    #[test]
    fn test_builder_partial_no_data() {
        let speed = TrafficSpeedBuilder::with_edge_length(1000)
            .with_unknown_segment(500)
            .unwrap()
            // .with_closed_segment(500)
            .with_speed_segment(SpeedValue::try_new(42).unwrap(), None, 500)
            .unwrap()
            .build()
            .unwrap();

        assert_eq!(
            speed.segment_info(0),
            SegmentTrafficInfo::NoData { breakpoint: 127 }
        );
        assert_eq!(
            speed.segment_info(1),
            SegmentTrafficInfo::Speed {
                speed_kph: 42,
                congestion: None,
                breakpoint: 255,
            }
        );
        assert_eq!(
            speed.segment_info(2),
            SegmentTrafficInfo::NoData { breakpoint: 0 }
        );
    }

    #[test]
    fn test_builder_no_data_and_closure_edge_case() {
        let speed = TrafficSpeedBuilder::with_edge_length(1000)
            .with_unknown_segment(500)
            .unwrap()
            .with_closed_segment(500)
            .unwrap()
            .build()
            .unwrap();

        // As the Valhalla logic is currently written,
        // such an edge is marked as closed since the first breakpoint is nonzero
        // but the overall edge speed is zero.
        // Detecting this scenario in the builder and setting the overall speed to "unknown"
        // would render the entire tile as not having valid speed (so it's just ignored as if there were no data).
        // That's not quite right either ;)
        // This is a bit of an edge case in Valhalla IMO.
        // This unit test documents the current, somewhat confusing behavior.
        assert!(speed.is_completely_closed());
        assert_eq!(
            speed.segment_info(0),
            SegmentTrafficInfo::NoData { breakpoint: 127 }
        );
        assert_eq!(
            speed.segment_info(1),
            SegmentTrafficInfo::Closed { breakpoint: 255 }
        );
        assert_eq!(
            speed.segment_info(2),
            SegmentTrafficInfo::NoData { breakpoint: 0 }
        );
    }

    proptest! {
        #[test]
        fn prop_zero_progress_is_always_zero(len: u32) {
            assert_eq!(normalize_progress(0, len), 0);
        }

        #[test]
        fn prop_progress_eq_nonzero_len_is_max(value in 1u32..) {
            assert_eq!(normalize_progress(value, value), 255);
        }
    }
}
