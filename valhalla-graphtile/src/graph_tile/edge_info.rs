use crate::{AsCowStr, BicycleNetwork, graph_tile::GraphTileError, shape_codec::decode_shape};
use bitfield_struct::bitfield;
use enumset::EnumSet;
use geo::LineString;
use std::borrow::Cow;
use std::cell::OnceCell;
use zerocopy::{FromBytes, LE, U16, U32, transmute};
use zerocopy_derive::{FromBytes, Immutable, Unaligned};

#[cfg(feature = "serde")]
use serde::{Serialize, Serializer, ser::SerializeStruct};

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, Immutable, Unaligned)]
pub struct NameInfo {
    #[bits(24, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    name_offset: U32<LE>,
    /// Additional fields following the name.
    ///
    /// These can be used for additional information like phonetic readings.
    #[bits(4)]
    additional_fields: u8,
    #[bits(1)]
    is_route_num: u8,
    /// Indicates the string is specially tagged (ex: uses the first char as the tag type).
    ///
    /// This doesn't have any relation to OSM tagging.
    #[bits(1)]
    is_tagged: u8,
    #[bits(2)]
    _spare: u8,
}

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, Immutable, Unaligned)]
struct FirstInnerBitfield {
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    mean_elevation: U16<LE>,
    #[bits(4)]
    bike_network: u8,
    #[bits(8)]
    speed_limit: u8,
    #[bits(8)]
    extended_way_id: u8,
}

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, Immutable, Unaligned)]
struct SecondInnerBitfield {
    #[bits(4)]
    name_count: u8,
    #[bits(16, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    encoded_shape_size: U16<LE>,
    #[bits(8)]
    extended_way_id: u8,
    #[bits(2)]
    extended_way_id_size: u8,
    #[bits(1)]
    has_elevation: u8,
    #[bits(1)]
    _spare: u8,
}

#[derive(Debug, FromBytes, Immutable, Unaligned)]
#[repr(C)]
struct EdgeInfoInner {
    // The first part of the OSM way ID
    // TODO: would be nice to reshuffle this in v4.0
    way_id: U32<LE>,
    first_inner_bitfield: FirstInnerBitfield,
    second_inner_bitfield: SecondInnerBitfield,
}

#[derive(Debug)]
pub struct EdgeInfo<'a> {
    inner: EdgeInfoInner,
    name_info_list: &'a [NameInfo],
    /// The raw varint-encoded shape bytes.
    pub encoded_shape: &'a [u8],
    // Last 2 bytes of the 64-bit way ID
    extended_way_id_2: u8,
    extended_way_id_3: u8,
    decoded_shape: OnceCell<LineString<f64>>,
    // TODO: Encoded elevation (pointer?)
    text_list_memory: &'a [u8],
    // TODO: Tag cache
}

impl EdgeInfo<'_> {
    /// Gets the tagged speed limit along this edge (in kph).
    #[inline]
    pub const fn speed_limit(&self) -> u8 {
        self.inner.first_inner_bitfield.speed_limit()
    }

    /// Gets the shape of the edge geometry as a [`LineString`].
    ///
    /// # Errors
    ///
    /// See [`decode_shape`] for a description of possible errors.
    ///
    /// # Performance
    ///
    /// If this [`EdgeInfo`] geometry has not been accessed previously,
    /// then it will be decoded during this method call.
    /// Subsequent fetches will be cached for as long as the `EdgeInfo`
    /// is live.
    pub fn shape(&self) -> std::io::Result<&LineString<f64>> {
        // TODO: Use https://doc.rust-lang.org/core/cell/struct.OnceCell.html#method.get_or_try_init when stabilized
        if let Some(linestring) = self.decoded_shape.get() {
            Ok(linestring)
        } else {
            let shape = decode_shape(self.encoded_shape)?;
            Ok(self.decoded_shape.get_or_init(|| shape))
        }
    }

    // TODO: Other filters (tagged and linguistic filters)
    /// Gets all names for this edge.
    ///
    /// # Performance
    ///
    /// This is mostly just pointer indirection and some light filtering.
    /// Not great to call in a hot loop, but also not doing a lot of heavy processing.
    /// The main thing to be careful of in hot paths is allocations.
    pub fn get_names(&self) -> Vec<Cow<'_, str>> {
        self.name_info_list
            .iter()
            .filter_map(|ni| {
                // FIXME: Methods
                // No, this is not a bug...
                if ni.is_tagged() == 0 {
                    Some(self.text_list_memory[ni.name_offset().get() as usize..].as_cow_str())
                } else {
                    None
                }
            })
            .collect()
    }

    /// The bicycle network membership mask for this edge.
    #[inline]
    pub fn bicycle_network(&self) -> EnumSet<BicycleNetwork> {
        // TODO: Look at ways to do this with FromBytes; this currently copies
        // Safety: The access bits are length 4, so invalid representations are impossible.
        unsafe { EnumSet::from_repr_unchecked(self.inner.first_inner_bitfield.bike_network()) }
    }

    /// The way ID of the edge.
    #[inline]
    pub fn way_id(&self) -> u64 {
        u64::from(self.extended_way_id_3) << 56
            | u64::from(self.extended_way_id_2) << 48
            | u64::from(self.inner.second_inner_bitfield.extended_way_id()) << 40
            | u64::from(self.inner.first_inner_bitfield.extended_way_id()) << 32
            | u64::from(self.inner.way_id)
    }
}

// TODO: Feels like this could be a macro
impl<'a> TryFrom<(&'a [u8], &'a [u8])> for EdgeInfo<'a> {
    type Error = GraphTileError;

    fn try_from((bytes, text_list_memory): (&'a [u8], &'a [u8])) -> Result<Self, Self::Error> {
        const INNER_SIZE: usize = size_of::<EdgeInfoInner>();
        let inner_slice: [u8; INNER_SIZE] = (bytes[0..INNER_SIZE]).try_into()?;
        let inner: EdgeInfoInner = transmute!(inner_slice);

        let (name_info_list, bytes) = <[NameInfo]>::ref_from_prefix_with_elems(
            &bytes[INNER_SIZE..],
            inner.second_inner_bitfield.name_count() as usize,
        )
        .map_err(|e| GraphTileError::CastError(e.to_string()))?;

        let offset = 0;
        let (encoded_shape, offset) = {
            let end = offset + inner.second_inner_bitfield.encoded_shape_size().get() as usize;
            (&bytes[offset..end], end)
        };

        // Maybe read a byte; the data structure on disk is tightly packed
        // and drops bytes when possible in exchange for bits that are otherwise unused.
        let (extended_way_id_2, offset) = if inner.second_inner_bitfield.extended_way_id_size() > 0
        {
            (bytes[offset], offset + 1)
        } else {
            (0, offset)
        };

        let (extended_way_id_3, _offset) = if inner.second_inner_bitfield.extended_way_id_size() > 1
        {
            (bytes[offset], offset + 1)
        } else {
            (0, offset)
        };

        // TODO: Elevation

        Ok(Self {
            inner,
            name_info_list,
            encoded_shape,
            extended_way_id_2,
            extended_way_id_3,
            decoded_shape: OnceCell::new(),
            text_list_memory,
        })
    }
}

#[cfg(feature = "serde")]
impl Serialize for EdgeInfo<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let num_fields = 4;

        let speed_limit = self.speed_limit();
        let num_fields = if speed_limit == 0 {
            num_fields - 1
        } else {
            num_fields
        };

        let names = self.get_names().join(" / ");
        let num_fields = if names.is_empty() {
            num_fields - 1
        } else {
            num_fields
        };

        let mut state = serializer.serialize_struct("EdgeInfo", num_fields)?;
        if !names.is_empty() {
            state.serialize_field("names", &names)?;
        }

        state.serialize_field(
            "bike_network",
            &self
                .bicycle_network()
                .iter()
                .map(|v| v.as_char())
                .collect::<String>(),
        )?;

        if speed_limit != 0 {
            state.serialize_field("speed_limit", &self.speed_limit())?;
        }

        state.serialize_field("way_id", &self.way_id())?;

        // TODO: elevation

        state.end()
    }
}
