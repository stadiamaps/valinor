use crate::Access;
use bitfield_struct::bitfield;
use enumset::EnumSet;
use zerocopy::{LE, U16, U32, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, TryFromBytes, Unaligned};

/// Types of access restrictions.
#[derive(TryFromBytes, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum AccessRestrictionType {
    Hazmat,
    MaxHeight,
    MaxWidth,
    MaxLength,
    MaxWeight,
    MaxAxleLoad,
    TimedAllowed,
    TimedDenied,
    DestinationAllowed,
    MaxAxles,
    // Valhalla docs say the max supported value is 31,
    // but the field looks 6 bits wide to me, not 5.
}

impl AccessRestrictionType {
    const fn into_bits(self) -> u8 {
        self as _
    }
    const fn from_bits(value: u8) -> Self {
        // FIXME: This is hackish
        match value {
            0 => AccessRestrictionType::Hazmat,
            1 => AccessRestrictionType::MaxHeight,
            2 => AccessRestrictionType::MaxWidth,
            3 => AccessRestrictionType::MaxLength,
            4 => AccessRestrictionType::MaxWeight,
            5 => AccessRestrictionType::MaxAxleLoad,
            6 => AccessRestrictionType::TimedAllowed,
            7 => AccessRestrictionType::TimedDenied,
            8 => AccessRestrictionType::DestinationAllowed,
            9 => AccessRestrictionType::MaxAxles,
            _ => panic!(
                "Invalid AccessRestriction. As far as I can tell, this crate doesn't support failable ops."
            ),
        }
    }
}

#[bitfield(u64,
    repr = U64<LE>,
    from = bit_twiddling_helpers::conv_u64le::from_inner,
    into = bit_twiddling_helpers::conv_u64le::into_inner
)]
#[derive(PartialEq, Eq, FromBytes, IntoBytes, Immutable, Unaligned)]
struct AccessRestrictionBitField {
    #[bits(22, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    edge_index: U32<LE>,
    #[bits(6)]
    restriction_type: AccessRestrictionType,
    #[bits(12, from = bit_twiddling_helpers::conv_u16le::from_inner, into = bit_twiddling_helpers::conv_u16le::into_inner)]
    modes: U16<LE>,
    #[bits(24)]
    _spare: U32<LE>,
}

/// Access restrictions beyond the usual access tags
#[derive(PartialEq, Eq, FromBytes, IntoBytes, Immutable, Unaligned, Debug, Clone)]
#[repr(C)]
pub struct AccessRestriction {
    bitfield: AccessRestrictionBitField,
    value: U64<LE>,
}

impl AccessRestriction {
    /// Gets the edge index (within the tile) to which the restriction applies.
    #[inline]
    pub fn edge_index(&self) -> u32 {
        self.bitfield.edge_index().get()
    }

    /// Gets the type of access restriction.
    #[inline]
    pub fn restriction_type(&self) -> AccessRestrictionType {
        self.bitfield.restriction_type()
    }

    /// The access modes affected by this restriction.
    #[inline]
    pub fn affected_access_modes(&self) -> EnumSet<Access> {
        // TODO: Look at ways to do this with FromBytes; this currently copies
        // SAFETY: The access bits are length 12, so invalid representations are impossible.
        unsafe { EnumSet::from_repr_unchecked(self.bitfield.modes().get()) }
    }
}

#[cfg(test)]
mod tests {
    use super::{Access, AccessRestrictionType};
    use crate::graph_tile::{GraphTile, TEST_GRAPH_TILE_L0};
    use enumset::EnumSet;

    #[test]
    fn test_parse_access_restrictions_count() {
        let tile = &*TEST_GRAPH_TILE_L0;
        let tile_view = tile.borrow_dependent();

        assert_eq!(
            tile_view.access_restrictions.len(),
            tile.header().access_restriction_count() as usize
        );
    }

    #[test]
    fn test_parse_access_restrictions() {
        let tile = &*TEST_GRAPH_TILE_L0;
        let tile_view = tile.borrow_dependent();

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(
                "first_access_restriction",
                tile_view.access_restrictions[0]
            );
        }

        assert_eq!(
            tile_view.access_restrictions[0].restriction_type(),
            AccessRestrictionType::MaxWeight
        );
        assert_eq!(
            tile_view.access_restrictions[0].affected_access_modes(),
            EnumSet::from(Access::Truck)
        );

        if !cfg!(miri) {
            insta::assert_debug_snapshot!(
                "last_access_restriction",
                tile_view.access_restrictions.last().unwrap()
            );
        }

        // TODO: Other sanity checks after we add some more advanced methods
    }
}
