use bitfield_struct::bitfield;
use zerocopy::{LE, U32};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, TryFromBytes, Unaligned};

/// Holds a generic sign with type and text.
///
/// Text is stored in the graph tile text list,
/// and the offset is stored within the sign.
/// The directed edge index within the tile is also stored
/// so that signs can be found via either the directed edge or node index.
#[derive(TryFromBytes, Immutable, Unaligned, Debug)]
#[repr(u8)]
pub enum SignType {
    ExitNumber,
    ExitBranch,
    ExitToward,
    ExitName,
    GuideBranch,
    GuideToward,
    JunctionName,
    GuidanceViewJunction,
    GuidanceViewSignboard,
    TollName,
    Linguistic = 255,
}

impl SignType {
    const fn into_bits(self) -> u8 {
        self as _
    }
    const fn from_bits(value: u8) -> Self {
        // FIXME: This is hackish
        match value {
            0 => SignType::ExitNumber,
            1 => SignType::ExitBranch,
            2 => SignType::ExitToward,
            3 => SignType::ExitName,
            4 => SignType::GuideBranch,
            5 => SignType::GuideToward,
            6 => SignType::JunctionName,
            7 => SignType::GuidanceViewJunction,
            8 => SignType::GuidanceViewSignboard,
            9 => SignType::TollName,
            255 => SignType::Linguistic,
            _ => panic!(
                "Invalid Sign. As far as I can tell, this crate doesn't support failable ops."
            ),
        }
    }
}

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct SignBitField {
    #[bits(22, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    edge_or_node_index: U32<LE>,
    #[bits(8)]
    sign_type: SignType,
    #[bits(1)]
    is_route_num_type: u8,
    #[bits(1)]
    is_text_tagged: u8,
}

#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Copy, Clone)]
#[repr(C)]
pub struct Sign {
    bitfield: SignBitField,
    /// The offset into the graph tile text list
    /// which contains the text for this sign.
    pub text_offset: U32<LE>,
}

impl Sign {
    /// Gets the index (within the same tile) of the directed edge or node this sign applies to.
    #[inline]
    pub fn edge_or_node_index(&self) -> u32 {
        self.bitfield.edge_or_node_index().get()
    }

    /// Gets the type of the sign.
    /// The index (within the same tile) of the directed edge or node this sign applies to.
    #[inline]
    pub fn sign_type(&self) -> SignType {
        self.bitfield.sign_type()
    }

    /// Does this sign indicate a route number, phoneme for a node, or the guidance view type?
    ///
    /// This description copied straight from Valhalla.
    /// The description and naming have room for improvement.
    #[inline]
    pub const fn is_route_num_type(&self) -> bool {
        self.bitfield.is_route_num_type() != 0
    }

    /// Is the sign text tagged?
    #[inline]
    pub const fn is_text_tagged(&self) -> bool {
        self.bitfield.is_text_tagged() != 0
    }
}

#[cfg(test)]
mod tests {
    use crate::graph_tile::TEST_GRAPH_TILE_L0;

    #[test]
    fn test_parse_sign_count() {
        let tile = &*TEST_GRAPH_TILE_L0;
        let tile_view = tile.borrow_dependent();

        assert_eq!(
            tile_view.signs.len(),
            tile_view.header.sign_count() as usize
        );
    }

    // TODO: There aren't any signs in the test tile
}
