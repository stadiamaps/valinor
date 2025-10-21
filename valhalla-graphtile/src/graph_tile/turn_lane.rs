use bitfield_struct::bitfield;
use zerocopy::{LE, U32};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

#[bitfield(u32,
    repr = U32<LE>,
    from = bit_twiddling_helpers::conv_u32le::from_inner,
    into = bit_twiddling_helpers::conv_u32le::into_inner
)]
#[derive(FromBytes, IntoBytes, Immutable, Unaligned)]
struct EdgeIndex {
    #[bits(22, from = bit_twiddling_helpers::conv_u32le::from_inner, into = bit_twiddling_helpers::conv_u32le::into_inner)]
    edge_index: U32<LE>,
    #[bits(10)]
    _spare: U16<LE>,
}

#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, Clone)]
#[repr(C)]
pub struct TurnLane {
    edge_index: EdgeIndex,
    /// The offset into the graph tile text list
    /// which contains the text for this turn lane.
    pub text_offset: U32<LE>,
}

/// Holds turn lane information at the end of a directed edge.
///
/// Turn lane text is stored in the graph tile text list
/// and the offset is stored within the [`TurnLane`] structure.
impl TurnLane {
    /// Gets the index (within the same tile) of the directed edge that this sign applies to.
    #[inline]
    pub const fn directed_edge_index(&self) -> u32 {
        self.edge_index.edge_index().get()
    }
}

#[cfg(test)]
mod tests {
    use crate::graph_tile::{GraphTile, TEST_GRAPH_TILE_L0};

    #[test]
    fn test_parse_turn_lane_count() {
        let tile = &*TEST_GRAPH_TILE_L0;
        let tile_view = tile.borrow_dependent();

        assert_eq!(
            tile_view.turn_lanes.len(),
            tile.header().turn_lane_count() as usize
        );
    }

    #[test]
    fn test_parse_turn_lanes() {
        let tile = &*TEST_GRAPH_TILE_L0;
        let tile_view = tile.borrow_dependent();

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!(tile_view.turn_lanes);
        }
    }
}
