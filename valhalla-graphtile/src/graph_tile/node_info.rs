use crate::Access;
use bitfield_struct::bitfield;
use enumset::EnumSet;
use geo::{coord, Coord};
use zerocopy_derive::FromBytes;

const NODE_ELEVATION_PRECISION: f32 = 0.25;
const MIN_ELEVATION: f32 = -500.0;
// Max number of edges on the local level
const MAX_LOCAL_EDGE_INDEX: u8 = 7;
const HEADING_EXPAND_FACTOR: f32 = 359f32 / 255f32;

#[derive(FromBytes)]
#[bitfield(u64)]
struct FirstBitfield {
    #[bits(22)]
    lat_offset: u32,
    #[bits(4)]
    lat_offset7: u8,
    #[bits(22)]
    lon_offset: u32,
    #[bits(4)]
    lon_offset7: u8,
    #[bits(12)]
    access: u16,
}

#[derive(FromBytes)]
#[bitfield(u64)]
struct SecondBitfield {
    #[bits(21)]
    edge_index: u32,
    #[bits(7)]
    edge_count: u8,
    #[bits(12)]
    admin_index: u16,
    #[bits(9)]
    time_zone_index: u16,
    #[bits(4)]
    intersection_type: u8,
    #[bits(4)]
    node_type: u8,
    #[bits(4)]
    density: u8,
    // Booleans represented this way for infailability.
    // See comment in node_info.rs for details.
    #[bits(1)]
    is_traffic_signal: u8,
    #[bits(1)]
    mode_change_allowed: u8,
    #[bits(1)]
    is_named_intersection: u8,
}

#[derive(FromBytes)]
#[bitfield(u64)]
struct ThirdBitfield {
    #[bits(21)]
    transition_index: u32,
    #[bits(3)]
    transition_count: u8,
    #[bits(16)]
    local_driveability: u16,
    #[bits(3)]
    local_edge_count: u8,
    // Booleans represented this way for infailability.
    // See comment in node_info.rs for details.
    #[bits(1)]
    drive_on_right: u8,
    #[bits(1)]
    tagged_access: u8,
    #[bits(1)]
    private_access: u8,
    #[bits(1)]
    is_cash_only_toll: u8,
    #[bits(15)]
    elevation: u16,
    // For compatibility when new time zones are added
    #[bits(1)]
    time_zone_ext: u16,
    #[bits(1)]
    _spare: u8,
}

/// Information for a node within the graph.
///
/// The graph uses a forward star structure,
/// where nodes point to the first outbound directed edge,
/// and each directed edge points to the other end node of the edge.
#[repr(C)]
#[derive(FromBytes, Debug)]
pub struct NodeInfo {
    first_bit_field: FirstBitfield,
    second_bit_field: SecondBitfield,
    third_bit_field: ThirdBitfield,
    /// Heading information.
    ///
    /// # Documentation from Valhalla
    ///
    /// For non transit levels, it's the headings of up to kMaxLocalEdgeIndex+1 local edges (rounded to
    /// nearest 2 degrees)for all other levels.
    /// Sadly we need to keep this for now because it's used in map matching, otherwise we could remove it
    /// Also for transit levels (while building data only) it can be used for either the connecting way
    /// id for matching the connection point of the station to the edge or an encoded lon lat pair for
    /// the exact connection point. If the highest bit is set it's a lon lat otherwise it's a way id
    headings: u64,
}

impl NodeInfo {
    /// Gets the coordinate of the node.
    /// The data is stored as a relative offset internally,
    /// so a reference coordinate (namely the SW corner of the tile)
    /// is required to compute the absolute position.
    #[inline]
    pub fn coordinate(&self, sw_corner: Coord<f32>) -> Coord<f32> {
        // NOTE: We are trying something a bit unorthodox here and attempting to save space
        // on storage of vast numbers of coordinates.
        // We also know the sw_corner resolution doesn't require f64.
        // But we still do all the internal math in f64 for better precision.
        let lat_offset = (self.first_bit_field.lat_offset() as f64) * 1e-6f64
            + (self.first_bit_field.lat_offset7() as f64) * 1e-7f64;
        let lon_offset = (self.first_bit_field.lon_offset() as f64) * 1e-6f64
            + (self.first_bit_field.lon_offset7() as f64) * 1e-7f64;
        sw_corner + coord! {x: lon_offset as f32, y: lat_offset as f32}
    }

    /// The access mask for this node.
    #[inline]
    pub fn access(&self) -> EnumSet<Access> {
        // TODO: Look at ways to do this with FromBytes; this currently copies
        // Safety: The access bits are length 12, so invalid representations are impossible.
        unsafe { EnumSet::from_repr_unchecked(self.first_bit_field.access()) }
    }

    /// The index within the node's tile of its first outbound directed edge.
    #[inline]
    pub const fn edge_index(&self) -> u32 {
        self.second_bit_field.edge_index()
    }

    /// The number of outbound edges (on this level).
    #[inline]
    pub const fn edge_count(&self) -> u8 {
        self.second_bit_field.edge_count()
    }

    /// The index of the admin region containing this node (in the tile's admin list).
    #[inline]
    pub const fn admin_index(&self) -> u16 {
        self.second_bit_field.admin_index()
    }

    /// The node's time zone index.
    ///
    /// TODO: Valhalla doesn't document this well, and admits as such in nodeinfo.h
    #[inline]
    pub const fn time_zone_index(&self) -> u16 {
        self.second_bit_field.time_zone_index() | (self.third_bit_field.time_zone_ext() << 9)
    }

    /// The type of intersection.
    ///
    /// TODO: See graphconstants.h for values
    #[inline]
    pub const fn intersection_type(&self) -> u8 {
        self.second_bit_field.intersection_type()
    }

    /// The type of node.
    ///
    /// TODO: See graphconstants.h for values
    #[inline]
    pub const fn node_type(&self) -> u8 {
        self.second_bit_field.node_type()
    }

    /// The relative road density at the node (0 - 15).
    #[inline]
    pub const fn density(&self) -> u8 {
        self.second_bit_field.density()
    }

    /// Is there a traffic signal at this node?
    #[inline]
    pub const fn is_traffic_signal(&self) -> bool {
        self.second_bit_field.is_traffic_signal() != 0
    }

    /// Is a mode change allowed at this node?
    ///
    /// The access data tells us which modes are allowed at the node.
    /// Examples include transit stops, bike share locations, and parking locations.
    #[inline]
    pub const fn mode_change_allowed(&self) -> bool {
        self.second_bit_field.mode_change_allowed() != 0
    }

    /// Is this a named intersection?
    #[inline]
    pub const fn is_named_intersection(&self) -> bool {
        self.second_bit_field.is_named_intersection() != 0
    }

    /// The index of the first transition from this node.
    /// This index is into the `transitions` vector on
    /// [`GraphTile`](super::GraphTile).
    #[inline]
    pub const fn transition_index(&self) -> u32 {
        self.third_bit_field.transition_index()
    }

    /// The number of transitions from this node
    #[inline]
    pub const fn transition_count(&self) -> u8 {
        self.third_bit_field.transition_count()
    }

    // /// The traversability of the local directed edge given a local edge index.
    // ///
    // /// TODO: Convert this into a traversability value
    // #[inline]
    // pub const fn traversability(&self, local_edge_index: u16) -> u16 {
    //     // let s = u32::from(local_edge_index) * 2;  // 2 bits per index
    //     // static_cast<Traversability>((local_driveability_ & (3 << s)) >> s);
    //     // Traversability values are an enum with none, forward, backward, and both
    //     // defined as 0, 1, 2, and 3 respectively.
    //     // This makes them a perfect enum set with two variants forward and backward.
    //     self.third_bit_field.local_driveability()
    // }

    /// The number of regular edges across all levels.
    ///
    /// Does not include shortcut edges, transit edges, transit connections, and transition edges.
    #[inline]
    pub const fn local_edge_count(&self) -> u8 {
        // Not sure that the +1 is for, but this is how I found it in nodeinfo.h
        self.third_bit_field.local_edge_count() + 1
    }

    /// Do you drive on the right hand side of the road
    /// along edges originating at this node?
    #[inline]
    pub const fn drive_on_right(&self) -> bool {
        self.third_bit_field.drive_on_right() != 0
    }

    /// Was access information explicitly tagged?
    #[inline]
    pub const fn tagged_access(&self) -> bool {
        self.third_bit_field.tagged_access() != 0
    }

    /// Is this private access?
    #[inline]
    pub const fn private_access(&self) -> bool {
        self.third_bit_field.private_access() != 0
    }

    /// Is node a cash-only toll (booth/barrier)?
    #[inline]
    pub const fn cash_only_toll(&self) -> bool {
        self.third_bit_field.is_cash_only_toll() != 0
    }

    /// The elevation at the node (in meters).
    #[inline]
    pub fn elevation(&self) -> f32 {
        MIN_ELEVATION + (NODE_ELEVATION_PRECISION * f32::from(self.third_bit_field.elevation()))
    }

    /// Gets the heading of the local edge index,
    /// relative to North (N = 0).
    /// Valid input values are 0-7.
    ///
    /// NOTE: Headings are stored rounded to 2 degrees of precision.
    #[inline]
    pub fn heading(&self, local_edge_index: u8) -> Option<u16> {
        if local_edge_index > MAX_LOCAL_EDGE_INDEX {
            None
        } else {
            let shift = u64::from(local_edge_index) * 8;
            Some(
                (((self.headings & (255u64 << shift)) >> shift) as f32 * HEADING_EXPAND_FACTOR)
                    .round() as u16,
            )
        }
    }
}

#[cfg(test)]
mod test {
    use crate::graph_tile::TEST_GRAPH_TILE;
    use enumset::EnumSet;

    #[test]
    fn test_parse_nodes_count() {
        let tile = &*TEST_GRAPH_TILE;

        assert_eq!(tile.nodes.len(), tile.header.node_count() as usize);
    }

    #[test]
    fn test_parse_nodes() {
        let tile = &*TEST_GRAPH_TILE;

        insta::assert_debug_snapshot!(tile.nodes[0]);
        insta::assert_debug_snapshot!(tile.nodes.last().unwrap());

        // Sanity check our coordinate parsing
        let coord = tile.nodes[0].coordinate(tile.header.sw_corner());
        assert!(coord.x - 1.5008542999999999 < f32::EPSILON);
        assert!(coord.y - 42.493887200000003 < f32::EPSILON);

        // TODO: Find some examples of restricted access
        assert_eq!(tile.nodes[0].access(), EnumSet::all());

        // TODO: Test the headings
    }
}
