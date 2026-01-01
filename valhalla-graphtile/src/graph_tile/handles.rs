//! # Graph Tile Handles
//!
//! This module contains several variations of owned handles to graph tile data.
//! These can be used in cases where longer-lived access is needed.
//! Each offers different performance, flexibility, and safety tradeoffs.

use super::{
    AccessRestriction, Admin, DirectedEdge, DirectedEdgeExt, EdgeInfo, GraphTile,
    GraphTileDecodingError, GraphTileHeader, GraphTileView, LookupError, NodeInfo, NodeTransition,
    OpposingEdgeIndex,
};
use crate::{Access, GraphId};
use enumset::EnumSet;
use memmap2::MmapRaw;
use self_cell::self_cell;
use std::sync::Arc;

pub trait GraphTileHandle {
    fn tile_view(&'_ self) -> GraphTileView<'_>;
}

self_cell! {
    /// A read-only view of a Valhalla graph tile.
    ///
    /// The bytes are fully owned by the handle, and access is infallible after construction.
    pub struct OwnedGraphTileHandle {
        owner: Vec<u8>,
        #[covariant]
        dependent: GraphTileView,
    }
}

impl TryFrom<Vec<u8>> for OwnedGraphTileHandle {
    type Error = GraphTileDecodingError;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        OwnedGraphTileHandle::try_new(value, |data| GraphTileView::try_from(data.as_slice()))
    }
}

impl GraphTile for OwnedGraphTileHandle {
    #[inline]
    fn graph_id(&self) -> GraphId {
        self.borrow_dependent().graph_id()
    }

    #[inline]
    fn may_contain_id(&self, id: GraphId) -> bool {
        self.borrow_dependent().may_contain_id(id)
    }

    #[inline]
    fn header(&self) -> &GraphTileHeader {
        self.borrow_dependent().header()
    }

    #[inline]
    fn get_node(&self, id: GraphId) -> Result<&NodeInfo, LookupError> {
        self.borrow_dependent().get_node(id)
    }

    #[inline]
    fn get_outbound_edges_from_node(&self, node_info: &NodeInfo) -> &[DirectedEdge] {
        self.borrow_dependent()
            .get_outbound_edges_from_node(node_info)
    }

    #[inline]
    fn get_transitions(&self, node: &NodeInfo) -> &[NodeTransition] {
        self.borrow_dependent().get_transitions(node)
    }

    #[inline]
    fn get_directed_edge(&self, id: GraphId) -> Result<&DirectedEdge, LookupError> {
        self.borrow_dependent().get_directed_edge(id)
    }

    #[inline]
    fn get_opp_edge_index(&self, graph_id: GraphId) -> Result<OpposingEdgeIndex, LookupError> {
        self.borrow_dependent().get_opp_edge_index(graph_id)
    }

    #[inline]
    fn get_ext_directed_edge(&self, id: GraphId) -> Result<&DirectedEdgeExt, LookupError> {
        self.borrow_dependent().get_ext_directed_edge(id)
    }

    #[inline]
    fn get_access_restrictions(
        &self,
        directed_edge_index: u32,
        access_modes: EnumSet<Access>,
    ) -> Vec<&AccessRestriction> {
        self.borrow_dependent()
            .get_access_restrictions(directed_edge_index, access_modes)
    }

    #[inline]
    fn get_predicted_speed(
        &self,
        directed_edge_index: usize,
        seconds_from_start_of_week: u32,
    ) -> Option<f32> {
        self.borrow_dependent()
            .get_predicted_speed(directed_edge_index, seconds_from_start_of_week)
    }

    #[inline]
    fn get_edge_info(
        &self,
        directed_edge: &DirectedEdge,
    ) -> Result<EdgeInfo<'_>, GraphTileDecodingError> {
        self.borrow_dependent().get_edge_info(directed_edge)
    }

    #[inline]
    fn directed_edges(&self) -> &[DirectedEdge] {
        self.borrow_dependent().directed_edges()
    }

    #[inline]
    fn nodes(&self) -> &[NodeInfo] {
        self.borrow_dependent().nodes
    }

    #[inline]
    fn admins(&self) -> &[Admin] {
        self.borrow_dependent().admins()
    }

    #[inline]
    fn edges_in_bin(&self, bin_index: usize) -> &[GraphId] {
        self.borrow_dependent().edges_in_bin(bin_index)
    }

    #[inline]
    fn bin_index_xy(&self, x: usize, y: usize) -> usize {
        self.borrow_dependent().bin_index_xy(x, y)
    }
}

self_cell! {
    /// A read-only view of a graph tile backed by a memory-mapped pointer.
    pub struct MmapGraphTileHandle {
        owner: MmapTilePointer,
        #[covariant]
        dependent: GraphTileView,
    }
}

impl GraphTile for MmapGraphTileHandle {
    #[inline]
    fn graph_id(&self) -> GraphId {
        self.borrow_dependent().graph_id()
    }

    #[inline]
    fn may_contain_id(&self, id: GraphId) -> bool {
        self.borrow_dependent().may_contain_id(id)
    }

    #[inline]
    fn header(&self) -> &GraphTileHeader {
        self.borrow_dependent().header()
    }

    #[inline]
    fn get_node(&self, id: GraphId) -> Result<&NodeInfo, LookupError> {
        self.borrow_dependent().get_node(id)
    }

    #[inline]
    fn get_outbound_edges_from_node(&self, node_info: &NodeInfo) -> &[DirectedEdge] {
        self.borrow_dependent()
            .get_outbound_edges_from_node(node_info)
    }

    #[inline]
    fn get_transitions(&self, node: &NodeInfo) -> &[NodeTransition] {
        self.borrow_dependent().get_transitions(node)
    }

    #[inline]
    fn get_directed_edge(&self, id: GraphId) -> Result<&DirectedEdge, LookupError> {
        self.borrow_dependent().get_directed_edge(id)
    }

    #[inline]
    fn get_opp_edge_index(&self, graph_id: GraphId) -> Result<OpposingEdgeIndex, LookupError> {
        self.borrow_dependent().get_opp_edge_index(graph_id)
    }

    #[inline]
    fn get_ext_directed_edge(&self, id: GraphId) -> Result<&DirectedEdgeExt, LookupError> {
        self.borrow_dependent().get_ext_directed_edge(id)
    }

    #[inline]
    fn get_access_restrictions(
        &self,
        directed_edge_index: u32,
        access_modes: EnumSet<Access>,
    ) -> Vec<&AccessRestriction> {
        self.borrow_dependent()
            .get_access_restrictions(directed_edge_index, access_modes)
    }

    #[inline]
    fn get_predicted_speed(
        &self,
        directed_edge_index: usize,
        seconds_from_start_of_week: u32,
    ) -> Option<f32> {
        self.borrow_dependent()
            .get_predicted_speed(directed_edge_index, seconds_from_start_of_week)
    }

    #[inline]
    fn get_edge_info(
        &self,
        directed_edge: &DirectedEdge,
    ) -> Result<EdgeInfo<'_>, GraphTileDecodingError> {
        self.borrow_dependent().get_edge_info(directed_edge)
    }

    #[inline]
    fn directed_edges(&self) -> &[DirectedEdge] {
        self.borrow_dependent().directed_edges()
    }

    #[inline]
    fn nodes(&self) -> &[NodeInfo] {
        self.borrow_dependent().nodes
    }

    #[inline]
    fn admins(&self) -> &[Admin] {
        self.borrow_dependent().admins()
    }

    #[inline]
    fn edges_in_bin(&self, bin_index: usize) -> &[GraphId] {
        self.borrow_dependent().edges_in_bin(bin_index)
    }

    #[inline]
    fn bin_index_xy(&self, x: usize, y: usize) -> usize {
        self.borrow_dependent().bin_index_xy(x, y)
    }
}

impl MmapGraphTileHandle {
    /// Creates a new graph tile handle backed by the memory mapped tile pointer.
    ///
    /// # Safety
    ///
    /// See the documentation for [`MmapTilePointer::as_tile_bytes`] for safety conditions.
    /// A valid pointer of the wrong length will result in a regular tile decoding error,
    /// but other errors may produce unexpected results.
    ///
    /// # Performance
    ///
    /// This does not perform any copies.
    /// It does involve some bounds/length checking to ensure at least nominally correct
    /// deserialization, but this overhead is minimal.
    pub unsafe fn try_from(tile_pointer: MmapTilePointer) -> Result<Self, GraphTileDecodingError> {
        MmapGraphTileHandle::try_new(tile_pointer, |ptr| {
            // SAFETY: Assumes that the pointer is to a valid graph tile (not malformed, incorrect index, etc.).
            // The backing memory is assumed to never be mutated during the lifetime of the returned slice.
            // Additionally, we explicitly assume that the index and offsets describe a valid tile.
            let tile_bytes = unsafe { ptr.as_tile_bytes() };
            GraphTileView::try_from(tile_bytes)
        })
    }
}

/// An encapsulating type that can be used to get the actual bytes for a tile.
///
/// This provides a single type that can "own" the backing bytes for tile memory,
/// which we leverage in the `self_cell` to create a zero-copy view.
pub struct MmapTilePointer {
    /// A handle to the memory map that can be shared across threads.
    pub(crate) mmap: Arc<MmapRaw>,
    /// The offsets of the represented data within the memory map.
    pub(crate) offsets: TileOffset,
}

impl MmapTilePointer {
    /// Returns a slice view over the data mapped in memory.
    ///
    /// # Safety
    ///
    /// The backing memory map must not be mutated during the lifetime of the returned slice.
    /// While some mutation of bytes may technically work, changing the values of memory underneath a slice
    /// is undefined behavior in Rust.
    ///
    /// Truncating the file will cause SIGBUS or similar.
    ///
    /// Additionally, we explicitly assume that the index and offsets describe a valid memory range.
    pub unsafe fn as_tile_bytes(&self) -> &[u8] {
        unsafe {
            // `as_ptr` assumes that the file has not been truncated, or else raises a SIGBUS.
            let start_ptr = self.mmap.as_ptr().offset(self.offsets.offset as isize);
            // Assumes the offset and size are valid.
            core::slice::from_raw_parts(start_ptr, self.offsets.size as usize)
        }
    }

    /// Reads from the mapped range and interprets it as type `T`.
    ///
    /// The instance of `T` is created from a _bitwise_ copy of the data.
    /// This uses [`core::ptr::read_volatile`] under the hood to make sure the I/O actually happens.
    ///
    /// # Panics
    ///
    /// Panics if the read is not naturally aligned (checked in an assertion).
    ///
    /// # Safety
    ///
    /// The approach taken here mirrors that of Valhalla,
    /// which I'm not sure is fundamentally sound,
    /// though it may be *practically* acceptable on x86_64 for the places it's used
    /// (traffic tile access via a shared memory map).
    ///
    /// There are a lot of things that can go wrong here.
    /// The following will likely result in a SIGBUS:
    ///
    /// - Truncating the memory mapped file.
    /// - Remapping or resizing the map.
    ///
    /// The following are also obviously unsafe and will cause either a panic or undefined behavior:
    ///
    /// - Trying to read a value where `size_of::<T>()` doesn't match the size of the pointer.
    ///   We statically assert this, and if you fail to uphold this invariant, the program will panic.
    /// - Reading an offset or size out of bounds.
    ///
    /// Finally, while this does force a volatile read,
    /// NO ATTEMPT IS MADE AT SYNCHRONIZATION!
    /// This is, regrettably, how Valhalla currently does things.
    /// There should probably be atomics involved to synchronize writes,
    /// but that requires some internal Valhalla evolution,
    /// which would result in some breaking changes.
    ///
    /// As far as I can tell, this is *practically* acceptable if the writer
    /// is always storing values of a size that are guaranteed to be atomic
    /// by the underlying architecture, provided that:
    ///
    /// - No logical field ever crosses a _byte_ boundary, OR
    /// - All reads and writes are naturally aligned AND integer operations are atomic for that size
    ///   on the architecture AND no logical field crosses a boundary between two such larger width integers
    ///
    /// Concretely, this means that **writers must use a larger size integer type
    /// if fields can span across byte boundaries (as they do in traffic tiles)
    /// as the byte-level reads would permit tearing.**
    pub unsafe fn read_volatile<T>(&self) -> T {
        assert_eq!(
            size_of::<T>(),
            self.offsets
                .size
                .try_into()
                .expect("u32 does not fit into usize... that's unexpected!"),
            "You can't try an unsafe cast on a byte range of the wrong size!"
        );
        // SAFETY: Assumes that the offset is valid.
        // The pointer arithmetic must never be greater than isize::MAX,
        // which we satisfy implicitly as it is of type `u32` and we do not support
        // any CPU with pointers smaller than 64-bits.
        unsafe {
            let ptr = self
                .mmap
                .as_ptr()
                .add(self.offsets.offset as usize)
                .cast::<T>();
            assert!(ptr.is_aligned());

            ptr.read_volatile()
        }
    }

    /// Writes the value to the mapped range.
    ///
    /// This will fail to compile if lock-free atomics are not supported for the current target
    /// for types of `size_of::<T>()`.
    /// This is statically checked at compile time.
    /// More on this later...
    ///
    /// # Panics
    ///
    /// - If `self.offsets.size` does not match the size of type `T` (clearly incorrect).
    /// - If the pointer is not aligned for type `T` (no major platform guarantees atomicity).
    ///
    /// # Safety
    ///
    /// The following will likely result in a SIGBUS:
    ///
    /// - Truncating the memory mapped file.
    /// - Remapping or resizing the map.
    ///
    /// The following are also obviously unsafe and will cause either a panic or undefined behavior:
    ///
    /// - Reading an offset or size out of bounds.
    /// - Language specs indicate that unsynchronized concurrent reads and writes are UB.
    ///   By making reads and writes volatile, we mitigate one source of uncertainty,
    ///   instructing the compiler that it can never optimize these away.
    ///   However, shared memory maps have NO inherent synchronization.
    ///   The check for lock-free atomics on the target for this value size _typically_ indicates
    ///   that loads and stores **to memory** are atomic for naturally aligned pointers.
    ///   This implies nothing about _ordering_, but it does protect against torn writes.
    pub unsafe fn write_volatile<T>(&self, value: T) {
        const {
            let has_atomic = match size_of::<T>() {
                1 => cfg!(target_has_atomic = "8"),
                2 => cfg!(target_has_atomic = "16"),
                4 => cfg!(target_has_atomic = "32"),
                8 => cfg!(target_has_atomic = "64"),
                16 => cfg!(target_has_atomic = "128"),
                _ => false,
            };
            assert!(
                has_atomic,
                "This type does not have a lock-free atomic support (it's probably too wide) on your current target."
            );
        };

        assert_eq!(self.offsets.size, size_of::<T>() as u32);
        unsafe {
            // SAFETY: Assumes that the offset is valid.
            let ptr = self
                .mmap
                .as_mut_ptr()
                .add(self.offsets.offset as usize)
                .cast::<T>();
            assert!(ptr.is_aligned());

            ptr.write_volatile(value);
        }
    }
}

/// A tile offset, used for internal storage out of the parsed index.
#[derive(Copy, Clone)]
pub(crate) struct TileOffset {
    /// Byte offset from the beginning of the tar
    pub(crate) offset: u64,
    /// The size of the tile in bytes.
    pub(crate) size: u32,
}
