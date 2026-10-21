use super::{GraphTileProvider, GraphTileProviderError, TileBytesSource};
use crate::GraphId;
use crate::graph_tile::handles::MmapGraphTileHandle;
use crate::graph_tile::{
    GraphTileView,
    handles::{MmapTilePointer, TileOffset},
};
use crate::spatial::bbox_with_center;
use crate::tile_hierarchy::STANDARD_LEVELS;
use geo::{CoordFloat, Point};
use memmap2::{MmapOptions, MmapRaw};
use num_traits::FromPrimitive;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::sync::Arc;
use tar::Archive;
use thiserror::Error;
use zerocopy::{FromBytes, IntoBytes, LE, U32, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

/// A tile provider backed by a memory-mapped tarball archive.
///
/// # Tarball requirements/assumptions
///
/// Valhalla is capable of reading almost any tarball containing graph tiles.
/// Valinor is much less tolerant, and *requires* an `index.bin` file.
///
/// Modern Valhalla tooling like `valhalla_build_extract`
/// will write this automatically, but if you're still hand-rolling tarballs with a `bash` script,
/// Valinor won't touch those (initialization will fail with an error).
///
/// # Safety
///
/// The following actions are *definitely* unsafe:
///
/// - Changing the contents of the index file.
/// - By extension, changing the set of tiles mapped.
/// - Also by extension, changing the size of a tile.
/// - Truncating the file.
///
/// Violating any of the above will result in either failed tile fetches (with an error)
/// or a SIGBUS.
///
/// Additionally, extreme care must be taken when the file may be modified by an external process.
/// The current implementation is primarily designed around volatile memory access.
pub struct TarballTileProvider<const MUT: bool, const CACHE: bool> {
    /// The file backing the mmap.
    ///
    /// This is unused, but we need to keep it in scope since the memmap only has a reference to it,
    /// not ownership!
    _file: File,
    /// The actual memory map.
    mmap: Arc<MmapRaw>,
    /// An index of offsets and sizes which enables quick tile extraction from the memory map.
    tile_index: HashMap<GraphId, TileOffset>,
    /// An immutable tile cache.
    ///
    /// While loading tiles from the tarball is zero-copy,
    /// it is not strictly zero-cost.
    /// A typical lookup requires these steps:
    ///
    /// - Hashmap look up by graph ID in `tile_index`
    /// - Construct a tile pointer
    /// - Create a slice to the raw bytes
    /// - Check the validity of the bytes before transmuting the pointer
    ///
    /// This overhead is very small,
    /// but a strenuous workload like map matching millions of short segments
    /// demonstrates that there is real overhead here.
    ///
    /// If (and only if!) the user guarantees that the underlying memory map will never be mutated,
    /// we can front-load all the sanity checks and convert every tile resolution
    /// into a single hashmap lookup.
    /// This only works if the underlying shared memory is immutable though,
    /// as mutation of memory backing a slice with a shared reference
    /// is undefined behavior: https://doc.rust-lang.org/reference/behavior-considered-undefined.html#r-undefined.immutable.
    tile_cache: HashMap<GraphId, Arc<MmapGraphTileHandle>>,
}

impl<const MUT: bool, const CACHE: bool> TarballTileProvider<MUT, CACHE> {
    /// Creates a new tarball tile provider from the given path.
    ///
    /// # Safety
    ///
    /// If `CACHE` is `true`, the caller must guarantee that the underlying memory map
    /// is never mutated during the lifetime of the object.
    /// Mutation results in undefined behavior.
    ///
    /// # Errors
    ///
    /// This may fail if the index is invalid or missing.
    /// It will also fail if `with_cache` is `true`, but a tile is malformed.
    pub(in crate::tile_provider) unsafe fn init<P: AsRef<Path>>(
        path: P,
    ) -> Result<Self, GraphTileProviderError> {
        const {
            assert!(
                !(MUT && CACHE),
                "TarballTileProvider<true, true> is not allowed; cache is not safe combined with mutability."
            );
        }

        let archive_file = File::open(&path)?;
        let archive_len = archive_file.metadata()?.len();
        let mut archive = Archive::new(archive_file);
        let mut entries = archive.entries()?;

        let Some(entry) = entries.next() else {
            return Err(GraphTileProviderError::InvalidTarball(
                "No entries in the archive".to_string(),
            ));
        };

        let mut entry = entry?;
        if entry.path()?.to_string_lossy() != INDEX_BIN_ENTRY_NAME {
            return Err(GraphTileProviderError::InvalidTarball(format!(
                "Expected {INDEX_BIN_ENTRY_NAME} at the start of the archive"
            )));
        }

        // Read the index file
        let mut index_bytes = Vec::with_capacity(entry.header().size()? as usize);
        entry.read_to_end(&mut index_bytes)?;

        let index_entries = parse_index_bin(&index_bytes)?;

        // Index the index
        let mut tile_index: HashMap<GraphId, TileOffset> =
            HashMap::with_capacity(index_entries.len());
        for entry in index_entries {
            let (graph_id, offset) = entry.validated(archive_len)?;
            tile_index.insert(
                graph_id,
                TileOffset {
                    offset,
                    size: entry.size.get(),
                },
            );
        }

        // Explicitly (not strictly necessary) close the archive reader handle
        drop(archive);

        let file = File::options().write(MUT).read(true).open(&path)?;
        // TODO: Prewarm and populate options
        let mmap = if MUT {
            Arc::new(MmapOptions::new().map_raw(&file)?)
        } else {
            Arc::new(MmapOptions::new().map_raw_read_only(&file)?)
        };

        // Tile pointers slice the map without a bounds check,
        // so the map must have the length that the index ranges were checked against.
        if mmap.len() as u64 != archive_len {
            return Err(GraphTileProviderError::InvalidTarball(format!(
                "the archive changed size while it was opened ({archive_len} bytes, then {} bytes)",
                mmap.len()
            )));
        }

        let mut tile_cache = HashMap::new();

        if CACHE {
            for (graph_id, tile_offset) in &tile_index {
                let tile_pointer = MmapTilePointer {
                    mmap: mmap.clone(),
                    offsets: *tile_offset,
                };
                // SAFETY: We document the immutability conditions in the method docs
                let tile_handle = Arc::new(unsafe { MmapGraphTileHandle::try_from(tile_pointer)? });
                tile_cache.insert(*graph_id, tile_handle);
            }
        }

        Ok(Self {
            _file: file,
            mmap,
            tile_index,
            tile_cache,
        })
    }

    /// An iterator over all tile IDs contained in the tarball, in arbitrary order.
    pub fn tile_ids(&self) -> impl Iterator<Item = &GraphId> {
        self.tile_index.keys()
    }

    /// Gets a pointer for the tile containing this graph ID.
    ///
    /// # Errors
    ///
    /// If the tile is not part of the tarball archive,
    /// this returns [`GraphTileProviderError::TileDoesNotExist`].
    #[inline]
    fn tile_pointer(&self, graph_id: GraphId) -> Result<MmapTilePointer, GraphTileProviderError> {
        let base_graph_id = graph_id.tile_base_id();
        let Some(offsets) = self.tile_index.get(&base_graph_id) else {
            return Err(GraphTileProviderError::TileDoesNotExist);
        };

        Ok(MmapTilePointer {
            mmap: self.mmap.clone(),
            offsets: *offsets,
        })
    }
}

impl<const MUT: bool, const CACHE: bool> TileBytesSource for TarballTileProvider<MUT, CACHE> {
    type Error = GraphTileProviderError;

    /// The size comes from the `index.bin` of the tarball, so this reads no tile data.
    #[inline]
    fn tile_size(&self, graph_id: GraphId) -> Result<Option<u32>, Self::Error> {
        Ok(self
            .tile_index
            .get(&graph_id.tile_base_id())
            .map(|tile_offset| tile_offset.size))
    }

    #[inline]
    fn with_tile_bytes<F, T>(&self, graph_id: GraphId, process: F) -> Result<T, Self::Error>
    where
        F: FnOnce(&[u8]) -> T,
    {
        let tile_pointer = self.tile_pointer(graph_id)?;
        // SAFETY: The provider checks at construction that every index range lies inside the memory map.
        // We assume that the underlying memory map has not changed in a way that would render the tile invalid
        // (see the safety discussion on TarballTileProvider).
        let tile_bytes = unsafe { tile_pointer.as_tile_bytes() };
        Ok(process(tile_bytes))
    }
}

impl<const MUT: bool> GraphTileProvider for TarballTileProvider<MUT, false> {
    type TileHandle = Arc<MmapGraphTileHandle>;

    #[inline]
    fn with_tile_containing<F, T>(
        &self,
        graph_id: GraphId,
        process: F,
    ) -> Result<T, GraphTileProviderError>
    where
        F: FnOnce(&GraphTileView) -> T,
    {
        let tile_pointer = self.get_pointer_for_tile_containing(graph_id)?;
        // SAFETY: We assume that the tile pointer is live and points to an actual graph tile location in the tarball.
        // That is to say, we assume the tile is well-formed (correct index) and that the underlying memory map
        // has not changed in a way that would render the tile invalid.
        let tile_bytes = unsafe { tile_pointer.as_tile_bytes() };
        let tile = GraphTileView::try_from(tile_bytes)?;
        Ok(process(&tile))
    }

    #[inline]
    fn get_handle_for_tile_containing(
        &self,
        graph_id: GraphId,
    ) -> Result<Self::TileHandle, GraphTileProviderError> {
        let pointer = self.get_pointer_for_tile_containing(graph_id)?;

        // SAFETY: Assumes that the pointer is to a valid graph tile.
        // Since we just got this from get_pointer_for_tile_containing, this should be safe enough.
        // The backing memory is assumed to never be mutated during the lifetime of the returned handle.
        Ok(Arc::new(unsafe { MmapGraphTileHandle::try_from(pointer)? }))
    }

    #[inline]
    fn tiles_within_radius<N: CoordFloat + FromPrimitive>(
        &self,
        center: Point<N>,
        radius: N,
    ) -> Vec<GraphId> {
        self.tiles_within_radius(center, radius)
    }
}

impl<const MUT: bool> GraphTileProvider for TarballTileProvider<MUT, true> {
    type TileHandle = Arc<MmapGraphTileHandle>;

    #[inline]
    fn with_tile_containing<F, T>(
        &self,
        graph_id: GraphId,
        process: F,
    ) -> Result<T, GraphTileProviderError>
    where
        F: FnOnce(&GraphTileView) -> T,
    {
        let tile = self
            .tile_cache
            .get(&graph_id.tile_base_id())
            .ok_or(GraphTileProviderError::TileDoesNotExist)?;
        Ok(process(tile.borrow_dependent()))
    }

    #[inline]
    fn get_handle_for_tile_containing(
        &self,
        graph_id: GraphId,
    ) -> Result<Self::TileHandle, GraphTileProviderError> {
        let tile = self
            .tile_cache
            .get(&graph_id.tile_base_id())
            .ok_or(GraphTileProviderError::TileDoesNotExist)?;
        Ok(tile.clone())
    }

    #[inline]
    fn tiles_within_radius<N: CoordFloat + FromPrimitive>(
        &self,
        center: Point<N>,
        radius: N,
    ) -> Vec<GraphId> {
        self.tiles_within_radius(center, radius)
    }
}

impl<const MUT: bool, const CACHE: bool> TarballTileProvider<MUT, CACHE> {
    #[inline]
    fn tiles_within_radius<N: CoordFloat + FromPrimitive>(
        &self,
        center: Point<N>,
        radius: N,
    ) -> Vec<GraphId> {
        let mut out: Vec<GraphId> = Vec::new();

        let (north, east, south, west) = bbox_with_center(center, radius);

        for level in STANDARD_LEVELS.iter() {
            for gid in level.tiles_intersecting_bbox(north, east, south, west) {
                if self.tile_index.contains_key(&gid) {
                    out.push(gid);
                }
            }
        }

        out
    }
}

impl<const MUT: bool> TarballTileProvider<MUT, false> {
    /// Gets a pointer for the tile containing this graph ID.
    ///
    /// # Errors
    ///
    /// If the tile is not part of the tarball archive,
    /// this returns [`GraphTileProviderError::TileDoesNotExist`].
    pub fn get_pointer_for_tile_containing(
        &self,
        graph_id: GraphId,
    ) -> Result<MmapTilePointer, GraphTileProviderError> {
        self.tile_pointer(graph_id)
    }
}

impl TarballTileProvider<false, false> {
    /// Creates a new tarball tile provider from an existing extract.
    ///
    /// This constructor creates the memory mapping in read-only mode,
    /// but it does not strictly assume that the underlying memory is immutable.
    /// This constructor is safe, but underlying memory access is subject to conditions
    /// which are noted in the various access methods on pointers.
    /// Refer to the [`TarballTileProvider`] documentation for a fuller safety discussion.
    ///
    /// If you guarantee that the tarball bytes will _never_ be mutated in any way
    /// during the life of the provider, you can use [`TarballTileProvider::new_immutable`]
    /// for better performance over the long run.
    ///
    /// # Errors
    ///
    /// The extract _must_ include an `index.bin` file as the first entry.
    /// If the file is not _valid_ (of the correct length and superficially correct structure),
    /// this constructor will fail.
    ///
    /// However, no further checks are performed to ensure the correctness of the file
    /// (its entire _raison d'être_ is that you shouldn't have to scan the whole tarball),
    /// so an incorrect index will invariably lead to tile fetch errors.
    pub fn new_readonly<P: AsRef<Path>>(path: P) -> Result<Self, GraphTileProviderError> {
        // SAFETY: Immutability is guaranteed by the const generic
        unsafe { Self::init(path) }
    }
}

impl TarballTileProvider<false, true> {
    /// Creates a new tarball tile provider from an immutable extract.
    ///
    /// Normally there is a small amount of overhead when accessing graph tiles due to validation
    /// to ensure that the memory layout is correct (it's zero copy, but not zero cost).
    /// You pay this cost on every tile access for tile providers constructed with
    /// [`TarballTileProvider::new_readonly`] or [`TarballTileProvider::new_immutable`].
    ///
    /// This constructor front-loads the validation work so that subsequent tile access
    /// is O(1).
    /// In exchange, this requires stronger guarantees, which is why it's marked unsafe.
    ///
    /// # Safety
    ///
    /// If you use this constructor, you *must* guarantee that the backing memory and file
    /// are immutable during the lifetime of the object.
    /// Any mutation of the underlying memory results in undefined behavior.
    ///
    /// If you cannot make these guarantees, but do not require mutability,
    /// use [`TarballTileProvider::new_readonly`] instead.
    ///
    /// # Errors
    ///
    /// The extract _must_ include an `index.bin` file as the first entry.
    /// If the file is not _valid_ (of the correct length and superficially correct structure),
    /// this constructor will fail.
    ///
    /// This will also fail if any tile is obviously malformed.
    pub unsafe fn new_immutable<P: AsRef<Path>>(path: P) -> Result<Self, GraphTileProviderError> {
        // SAFETY: Immutability requirement documented in docstring
        unsafe { Self::init(path) }
    }
}

impl TarballTileProvider<true, false> {
    /// Creates a new tarball tile provider from an existing extract.
    /// Write support is enabled by this constructor.
    ///
    /// # Errors
    ///
    /// The extract _must_ include an `index.bin` file as the first entry.
    /// If the file is not _valid_ (of the correct length and superficially correct structure),
    /// this constructor will fail.
    ///
    /// However, no further checks are performed to ensure the correctness of the file
    /// (its entire _raison d'être_ is that you shouldn't have to scan the whole tarball),
    /// so an incorrect index will invariably lead to tile fetch errors.
    pub fn new_mutable<P: AsRef<Path>>(path: P) -> Result<Self, GraphTileProviderError> {
        // SAFETY: CACHE=false is guaranteed by the const generic
        unsafe { Self::init(path) }
    }

    /// Flushes outstanding memory map modifications to disk.
    ///
    /// See [`MmapRaw::flush`] for more details.
    ///
    /// # Errors
    ///
    /// This may fail due to any of the usual reasons I/O operations fail.
    pub fn flush(&self) -> std::io::Result<()> {
        self.mmap.flush()
    }
}

/// A tile index entry enabling efficient random access into a tarball archive.
///
/// # The `index.bin` file
///
/// Tarballs were designed for an era of tape drives, where access was essentially sequential.
/// This gives tarballs some interesting properties, like being a series of entries that can
/// be written sequentially without requiring (necessarily) a header at the start with full info.
/// They can even be concatenated together!
///
/// But I digress... Tarballs *can* be accessed randomly by seeking to specific offsets in the file,
/// but you need to know where each file is located.
/// Valhalla has a convention of writing an `index.bin` file as the first entry of the archive
/// which contains these offsets.
/// Once you parse this, you have the keys to random access of any graph tile within a single file
/// (typically a memory map).
///
/// The `index.bin` file is just a series of these structs written out sequentially;
/// no padding or headers, just bytes.
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, Debug, PartialEq)]
#[repr(C)]
pub struct TileIndexBinEntry {
    /// Byte offset from the beginning of the tar
    offset: U64<LE>,
    /// Just the level and tile index, hence fitting in 32 bits
    tile_id: U32<LE>,
    /// The size of the tile in bytes.
    size: U32<LE>,
}

/// The size of one [`TileIndexBinEntry`] in bytes.
pub(crate) const INDEX_ENTRY_SIZE: usize = size_of::<TileIndexBinEntry>();

/// The block size of a tar archive.
///
/// Each entry is a header block, then its data, padded with zeros to whole blocks.
pub(crate) const TAR_BLOCK_SIZE: u64 = 512;

/// The name of the tile index entry, which is the first entry of an extract tarball.
pub(crate) const INDEX_BIN_ENTRY_NAME: &str = "index.bin";

/// The reasons why an `index.bin` file or one of its entries is not valid.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum InvalidIndexBinError {
    #[error("the index has no entries")]
    Empty,
    #[error(
        "the index length ({0} bytes) is not a multiple of the entry size ({INDEX_ENTRY_SIZE} bytes)"
    )]
    Length(usize),
    #[error("{0} is not a base tile ID; expected the feature index to be zero")]
    FeatureIndex(GraphId),
    #[error("graph ID {0} has reserved bits set")]
    ReservedBits(u64),
    #[error(
        "the entry for {graph_id} has offset {offset}; expected a non-zero multiple of {TAR_BLOCK_SIZE}"
    )]
    Offset { graph_id: GraphId, offset: u64 },
    #[error(
        "the entry for {graph_id} has {size} bytes at offset {offset}, which is past the end of the {archive_len}-byte archive"
    )]
    OutOfBounds {
        graph_id: GraphId,
        offset: u64,
        size: u32,
        archive_len: u64,
    },
}

impl TileIndexBinEntry {
    /// Creates an index entry for a tile located at the given byte offset within a tarball.
    ///
    /// # Errors
    ///
    /// This will fail if `graph_id` is not a base tile ID
    /// (the feature index and reserved bits must be zero),
    /// or if `offset` is zero or does not lie on a 512-byte boundary
    /// (tar entry data is always aligned to 512-byte blocks).
    pub fn new(graph_id: GraphId, offset: u64, size: u32) -> Result<Self, InvalidIndexBinError> {
        let tile_id = base_tile_id(graph_id)?;
        check_offset(graph_id, offset)?;

        Ok(Self {
            offset: U64::new(offset),
            tile_id: U32::new(tile_id),
            size: U32::new(size),
        })
    }

    /// Checks the entry against an archive of `archive_len` bytes,
    /// and returns its graph ID and offset.
    ///
    /// Call this before you use an entry from [`parse_index_bin`], which does not check the values.
    fn validated(&self, archive_len: u64) -> Result<(GraphId, u64), InvalidIndexBinError> {
        let graph_id = self.graph_id()?;
        let offset = self.offset.get();
        check_offset(graph_id, offset)?;
        check_range(graph_id, offset, self.size.get(), archive_len)?;

        Ok((graph_id, offset))
    }

    /// The graph ID of the indexed tile.
    ///
    /// # Errors
    ///
    /// Returns an error if the stored tile ID has nonzero feature index bits.
    pub fn graph_id(&self) -> Result<GraphId, InvalidIndexBinError> {
        // SAFETY: We know that the bit field cannot contain a value
        // larger than the max allowed value (it's limited to 46 bits).
        // Therefore, this is guaranteed to be a valid Graph ID bit pattern.
        let graph_id = unsafe { GraphId::from_id_unchecked(self.tile_id.into()) };
        base_tile_id(graph_id)?;

        Ok(graph_id)
    }

    /// The byte offset of the tile payload from the beginning of the tarball.
    #[inline]
    pub fn offset(&self) -> u64 {
        self.offset.get()
    }

    /// The size of the tile in bytes.
    #[inline]
    pub fn size(&self) -> u32 {
        self.size.get()
    }
}

/// Makes sure that `graph_id` identifies a full tile,
/// and returns the packed level and tile ID that `index.bin` stores.
fn base_tile_id(graph_id: GraphId) -> Result<u32, InvalidIndexBinError> {
    if graph_id.feature_index() != 0 {
        return Err(InvalidIndexBinError::FeatureIndex(graph_id));
    }

    // A base tile ID packs the level and tile ID into the low 25 bits,
    // so this conversion only fails for IDs with reserved bits set
    // (such IDs can only be produced by the unchecked GraphId constructors).
    u32::try_from(graph_id.value())
        .map_err(|_| InvalidIndexBinError::ReservedBits(graph_id.value()))
}

/// Makes sure that `offset` can be the start of the data of a tar entry.
///
/// A tar entry starts with a 512-byte header, so its data cannot be at offset zero.
fn check_offset(graph_id: GraphId, offset: u64) -> Result<(), InvalidIndexBinError> {
    if offset == 0 || !offset.is_multiple_of(TAR_BLOCK_SIZE) {
        return Err(InvalidIndexBinError::Offset { graph_id, offset });
    }

    Ok(())
}

/// Makes sure that the tile at `offset` with `size` bytes lies inside an archive of `archive_len` bytes.
fn check_range(
    graph_id: GraphId,
    offset: u64,
    size: u32,
    archive_len: u64,
) -> Result<(), InvalidIndexBinError> {
    if offset
        .checked_add(u64::from(size))
        .is_none_or(|end| end > archive_len)
    {
        return Err(InvalidIndexBinError::OutOfBounds {
            graph_id,
            offset,
            size,
            archive_len,
        });
    }

    Ok(())
}

/// Parses an `index.bin` file to enable random access.
///
/// See [`TileIndexBinEntry`] for a description of the tile format.
/// This function only checks the length of the input.
/// It does not validate the values in the entries.
///
/// # Errors
///
/// The input must be non-zero in length and consist of a whole number of entries;
/// anything else fails with an [`InvalidIndexBinError`].
pub fn parse_index_bin(index_bytes: &[u8]) -> Result<&[TileIndexBinEntry], InvalidIndexBinError> {
    if index_bytes.is_empty() {
        return Err(InvalidIndexBinError::Empty);
    }

    // The entry type is unaligned,
    // so the only possible failure is a length that is not a whole number of entries.
    <[TileIndexBinEntry]>::ref_from_bytes(index_bytes)
        .map_err(|_| InvalidIndexBinError::Length(index_bytes.len()))
}

/// Serializes tile index entries into the bytes of an `index.bin` file.
///
/// This is the write-side twin of [`parse_index_bin`]:
/// the entries are written out sequentially with no padding or headers
/// (see [`TileIndexBinEntry`] for a description of the file format).
/// Bytes returned by this function always parse back into the same entries.
///
/// # Performance
///
/// The entries already have the exact memory layout of the file format,
/// so this is a zero-copy transmutation of the slice.
///
/// # Errors
///
/// An index without any entries is malformed
/// (an extract containing no tiles is meaningless, and [`parse_index_bin`] rejects it),
/// so serializing an empty slice fails with [`InvalidIndexBinError::Empty`].
pub fn serialize_index_bin(entries: &[TileIndexBinEntry]) -> Result<&[u8], InvalidIndexBinError> {
    if entries.is_empty() {
        return Err(InvalidIndexBinError::Empty);
    }

    Ok(entries.as_bytes())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::graph_tile::{GraphTile, GraphTileView};
    use crate::test_fixtures;
    use crate::tile_provider::DirectoryGraphTileProvider;
    use proptest::collection::vec;
    use proptest::{prop_assert, prop_assert_eq, proptest};
    use std::num::NonZeroUsize;

    /// Bytes taken from the start of a large extract generated by official Valhalla tooling.
    const INDEX_BIN_FIXTURE: &[u8] = &[
        // Tile 1
        0x00, 0x5a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x4f, 0x00, 0x00, 0x9c, 0x08, 0x12,
        0x00, // Tile 2
        0x00, 0x6a, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x52, 0x00, 0x00, 0xc8, 0x67, 0x01,
        0x00, // Tile 3
        0x00, 0xd8, 0x13, 0x00, 0x00, 0x00, 0x00, 0x00, 0x28, 0x52, 0x00, 0x00, 0x28, 0x9d, 0x1b,
        0x00,
    ];

    #[test]
    fn test_parse_index_bin_invalid() {
        assert_eq!(
            parse_index_bin(&[]),
            Err(InvalidIndexBinError::Empty),
            "Empty indexes are invalid"
        );
        assert_eq!(
            parse_index_bin(&[0x00, 0x5a]),
            Err(InvalidIndexBinError::Length(2)),
            "Index must contain at least one full entry"
        );
        assert_eq!(
            parse_index_bin(&[
                // Contains one extra byte
                0x00, 0x5a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x4f, 0x00, 0x00, 0x9c, 0x08,
                0x12, 0x00, 0x00
            ]),
            Err(InvalidIndexBinError::Length(17)),
            "Index must be completely parseable with no bytes leftover"
        );
    }

    #[test]
    fn test_validate_parsed_entry() {
        let graph_id = GraphId::try_from_components(0, 2540, 0).expect("Unable to create graph ID");
        let index_entries = parse_index_bin(INDEX_BIN_FIXTURE).expect("Unable to parse fixture");
        // The smallest archive that can contain the first tile ends where that tile ends.
        let first_entry_end = index_entries[0].offset() + u64::from(index_entries[0].size());
        assert_eq!(
            index_entries[0].validated(first_entry_end),
            Ok((graph_id, 23040)),
            "A tile may end exactly at the end of the archive"
        );
        assert_eq!(
            index_entries[0].validated(first_entry_end - 1),
            Err(InvalidIndexBinError::OutOfBounds {
                graph_id,
                offset: 23040,
                size: 1_181_852,
                archive_len: first_entry_end - 1
            }),
            "A tile must not end past the end of the archive"
        );

        // Change the low byte of the first offset (23040 = 0x5a00) to make it unaligned
        let mut bytes = INDEX_BIN_FIXTURE.to_vec();
        bytes[0] = 0x01;
        let index_entries = parse_index_bin(&bytes).expect("Unable to parse modified fixture");
        assert_eq!(
            index_entries[0].validated(first_entry_end),
            Err(InvalidIndexBinError::Offset {
                graph_id,
                offset: 23041
            }),
            "Offsets must lie on a 512-byte boundary"
        );

        // Zero the first offset
        let mut bytes = INDEX_BIN_FIXTURE.to_vec();
        bytes[..8].fill(0);
        let index_entries = parse_index_bin(&bytes).expect("Unable to parse modified fixture");
        assert_eq!(
            index_entries[0].validated(first_entry_end),
            Err(InvalidIndexBinError::Offset {
                graph_id,
                offset: 0
            }),
            "Zero offsets are invalid"
        );

        // Set bit 25 of the first tile ID (the lowest bit of the feature index)
        let mut bytes = INDEX_BIN_FIXTURE.to_vec();
        bytes[11] |= 0x02;
        let index_entries = parse_index_bin(&bytes).expect("Unable to parse modified fixture");
        assert_eq!(
            index_entries[0].validated(first_entry_end),
            Err(InvalidIndexBinError::FeatureIndex(
                graph_id
                    .with_feature_index(1)
                    .expect("Unable to create graph ID")
            )),
            "Graph IDs with a non-zero feature index are invalid"
        );
    }

    #[test]
    fn test_parse_index_bin() {
        let index_entries = parse_index_bin(INDEX_BIN_FIXTURE).expect("Unable ta parse fixture");

        assert_eq!(index_entries.len(), 3);

        // All sizes were verified on disk from the original tiles when constructing the test

        // First entry
        assert_eq!(index_entries[0].offset.get(), 23040);
        assert_eq!(index_entries[0].graph_id().unwrap(), unsafe {
            GraphId::from_components_unchecked(0, 2540, 0)
        });
        assert_eq!(index_entries[0].size.get(), 1_181_852);

        // Second entry
        assert_eq!(index_entries[1].offset.get(), 1_206_784);
        assert_eq!(index_entries[1].graph_id().unwrap(), unsafe {
            GraphId::from_components_unchecked(0, 2628, 0)
        });
        assert_eq!(index_entries[1].size.get(), 92_104);

        // Third entry
        assert_eq!(index_entries[2].offset.get(), 1_300_480);
        assert_eq!(index_entries[2].graph_id().unwrap(), unsafe {
            GraphId::from_components_unchecked(0, 2629, 0)
        });
        assert_eq!(index_entries[2].size.get(), 1_809_704);
    }

    #[test]
    fn test_check_range() {
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");

        assert_eq!(check_range(graph_id, 512, 512, 1024), Ok(()));
        assert_eq!(
            check_range(graph_id, 512, 513, 1024),
            Err(InvalidIndexBinError::OutOfBounds {
                graph_id,
                offset: 512,
                size: 513,
                archive_len: 1024
            }),
            "A tile must end at or before the end of the archive"
        );
        assert_eq!(
            check_range(graph_id, u64::MAX - 511, 1024, u64::MAX),
            Err(InvalidIndexBinError::OutOfBounds {
                graph_id,
                offset: u64::MAX - 511,
                size: 1024,
                archive_len: u64::MAX
            }),
            "The end of the range must not overflow"
        );
    }

    // Tragically, memory maps are not supported by Miri!
    #[cfg(not(miri))]
    #[test]
    fn test_reject_index_past_end_of_archive() {
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        // The index gives 10,000 bytes, but the archive has only 100 bytes of tile data.
        let index_entry =
            TileIndexBinEntry::new(graph_id, 1536, 10_000).expect("Unable to create index entry");
        let index_bytes = serialize_index_bin(core::slice::from_ref(&index_entry))
            .expect("Unable to serialize the index");

        let file = tempfile::NamedTempFile::new().expect("Unable to create a temporary file");
        let mut builder = tar::Builder::new(file.as_file());
        for (path, payload) in [("index.bin", index_bytes), ("0/003/015.gph", &[0x5a; 100])] {
            let mut header = tar::Header::new_ustar();
            header.set_size(payload.len() as u64);
            header.set_cksum();
            builder
                .append_data(&mut header, path, payload)
                .expect("Unable to append a tar entry");
        }
        builder.finish().expect("Unable to finish the archive");

        let result = TarballTileProvider::new_readonly(file.path());
        assert!(
            matches!(
                result,
                Err(GraphTileProviderError::InvalidIndexBin(
                    InvalidIndexBinError::OutOfBounds {
                        offset: 1536,
                        size: 10_000,
                        ..
                    }
                ))
            ),
            "An index entry past the end of the archive must be rejected"
        );
    }

    #[test]
    fn test_tile_index_bin_entry_new() {
        let graph_id = GraphId::try_from_components(0, 2540, 0).expect("Unable to create graph ID");
        let entry = TileIndexBinEntry::new(graph_id, 23040, 1_181_852)
            .expect("Unable to create index entry");

        assert_eq!(entry.offset.get(), 23040);
        assert_eq!(entry.graph_id().unwrap(), graph_id);
        assert_eq!(entry.size.get(), 1_181_852);
    }

    #[test]
    fn test_tile_index_bin_entry_new_invalid() {
        let graph_id = GraphId::try_from_components(0, 2540, 0).expect("Unable to create graph ID");

        let feature_id = graph_id
            .with_feature_index(1)
            .expect("Unable to create graph ID");
        assert_eq!(
            TileIndexBinEntry::new(feature_id, 512, 42),
            Err(InvalidIndexBinError::FeatureIndex(feature_id)),
            "Graph IDs with a non-zero feature index are invalid"
        );

        // Only constructible via the unchecked APIs,
        // but the constructor still shouldn't let it through silently.
        // SAFETY: The test does not use this ID to index into a tile.
        // It only gives the ID to the constructor, which must reject it.
        let reserved_id = unsafe { GraphId::from_id_unchecked(U64::new(1 << 46)) };
        assert_eq!(
            TileIndexBinEntry::new(reserved_id, 512, 42),
            Err(InvalidIndexBinError::ReservedBits(1 << 46)),
            "Graph IDs with reserved bits set are invalid"
        );

        for offset in [0, 256, 23041] {
            assert_eq!(
                TileIndexBinEntry::new(graph_id, offset, 42),
                Err(InvalidIndexBinError::Offset { graph_id, offset }),
                "Offsets must be non-zero and lie on a 512-byte boundary"
            );
        }
    }

    #[test]
    fn test_serialize_index_bin_empty() {
        assert_eq!(
            serialize_index_bin(&[]),
            Err(InvalidIndexBinError::Empty),
            "Empty indexes are invalid"
        );
    }

    #[test]
    fn test_serialize_index_bin() {
        // The same three entries as in the fixture (see test_parse_index_bin)
        let entries = [
            TileIndexBinEntry::new(
                GraphId::try_from_components(0, 2540, 0).expect("Unable to create graph ID"),
                23040,
                1_181_852,
            )
            .expect("Unable to create index entry"),
            TileIndexBinEntry::new(
                GraphId::try_from_components(0, 2628, 0).expect("Unable to create graph ID"),
                1_206_784,
                92_104,
            )
            .expect("Unable to create index entry"),
            TileIndexBinEntry::new(
                GraphId::try_from_components(0, 2629, 0).expect("Unable to create graph ID"),
                1_300_480,
                1_809_704,
            )
            .expect("Unable to create index entry"),
        ];

        let bytes = serialize_index_bin(&entries).expect("Unable to serialize index entries");

        assert_eq!(bytes, INDEX_BIN_FIXTURE);
    }

    proptest! {
        #[test]
        fn test_index_bin_roundtrip(
            // Levels are 3 bits, tile IDs are 22 bits, and offsets are counted in 512-byte blocks.
            // The offset bound keeps the end of every tile inside a u64.
            raw_entries in vec(
                (0u8..=7, 0u64..1 << 22, 1u64..=(u64::MAX - u64::from(u32::MAX)) / 512, 0u32..=u32::MAX),
                1..64
            )
        ) {
            let entries: Vec<TileIndexBinEntry> = raw_entries
                .into_iter()
                .map(|(level, tile_id, offset_block, size)| {
                    let graph_id = GraphId::try_from_components(level, tile_id, 0)
                        .expect("All components are within their field limits");
                    TileIndexBinEntry::new(graph_id, offset_block * 512, size)
                        .expect("Offsets are non-zero and 512-aligned by construction")
                })
                .collect();

            let bytes = serialize_index_bin(&entries).expect("The entry list is non-empty");
            let parsed = parse_index_bin(bytes).expect("Serialized bytes always parse");

            prop_assert_eq!(parsed, entries.as_slice());
            // Every entry is valid in an archive that ends where the last tile ends.
            let archive_len = parsed
                .iter()
                .map(|entry| entry.offset() + u64::from(entry.size()))
                .max()
                .expect("The entry list is non-empty");
            for entry in parsed {
                prop_assert!(entry.validated(archive_len).is_ok());
            }
        }
    }

    // Tragically, memory maps are not supported by Miri!
    #[cfg(not(miri))]
    #[test]
    fn test_get_tile() {
        let path = test_fixtures::andorra_tiles_tar();
        let provider =
            TarballTileProvider::new_readonly(path).expect("Unable to init tile provider");
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let tile_pointer = provider
            .get_pointer_for_tile_containing(graph_id)
            .expect("Unable to get tile");
        let tile_bytes = unsafe { tile_pointer.as_tile_bytes() };
        let tile = GraphTileView::try_from(tile_bytes).expect("Unable to deserialize tile");

        // Minimally test that we got the correct tile
        assert_eq!(tile.header().graph_id(), graph_id);
        assert_eq!(tile.header().graph_id().value(), graph_id.value());
    }

    // Tragically, memory maps are not supported by Miri!
    #[cfg(not(miri))]
    #[test]
    fn test_tiles_are_identical_to_directory() {
        // This test uses the directory tile provider as an oracle
        // to make sure the tarball reader is working as expected.
        // Probably goes without saying, but the tarball was created using
        // valhalla_build_extract from the andorra-tiles directory.

        // Indexes are all intentionally non-zero to test that the provider impl fetches based on the base ID
        let tile_ids = &[
            GraphId::try_from_components(0, 3015, 1).expect("Unable to create graph ID"),
            GraphId::try_from_components(1, 47701, 1).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 762485, 1).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 762486, 1).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 763925, 1).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 763926, 1).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 763927, 1).expect("Unable to create graph ID"),
        ];

        let base = test_fixtures::andorra_tiles_dir();
        let directory_provider =
            DirectoryGraphTileProvider::new(base, NonZeroUsize::new(1).unwrap());

        let tarball_path = test_fixtures::andorra_tiles_tar();
        let tarball_provider = TarballTileProvider::new_readonly(tarball_path.clone())
            .expect("Unable to init tile provider");
        let immutable_tarball_provider = unsafe {
            TarballTileProvider::new_immutable(tarball_path).expect("Unable to init tile provider")
        };

        for graph_id in tile_ids {
            let directory_tile = directory_provider
                .get_handle_for_tile_containing(*graph_id)
                .expect("Unable to get tile");
            let tarball_tile_pointer = tarball_provider
                .get_pointer_for_tile_containing(*graph_id)
                .expect("Unable to get tile");
            let tarball_tile_bytes = unsafe { tarball_tile_pointer.as_tile_bytes() };

            assert_eq!(directory_tile.borrow_owner(), tarball_tile_bytes);

            let immutable_tarball_tile_pointer = immutable_tarball_provider
                .get_handle_for_tile_containing(*graph_id)
                .expect("Unable to get tile");
            let immutable_tarball_tile_bytes = unsafe {
                immutable_tarball_tile_pointer
                    .borrow_owner()
                    .as_tile_bytes()
            };
            assert_eq!(directory_tile.borrow_owner(), immutable_tarball_tile_bytes);
        }
    }
}
