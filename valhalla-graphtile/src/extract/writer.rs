//! Manifest-first, single-pass streaming tar writer for tile extracts.
//!
//! The tar format makes every output offset computable *before writing a single byte*,
//! given a manifest of `(GraphId, size)` pairs.
//! [`write_extract`] gets the manifest from the [`TileBytesSource`]
//! (a tarball provider reads the sizes from its `index.bin`,
//! and a directory provider reads them from the file system),
//! so a caller never gives sizes by hand:
//!
//! - `index.bin` is one [`TileIndexBinEntry`] per tile,
//!   padded to a 512-byte boundary, preceded by its 512-byte tar header.
//! - Each tile contributes a 512-byte tar header plus its payload padded to 512 bytes.
//!
//! [`ExtractLayout`] is that pure computation.
//! The writer then streams the corresponding archive into any [`Write`],
//! with no `Seek`, no temp files, and no buffering of the whole archive.
//!
//! # Archive layout
//!
//! 1. `index.bin` is always the first entry.
//!    Valhalla C++ treats it as optional for local tarballs
//!    but requires it as the first entry for remotely-served tarballs,
//!    and Valinor's own reader requires it unconditionally.
//!    Writing it first satisfies every consumer
//!    and keeps HTTP range-request serving possible.
//! 2. Graph tiles follow, sorted ascending by (level, tile index),
//!    with spec-compliant entry paths (see [`GraphId::relative_path`])
//!    so that index-less consumers scanning the tar can still resolve them.
//!    Note that this canonical order differs from the `Ord` impl of [`GraphId`],
//!    which deliberately orders levels in reverse.
//! 3. The archive ends with the standard two-block end-of-archive marker.
//!
//! Output is byte-deterministic:
//! tar header metadata is fixed (mtime 0, uid/gid 0, mode 644, ustar format),
//! and the writer sorts its own manifest, so caller order never leaks into the output.

use crate::GraphId;
use crate::graph_id::InvalidGraphIdError;
use crate::tile_provider::{
    GraphTileProviderError, INDEX_BIN_ENTRY_NAME, InvalidIndexBinError, TAR_BLOCK_SIZE,
    TileBytesSource, TileIndexBinEntry, serialize_index_bin,
};
use std::io::Write;
use tar::{EntryType, Header};
use thiserror::Error;

/// A zeroed block (of [`TAR_BLOCK_SIZE`] bytes)
/// for payload padding and the end-of-archive marker.
#[expect(clippy::cast_possible_truncation, reason = "512 fits in every usize")]
const ZERO_BLOCK: [u8; TAR_BLOCK_SIZE as usize] = [0; TAR_BLOCK_SIZE as usize];

/// The length of the end-of-archive marker: two zero blocks.
const END_OF_ARCHIVE_LEN: u64 = 2 * TAR_BLOCK_SIZE;

/// The extension of graph tile files.
const TILE_EXTENSION: &str = "gph";

/// An error in the set of tiles of an extract.
///
/// The writer finds these errors before it writes any bytes.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum ExtractLayoutError {
    /// An extract containing no tiles is meaningless
    /// (and its `index.bin` would be malformed).
    #[error("the extract contains no tiles")]
    EmptyManifest,
    /// The same tile is requested more than once.
    ///
    /// Two graph IDs which differ only in the feature index are the same tile.
    #[error("the extract contains tile {0} more than once")]
    DuplicateTile(GraphId),
    /// The source gives a tile a size of zero.
    ///
    /// A graph tile always contains at least a header,
    /// so a size of zero is always an error in the source.
    #[error("the source gives tile {0} a size of zero")]
    EmptyTile(GraphId),
    /// A tile cannot be indexed.
    #[error("invalid index.bin: {0}")]
    InvalidIndexBin(#[from] InvalidIndexBinError),
}

/// An error while writing a tile extract.
///
/// `E` is the error type of the [`TileBytesSource`].
#[derive(Debug, Error)]
pub enum ExtractWriteError<E = GraphTileProviderError> {
    /// The requested tiles do not make a valid extract.
    #[error("invalid extract: {0}")]
    Layout(#[from] ExtractLayoutError),
    /// A requested tile is not in the source.
    #[error("tile {0} is not in the source")]
    MissingTile(GraphId),
    /// A requested graph ID cannot be converted into a tar entry path.
    #[error("invalid graph ID: {0}")]
    InvalidGraphId(#[from] InvalidGraphIdError),
    /// The source produced a tile whose length differs from the size that it reported.
    ///
    /// Sizes must match exactly:
    /// every downstream offset was computed from the reported sizes before any bytes were written,
    /// so a mismatch would silently corrupt the rest of the archive.
    /// This can happen if the source changes during the write
    /// (for example, if a tile file in a tile directory is replaced).
    #[error(
        "the source produced {actual} bytes for tile {graph_id}, but it reported a size of {expected} bytes"
    )]
    SizeMismatch {
        /// The base graph ID of the offending tile.
        graph_id: GraphId,
        /// The size that the source reported before the write.
        expected: u32,
        /// The length of the bytes actually produced by the source.
        actual: usize,
    },
    /// The source failed to give the size or the bytes of a tile.
    #[error("the source failed to produce tile {graph_id}: {source}")]
    Source {
        /// The base graph ID of the tile.
        graph_id: GraphId,
        /// The error from the source.
        source: E,
    },
    /// Writing to the destination failed.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

/// Writes a tile extract which contains the tiles of `tile_ids` into the destination.
///
/// Each ID is normalized to its base tile ID (see [`GraphId::tile_base_id`]),
/// and every tile is copied verbatim from the source.
/// The source can be any [`TileBytesSource`],
/// such as a [`TarballTileProvider`](crate::tile_provider::TarballTileProvider)
/// or a [`DirectoryGraphTileProvider`](crate::tile_provider::DirectoryGraphTileProvider).
///
/// The archive is streamed sequentially in a single pass
/// (no `Seek`, no temp files, no buffering of the whole archive):
/// the `index.bin` entry first,
/// then one entry per tile in canonical archive order
/// (ascending by level, then tile index),
/// and finally the two-block end-of-archive marker.
/// The order of `tile_ids` does not matter.
/// Output is byte-deterministic:
/// the same tiles always produce byte-identical output.
///
/// Returns the total number of bytes written.
///
/// # Errors
///
/// This fails before it writes any bytes if `tile_ids` is empty,
/// contains the same tile more than once,
/// or contains a tile which is not in the source.
/// It fails during the write if the source fails to produce a tile,
/// if a tile's length differs from the size that the source reported,
/// or if writing to the destination fails.
///
/// The destination contents are unspecified after an error;
/// streaming destinations cannot roll back partially written entries.
pub fn write_extract<S, W>(
    source: &S,
    tile_ids: &[GraphId],
    dest: W,
) -> Result<u64, ExtractWriteError<S::Error>>
where
    S: TileBytesSource,
    W: Write,
{
    let manifest = tile_ids
        .iter()
        .map(|graph_id| {
            let base_id = graph_id.tile_base_id();
            match source.tile_size(base_id) {
                Ok(Some(size)) => Ok((base_id, size)),
                Ok(None) => Err(ExtractWriteError::MissingTile(base_id)),
                Err(source) => Err(ExtractWriteError::Source {
                    graph_id: base_id,
                    source,
                }),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    let layout = ExtractLayout::from_manifest(&manifest)?;
    write_layout(&layout, source, dest)
}

/// The precomputed layout of an extract tarball.
///
/// This is the pure "manifest → offsets" half of the writer:
/// given `(GraphId, size)` pairs,
/// it computes the byte offset of every tile payload in the output archive
/// and the exact total archive length,
/// without performing any I/O.
///
/// The layout sorts the manifest into the canonical archive order
/// (ascending by level, then tile index),
/// so the index entries are in the exact order
/// their tiles appear in the archive.
#[derive(Debug)]
struct ExtractLayout {
    /// One index entry per tile, in canonical archive order.
    entries: Vec<TileIndexBinEntry>,
    /// The total length of the archive in bytes, including the end-of-archive marker.
    total_len: u64,
}

impl ExtractLayout {
    /// Computes the archive layout for a manifest of `(GraphId, size)` pairs.
    ///
    /// The manifest may be in any order (the layout sorts a copy into canonical order),
    /// but every graph ID must be a *base* tile ID
    /// (see [`GraphId::tile_base_id`]),
    /// and each tile may appear at most once.
    ///
    /// # Errors
    ///
    /// This fails if the manifest is empty, contains duplicate tiles,
    /// contains a tile with a size of zero,
    /// or contains an ID which is not a valid base tile ID.
    fn from_manifest(manifest: &[(GraphId, u32)]) -> Result<Self, ExtractLayoutError> {
        if manifest.is_empty() {
            return Err(ExtractLayoutError::EmptyManifest);
        }

        let mut sorted = manifest.to_vec();
        sorted.sort_unstable_by_key(|(graph_id, _)| (graph_id.level(), graph_id.tile_id()));

        // The archive is a sequence of entries, and `index.bin` is the first entry (at offset 0).
        // `next_entry_offset` is the offset of the header block of the next entry;
        // the payload of that entry starts one block later.
        let index_len = (size_of::<TileIndexBinEntry>() * sorted.len()) as u64;
        let mut next_entry_offset = entry_len(index_len);

        let mut entries = Vec::with_capacity(sorted.len());
        for (i, &(graph_id, size)) in sorted.iter().enumerate() {
            // Equal (level, tile index) pairs are adjacent after the sort.
            if i > 0 && sorted[i - 1].0 == graph_id {
                return Err(ExtractLayoutError::DuplicateTile(graph_id));
            }
            if size == 0 {
                return Err(ExtractLayoutError::EmptyTile(graph_id));
            }

            let payload_offset = next_entry_offset + TAR_BLOCK_SIZE;
            entries.push(TileIndexBinEntry::new(graph_id, payload_offset, size)?);
            next_entry_offset += entry_len(u64::from(size));
        }

        Ok(Self {
            entries,
            total_len: next_entry_offset + END_OF_ARCHIVE_LEN,
        })
    }

    /// The index entries of the archive, in canonical archive order
    /// (ascending by level, then tile index).
    ///
    /// Serializing these with [`serialize_index_bin`]
    /// yields exactly the `index.bin` payload of the archive.
    #[inline]
    fn index_entries(&self) -> &[TileIndexBinEntry] {
        &self.entries
    }

    /// The exact total length of the archive in bytes,
    /// including the end-of-archive marker.
    ///
    /// This is always a multiple of 512,
    /// and is known before a single byte is written.
    #[inline]
    fn total_len(&self) -> u64 {
        self.total_len
    }
}

/// The length of a tar entry with a payload of `payload_len` bytes:
/// a header block, then the payload padded to a whole number of blocks.
const fn entry_len(payload_len: u64) -> u64 {
    TAR_BLOCK_SIZE + payload_len.next_multiple_of(TAR_BLOCK_SIZE)
}

/// Streams the archive of a layout into the destination,
/// and returns the number of bytes written.
fn write_layout<S, W>(
    layout: &ExtractLayout,
    source: &S,
    dest: W,
) -> Result<u64, ExtractWriteError<S::Error>>
where
    S: TileBytesSource,
    W: Write,
{
    let mut dest = CountingWriter {
        inner: dest,
        position: 0,
    };

    let index_bytes =
        serialize_index_bin(layout.index_entries()).map_err(ExtractLayoutError::from)?;
    write_entry(&mut dest, INDEX_BIN_ENTRY_NAME, index_bytes)?;

    for entry in layout.index_entries() {
        // Infallible in practice: the layout was constructed from valid base tile IDs.
        let graph_id = entry.graph_id().map_err(ExtractLayoutError::from)?;
        let path = graph_id.relative_path(TILE_EXTENSION)?;
        let expected = entry.size();

        source
            .with_tile_bytes(graph_id, |tile_bytes| {
                if tile_bytes.len() != expected as usize {
                    return Err(ExtractWriteError::SizeMismatch {
                        graph_id,
                        expected,
                        actual: tile_bytes.len(),
                    });
                }
                let payload_offset = write_entry(&mut dest, &path, tile_bytes)?;
                debug_assert_eq!(
                    payload_offset,
                    entry.offset(),
                    "the payload of {graph_id} is not where index.bin says it is"
                );
                Ok(())
            })
            .map_err(|source| ExtractWriteError::Source { graph_id, source })??;
    }

    dest.write_all(&ZERO_BLOCK)?;
    dest.write_all(&ZERO_BLOCK)?;
    dest.flush()?;

    debug_assert_eq!(dest.position, layout.total_len());
    Ok(dest.position)
}

/// Writes a single tar entry: a 512-byte header, the payload, and zero padding to a block boundary.
///
/// Returns the offset of the payload in the archive.
fn write_entry<W: Write>(
    dest: &mut CountingWriter<W>,
    path: &str,
    payload: &[u8],
) -> std::io::Result<u64> {
    // Determinism requires every header field to be fixed:
    // ustar format, mtime 0, uid/gid 0 (with empty user/group names), mode 644.
    let mut header = Header::new_ustar();
    header.set_entry_type(EntryType::Regular);
    header.set_path(path)?;
    header.set_size(payload.len() as u64);
    header.set_mode(0o644);
    header.set_uid(0);
    header.set_gid(0);
    header.set_mtime(0);
    header.set_cksum();

    dest.write_all(header.as_bytes())?;
    let payload_offset = dest.position;
    dest.write_all(payload)?;

    let padding = payload.len().next_multiple_of(ZERO_BLOCK.len()) - payload.len();
    dest.write_all(&ZERO_BLOCK[..padding])?;

    Ok(payload_offset)
}

/// A writer which counts the bytes written through it.
///
/// The writer uses the count to check the precomputed layout,
/// and to return the number of bytes that it actually wrote.
struct CountingWriter<W> {
    inner: W,
    /// The number of bytes written so far, which is the offset of the next byte in the archive.
    position: u64,
}

impl<W: Write> Write for CountingWriter<W> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let written = self.inner.write(buf)?;
        self.position += written as u64;
        Ok(written)
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_fixtures;
    use crate::tile_provider::{DirectoryGraphTileProvider, TarballTileProvider, parse_index_bin};
    use proptest::collection::btree_map;
    use proptest::{prop_assert, prop_assert_eq, proptest};
    use std::collections::{HashMap, HashSet};
    use std::io::Read;
    use std::num::NonZeroUsize;
    use tar::Archive;

    /// Helper to construct a base tile [`GraphId`].
    fn tile(level: u8, tile_id: u64) -> GraphId {
        GraphId::try_from_components(level, tile_id, 0).expect("valid tile ID in test")
    }

    /// An in-memory tile source for driving the writer without any I/O.
    #[derive(Default)]
    struct MemorySource {
        tiles: HashMap<GraphId, Vec<u8>>,
        /// Sizes which `tile_size` reports in place of the real sizes.
        reported_sizes: HashMap<GraphId, u32>,
        /// Tiles which the source has, but whose bytes it fails to produce.
        unreadable: HashSet<GraphId>,
    }

    /// The error of a [`MemorySource`] when it cannot produce a tile.
    #[derive(Debug, Error, PartialEq, Eq)]
    #[error("the tile is not readable")]
    struct Unreadable;

    impl MemorySource {
        /// A source which contains one tile of the given size for each manifest entry.
        fn from_manifest(manifest: &[(GraphId, u32)]) -> Self {
            let tiles = manifest
                .iter()
                .map(|(graph_id, size)| {
                    // Distinctive fill bytes so tiles cannot be confused with each other
                    // (or with zero padding).
                    let fill =
                        0x11 * (1 + u8::try_from(graph_id.tile_id() % 13).expect("13 fits in u8"));
                    (*graph_id, vec![fill; *size as usize])
                })
                .collect();
            Self {
                tiles,
                ..Self::default()
            }
        }

        fn tile_ids(&self) -> Vec<GraphId> {
            self.tiles.keys().copied().collect()
        }
    }

    impl TileBytesSource for MemorySource {
        type Error = Unreadable;

        fn tile_size(&self, graph_id: GraphId) -> Result<Option<u32>, Self::Error> {
            let graph_id = graph_id.tile_base_id();
            if let Some(size) = self.reported_sizes.get(&graph_id) {
                return Ok(Some(*size));
            }
            Ok(self
                .tiles
                .get(&graph_id)
                .map(|tile_bytes| u32::try_from(tile_bytes.len()).expect("test tiles are small")))
        }

        fn with_tile_bytes<F, T>(&self, graph_id: GraphId, process: F) -> Result<T, Self::Error>
        where
            F: FnOnce(&[u8]) -> T,
        {
            let graph_id = graph_id.tile_base_id();
            if self.unreadable.contains(&graph_id) {
                return Err(Unreadable);
            }
            self.tiles
                .get(&graph_id)
                .map(|tile_bytes| process(tile_bytes))
                .ok_or(Unreadable)
        }
    }

    /// A manifest which is deliberately *not* in canonical order
    /// (and not in `GraphId` order either),
    /// with sizes exercising all padding cases:
    /// an exact block multiple, a one-byte remainder, and a one-byte shortfall.
    fn scrambled_manifest() -> Vec<(GraphId, u32)> {
        vec![
            (tile(2, 762_485), 100),
            (tile(0, 3015), 512),
            (tile(2, 762_484), 1024),
            (tile(1, 47_701), 513),
            (tile(1, 47_700), 511),
        ]
    }

    /// Reads the archive with the `tar` crate (an independent tar reader),
    /// and returns the path and payload offset of each entry, in archive order.
    fn read_entries(archive_bytes: &[u8]) -> Vec<(String, u64)> {
        Archive::new(archive_bytes)
            .entries()
            .expect("the archive is readable")
            .map(|entry| {
                let entry = entry.expect("every entry is readable");
                let path = entry
                    .path()
                    .expect("every entry path is valid")
                    .to_string_lossy()
                    .into_owned();
                (path, entry.raw_file_position())
            })
            .collect()
    }

    /// Reads the `index.bin` payload, which is the first entry of the archive.
    fn read_index_bytes(archive_bytes: &[u8]) -> Vec<u8> {
        let mut index_bytes = Vec::new();
        Archive::new(archive_bytes)
            .entries()
            .expect("the archive is readable")
            .next()
            .expect("the archive has entries")
            .expect("the index entry is readable")
            .read_to_end(&mut index_bytes)
            .expect("the index payload is readable");
        index_bytes
    }

    #[test]
    fn test_layout_offsets() {
        const B: u64 = TAR_BLOCK_SIZE;

        let layout = ExtractLayout::from_manifest(&scrambled_manifest())
            .expect("the manifest is well-formed");

        // Each entry is a header block, then its payload padded to whole blocks.
        // The index has 5 tiles × 16 bytes = 80 bytes, so the index entry is 2 blocks,
        // and the first tile header is at block 2.
        // The payload of each tile starts one block after its header.
        let expected = [
            // (graph_id, payload offset, size), in canonical (level, tile index) order
            (tile(0, 3015), 3 * B, 512), // header at block 2; payload is 1 block
            (tile(1, 47_700), 5 * B, 511), // header at block 4; payload is padded to 1 block
            (tile(1, 47_701), 7 * B, 513), // header at block 6; payload is padded to 2 blocks
            (tile(2, 762_484), 10 * B, 1024), // header at block 9; payload is 2 blocks
            (tile(2, 762_485), 13 * B, 100), // header at block 12; payload is padded to 1 block
        ];

        assert_eq!(layout.index_entries().len(), expected.len());
        for (entry, (graph_id, offset, size)) in layout.index_entries().iter().zip(expected) {
            assert_eq!(entry.graph_id().unwrap(), graph_id);
            assert_eq!(entry.offset(), offset);
            assert_eq!(entry.size(), size);
        }

        // The last payload ends at block 14, and the end-of-archive marker is 2 blocks.
        assert_eq!(layout.total_len(), 16 * B);
    }

    #[test]
    fn test_layout_rejects_empty_manifest() {
        assert_eq!(
            ExtractLayout::from_manifest(&[]).unwrap_err(),
            ExtractLayoutError::EmptyManifest
        );
    }

    #[test]
    fn test_layout_rejects_duplicate_tiles() {
        let manifest = [(tile(1, 47_701), 100), (tile(1, 47_701), 100)];
        assert_eq!(
            ExtractLayout::from_manifest(&manifest).unwrap_err(),
            ExtractLayoutError::DuplicateTile(tile(1, 47_701))
        );
    }

    #[test]
    fn test_layout_rejects_empty_tiles() {
        let manifest = [(tile(0, 3015), 512), (tile(1, 47_701), 0)];
        assert_eq!(
            ExtractLayout::from_manifest(&manifest).unwrap_err(),
            ExtractLayoutError::EmptyTile(tile(1, 47_701))
        );
    }

    #[test]
    fn test_layout_rejects_non_base_tile_ids() {
        let with_feature_index =
            GraphId::try_from_components(1, 47_701, 7).expect("valid graph ID in test");
        assert_eq!(
            ExtractLayout::from_manifest(&[(with_feature_index, 100)]).unwrap_err(),
            ExtractLayoutError::InvalidIndexBin(InvalidIndexBinError::FeatureIndex(
                with_feature_index
            ))
        );
    }

    #[test]
    fn test_write_rejects_empty_tile_list() {
        let source = MemorySource::default();
        assert!(matches!(
            write_extract(&source, &[], Vec::new()),
            Err(ExtractWriteError::Layout(ExtractLayoutError::EmptyManifest))
        ));
    }

    #[test]
    fn test_write_rejects_the_same_tile_twice() {
        let source = MemorySource::from_manifest(&[(tile(1, 47_701), 100)]);
        // These IDs differ only in the feature index, so they are the same tile.
        let with_feature_index =
            GraphId::try_from_components(1, 47_701, 7).expect("valid graph ID in test");
        assert!(matches!(
            write_extract(&source, &[tile(1, 47_701), with_feature_index], Vec::new()),
            Err(ExtractWriteError::Layout(ExtractLayoutError::DuplicateTile(graph_id)))
                if graph_id == tile(1, 47_701)
        ));
    }

    #[test]
    fn test_write_rejects_missing_tiles() {
        let source = MemorySource::from_manifest(&[(tile(0, 3015), 100)]);
        let mut dest = Vec::new();
        assert!(matches!(
            write_extract(&source, &[tile(0, 3015), tile(2, 0)], &mut dest),
            Err(ExtractWriteError::MissingTile(graph_id)) if graph_id == tile(2, 0)
        ));
        assert!(dest.is_empty(), "a missing tile is found before any write");
    }

    #[test]
    fn test_write_rejects_size_mismatch() {
        // The source produces 99 bytes, but it reports a size of 100.
        let mut source = MemorySource::from_manifest(&[(tile(0, 3015), 99)]);
        source.reported_sizes.insert(tile(0, 3015), 100);

        assert!(matches!(
            write_extract(&source, &[tile(0, 3015)], Vec::new()),
            Err(ExtractWriteError::SizeMismatch {
                graph_id,
                expected: 100,
                actual: 99,
            }) if graph_id == tile(0, 3015)
        ));
    }

    #[test]
    fn test_write_reports_source_errors() {
        let mut source = MemorySource::from_manifest(&[(tile(0, 3015), 100)]);
        source.unreadable.insert(tile(0, 3015));

        assert!(matches!(
            write_extract(&source, &[tile(0, 3015)], Vec::new()),
            Err(ExtractWriteError::Source {
                graph_id,
                source: Unreadable
            }) if graph_id == tile(0, 3015)
        ));
    }

    #[test]
    fn test_archive_invariants() {
        let manifest = scrambled_manifest();
        let source = MemorySource::from_manifest(&manifest);

        let mut archive_bytes = Vec::new();
        let written = write_extract(&source, &source.tile_ids(), &mut archive_bytes)
            .expect("the source is well-formed");

        assert_eq!(written, archive_bytes.len() as u64);
        assert!(archive_bytes.len().is_multiple_of(ZERO_BLOCK.len()));

        // The archive must list index.bin first,
        // then the tiles in canonical (level, tile index) order under spec-compliant paths.
        let entries = read_entries(&archive_bytes);
        let entry_paths: Vec<&str> = entries.iter().map(|(path, _)| path.as_str()).collect();
        assert_eq!(
            entry_paths,
            vec![
                "index.bin",
                "0/003/015.gph",
                "1/047/700.gph",
                "1/047/701.gph",
                "2/000/762/484.gph",
                "2/000/762/485.gph",
            ]
        );

        // The index says where each payload starts,
        // and an independent tar reader finds each payload at the same offset.
        let index_bytes = read_index_bytes(&archive_bytes);
        let index_entries = parse_index_bin(&index_bytes).expect("the index parses");
        assert_eq!(index_entries.len(), manifest.len());

        for (index_entry, (_, payload_offset)) in index_entries.iter().zip(&entries[1..]) {
            assert_eq!(index_entry.offset(), *payload_offset);

            // The payload at the indexed offset is byte-identical to the source tile.
            let graph_id = index_entry.graph_id().expect("the entry ID is valid");
            let start = usize::try_from(index_entry.offset()).expect("the offset fits in memory");
            let payload = &archive_bytes[start..start + index_entry.size() as usize];
            source
                .with_tile_bytes(graph_id, |tile_bytes| assert_eq!(payload, tile_bytes))
                .expect("the tile is in the source");
        }
    }

    #[test]
    fn test_determinism() {
        let source = MemorySource::from_manifest(&scrambled_manifest());
        let tile_ids = source.tile_ids();

        let mut first = Vec::new();
        write_extract(&source, &tile_ids, &mut first).expect("first write succeeds");

        // A reordered tile list must not change the output either:
        // the writer sorts its own copy.
        let mut reversed = tile_ids;
        reversed.reverse();
        let mut second = Vec::new();
        write_extract(&source, &reversed, &mut second).expect("second write succeeds");

        assert_eq!(first, second);
    }

    proptest! {
        #[test]
        fn test_archive_matches_independent_reader(
            // Unique tiles (the map keys) on the three standard levels,
            // with sizes that cover the padding cases around one and several blocks.
            tiles in btree_map((0u8..=2, 0u64..4050), 1u32..=2049, 1..32)
        ) {
            let manifest: Vec<(GraphId, u32)> = tiles
                .into_iter()
                .map(|((level, tile_id), size)| (tile(level, tile_id), size))
                .collect();
            let source = MemorySource::from_manifest(&manifest);

            let mut archive_bytes = Vec::new();
            let written = write_extract(&source, &source.tile_ids(), &mut archive_bytes)
                .expect("the source is well-formed");
            let layout = ExtractLayout::from_manifest(&manifest).expect("the manifest is well-formed");
            prop_assert_eq!(written, archive_bytes.len() as u64);
            prop_assert_eq!(written, layout.total_len());

            // Every index entry points at the payload that the tar reader finds,
            // under the path of the same tile.
            let entries = read_entries(&archive_bytes);
            prop_assert_eq!(entries.len(), manifest.len() + 1);
            for (index_entry, (path, payload_offset)) in layout.index_entries().iter().zip(&entries[1..]) {
                let graph_id = index_entry.graph_id().expect("the entry ID is valid");
                prop_assert_eq!(index_entry.offset(), *payload_offset);
                prop_assert_eq!(path, &graph_id.relative_path(TILE_EXTENSION).expect("valid tile"));
                prop_assert!(index_entry.offset().is_multiple_of(TAR_BLOCK_SIZE));
            }
        }
    }

    // Tragically, memory maps are not supported by Miri!
    #[cfg(not(miri))]
    #[test]
    fn test_andorra_round_trip() {
        let source_provider = TarballTileProvider::new_readonly(test_fixtures::andorra_tiles_tar())
            .expect("Unable to init the source tile provider");

        // A hand-picked subset of the fixture, spanning all three standard levels,
        // deliberately not in canonical order,
        // and with one non-zero feature index to test base ID normalization.
        let tile_ids = [
            tile(2, 763_926),
            tile(0, 3015),
            GraphId::try_from_components(1, 47_701, 42).expect("valid graph ID in test"),
            tile(2, 762_485),
        ];
        // A fixture tile which is *not* part of the subset.
        let excluded = tile(2, 763_925);
        assert!(source_provider.tile_size(excluded).unwrap().is_some());

        let mut archive_bytes = Vec::new();
        let written = write_extract(&source_provider, &tile_ids, &mut archive_bytes)
            .expect("the extract writes cleanly");
        assert_eq!(written, archive_bytes.len() as u64);

        // Determinism on real data: a second run is byte-identical.
        let mut second = Vec::new();
        write_extract(&source_provider, &tile_ids, &mut second).expect("second write succeeds");
        assert_eq!(archive_bytes, second);

        // Round-trip: Valinor's own reader opens the extract,
        // and every tile is byte-identical to the source.
        // The temporary file is removed on drop, even if an assertion fails.
        let mut extract_file = tempfile::NamedTempFile::new().expect("a temporary file is created");
        extract_file
            .write_all(&archive_bytes)
            .expect("the extract is written to disk");

        let extract_provider = TarballTileProvider::new_readonly(extract_file.path())
            .expect("the generated extract opens cleanly");

        for graph_id in tile_ids {
            extract_provider
                .with_tile_bytes(graph_id, |extract_bytes| {
                    source_provider
                        .with_tile_bytes(graph_id, |source_bytes| {
                            assert_eq!(extract_bytes, source_bytes);
                        })
                        .expect("the tile is in the source");
                })
                .expect("the tile is in the extract");
        }

        // Tiles outside the subset did not leak into the extract.
        assert!(extract_provider.tile_size(excluded).unwrap().is_none());
    }

    // Tragically, memory maps are not supported by Miri!
    #[cfg(not(miri))]
    #[test]
    fn test_directory_and_tarball_sources_write_the_same_extract() {
        // The tarball fixture was made from the directory fixture with valhalla_build_extract,
        // so both sources contain the same tiles, and the extracts must be byte-identical.
        let tarball = TarballTileProvider::new_readonly(test_fixtures::andorra_tiles_tar())
            .expect("Unable to init the tarball tile provider");
        let directory = DirectoryGraphTileProvider::new(
            test_fixtures::andorra_tiles_dir(),
            NonZeroUsize::new(1).unwrap(),
        );

        // Every tile of the fixture.
        let tile_ids: Vec<GraphId> = tarball.tile_ids().copied().collect();
        assert!(tile_ids.len() > 1);

        let mut from_tarball = Vec::new();
        write_extract(&tarball, &tile_ids, &mut from_tarball)
            .expect("the extract writes cleanly from the tarball");
        let mut from_directory = Vec::new();
        write_extract(&directory, &tile_ids, &mut from_directory)
            .expect("the extract writes cleanly from the directory");
        assert_eq!(from_tarball, from_directory);

        // A tile which is in neither fixture fails the same way for both sources.
        for result in [
            write_extract(&tarball, &[tile(0, 3015), tile(2, 0)], Vec::new()),
            write_extract(&directory, &[tile(0, 3015), tile(2, 0)], Vec::new()),
        ] {
            assert!(matches!(
                result,
                Err(ExtractWriteError::MissingTile(graph_id)) if graph_id == tile(2, 0)
            ));
        }
    }
}
