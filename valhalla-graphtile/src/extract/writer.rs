//! Manifest-first, single-pass streaming tar writer for tile extracts.
//!
//! The tar format makes every output offset computable *before writing a single byte*,
//! given a manifest of `(GraphId, size)` pairs
//! (which we always have, because the source provider's tile index stores sizes):
//!
//! - `index.bin` is one [`TileIndexBinEntry`] per tile,
//!   padded to a 512-byte boundary, preceded by its 512-byte tar header.
//! - Each tile contributes a 512-byte tar header plus its payload padded to 512 bytes.
//!
//! [`ExtractLayout`] is that pure computation;
//! [`write_extract_from_source`] streams the corresponding archive into any [`Write`],
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
//!    with spec-compliant entry paths (`level/xxx/yyy….gph`)
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
    TarballTileProvider, TileIndexBinEntry, serialize_index_bin,
};
use std::io::Write;
use tar::{EntryType, Header};
use thiserror::Error;

/// A zeroed block (of [`TAR_BLOCK_SIZE`] bytes)
/// for payload padding and the end-of-archive marker.
#[expect(clippy::cast_possible_truncation, reason = "512 fits in every usize")]
const ZERO_BLOCK: [u8; TAR_BLOCK_SIZE as usize] = [0; TAR_BLOCK_SIZE as usize];

/// An error in an extract manifest.
///
/// The layout finds these errors before the writer writes any bytes.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum ExtractLayoutError {
    /// An extract containing no tiles is meaningless
    /// (and its `index.bin` would be malformed).
    #[error("the extract manifest contains no tiles")]
    EmptyManifest,
    /// The manifest contains the same tile more than once.
    #[error("the extract manifest contains tile {0} more than once")]
    DuplicateTile(GraphId),
    /// The manifest gives a tile a size of zero.
    ///
    /// A graph tile always contains at least a header,
    /// so a size of zero is always an error in the manifest.
    #[error("the extract manifest gives tile {0} a size of zero")]
    EmptyTile(GraphId),
    /// The manifest contains an ID which cannot be indexed.
    #[error("invalid index.bin: {0}")]
    InvalidIndexBin(#[from] InvalidIndexBinError),
}

/// An error while writing a tile extract.
///
/// `E` is the error type of the [`TileBytesSource`].
#[derive(Debug, Error)]
pub enum ExtractWriteError<E = GraphTileProviderError> {
    /// The manifest is not valid (see [`ExtractLayout::from_manifest`]).
    #[error("invalid manifest: {0}")]
    Layout(#[from] ExtractLayoutError),
    /// A requested tile is not in the source extract.
    #[error("tile {0} is not in the source extract")]
    MissingTile(GraphId),
    /// A graph ID in the manifest cannot be converted into a tar entry path.
    #[error("invalid graph ID: {0}")]
    InvalidGraphId(#[from] InvalidGraphIdError),
    /// The byte source produced a tile whose length differs from the manifest size.
    ///
    /// Sizes must match exactly:
    /// every downstream offset was computed from the manifest before any bytes were written,
    /// so a mismatch would silently corrupt the rest of the archive.
    #[error(
        "the byte source produced {actual} bytes for tile {graph_id}, but the manifest size is {expected}"
    )]
    SizeMismatch {
        /// The base graph ID of the offending tile.
        graph_id: GraphId,
        /// The size recorded in the manifest.
        expected: u32,
        /// The length of the bytes actually produced by the source.
        actual: usize,
    },
    /// The byte source failed to produce a tile.
    #[error("the byte source failed to produce tile {graph_id}: {source}")]
    Source {
        /// The base graph ID of the tile.
        graph_id: GraphId,
        /// The error from the byte source.
        source: E,
    },
    /// Writing to the destination failed.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

/// A source of tile bytes for extract writing.
///
/// The writer core ([`write_extract_from_source`]) is generic over this trait,
/// so any byte lookup can drive it:
/// a memory-mapped tarball in production, or an in-memory map in tests.
///
/// The callback style (rather than returning a slice)
/// lets implementations hand out bytes borrowed from per-call state,
/// such as a tile pointer into a memory map.
pub trait TileBytesSource {
    /// The error type of this source.
    type Error: core::error::Error + 'static;

    /// Calls `process` with the raw bytes of the tile containing the given graph ID.
    ///
    /// # Errors
    ///
    /// This fails if the tile does not exist in the source,
    /// or if fetching its bytes fails.
    fn with_tile_bytes<F, T>(&self, graph_id: GraphId, process: F) -> Result<T, Self::Error>
    where
        F: FnOnce(&[u8]) -> T;
}

impl<const MUT: bool> TileBytesSource for TarballTileProvider<MUT, false> {
    type Error = GraphTileProviderError;

    #[inline]
    fn with_tile_bytes<F, T>(&self, graph_id: GraphId, process: F) -> Result<T, Self::Error>
    where
        F: FnOnce(&[u8]) -> T,
    {
        let tile_pointer = self.get_pointer_for_tile_containing(graph_id)?;
        // SAFETY: The provider checks at construction that every index range lies inside the memory map.
        // We assume that the underlying memory map has not changed in a way that would render the tile invalid
        // (see the safety discussion on TarballTileProvider).
        let tile_bytes = unsafe { tile_pointer.as_tile_bytes() };
        Ok(process(tile_bytes))
    }
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
pub struct ExtractLayout {
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
    pub fn from_manifest(manifest: &[(GraphId, u32)]) -> Result<Self, ExtractLayoutError> {
        if manifest.is_empty() {
            return Err(ExtractLayoutError::EmptyManifest);
        }

        let mut sorted = manifest.to_vec();
        sorted.sort_unstable_by_key(|(graph_id, _)| (graph_id.level(), graph_id.tile_id()));

        // The index entry for a tile records the offset of its *payload*,
        // so the first tile payload lands one header block past the index entry:
        // the index header block, the padded index payload, and the tile's own header block.
        let index_len = (size_of::<TileIndexBinEntry>() * sorted.len()) as u64;
        let mut header_offset = TAR_BLOCK_SIZE + index_len.next_multiple_of(TAR_BLOCK_SIZE);

        let mut entries = Vec::with_capacity(sorted.len());
        for (i, (graph_id, size)) in sorted.iter().enumerate() {
            // Equal (level, tile index) pairs are adjacent after the sort.
            if i > 0 && sorted[i - 1].0 == *graph_id {
                return Err(ExtractLayoutError::DuplicateTile(*graph_id));
            }
            if *size == 0 {
                return Err(ExtractLayoutError::EmptyTile(*graph_id));
            }

            let payload_offset = header_offset + TAR_BLOCK_SIZE;
            entries.push(TileIndexBinEntry::new(*graph_id, payload_offset, *size)?);
            header_offset = payload_offset + u64::from(*size).next_multiple_of(TAR_BLOCK_SIZE);
        }

        Ok(Self {
            entries,
            // The archive ends with two zero blocks (the standard end-of-archive marker).
            total_len: header_offset + 2 * TAR_BLOCK_SIZE,
        })
    }

    /// The index entries of the archive, in canonical archive order
    /// (ascending by level, then tile index).
    ///
    /// Serializing these with
    /// [`serialize_index_bin`](crate::tile_provider::serialize_index_bin)
    /// yields exactly the `index.bin` payload of the archive.
    #[inline]
    pub fn index_entries(&self) -> &[TileIndexBinEntry] {
        &self.entries
    }

    /// The exact total length of the archive in bytes,
    /// including the end-of-archive marker.
    ///
    /// This is always a multiple of 512,
    /// and is known before a single byte is written,
    /// which makes it possible to set a `Content-Length` up front
    /// when streaming an extract over HTTP.
    #[inline]
    pub fn total_len(&self) -> u64 {
        self.total_len
    }
}

/// Writes a tile extract sourced from an existing tarball.
///
/// This is a convenience wrapper over [`write_extract_from_source`]:
/// the manifest is built by resolving each ID in `tile_ids`
/// (normalized to its base tile ID)
/// against the source provider's tile index,
/// and tile bytes are read from the provider's memory map.
/// See [`write_extract_from_source`] for the full output format contract.
///
/// Returns the total number of bytes written.
///
/// # Errors
///
/// This fails if `tile_ids` is empty, contains duplicate tiles,
/// or references a tile which is not present in the source tarball.
/// It also fails if writing to the destination fails.
pub fn write_extract<const MUT: bool, W: Write>(
    provider: &TarballTileProvider<MUT, false>,
    tile_ids: &[GraphId],
    dest: W,
) -> Result<u64, ExtractWriteError> {
    let manifest = tile_ids
        .iter()
        .map(|graph_id| {
            let base_id = graph_id.tile_base_id();
            provider
                .tile_size(base_id)
                .map(|size| (base_id, size))
                .ok_or(ExtractWriteError::MissingTile(base_id))
        })
        .collect::<Result<Vec<_>, _>>()?;

    write_extract_from_source(&manifest, provider, dest)
}

/// Writes a tile extract as a tar archive into the destination.
///
/// The archive is streamed sequentially in a single pass
/// (no `Seek`, no temp files, no buffering of the whole archive):
/// the `index.bin` entry first,
/// then one entry per manifest tile in canonical archive order
/// (ascending by level, then tile index),
/// and finally the two-block end-of-archive marker.
/// The manifest may be in any order; the writer sorts its own copy.
///
/// Output is byte-deterministic:
/// the same manifest and tile bytes always produce byte-identical output.
///
/// Returns the total number of bytes written,
/// which always equals [`ExtractLayout::total_len`] for the same manifest.
///
/// # Errors
///
/// This fails if the layout cannot be computed from the manifest
/// (see [`ExtractLayout::from_manifest`]),
/// if the source fails to produce a tile,
/// if a tile's length differs from its manifest size,
/// or if writing to the destination fails.
///
/// The destination contents are unspecified after an error;
/// streaming destinations cannot roll back partially written entries.
pub fn write_extract_from_source<S, W>(
    manifest: &[(GraphId, u32)],
    source: &S,
    mut dest: W,
) -> Result<u64, ExtractWriteError<S::Error>>
where
    S: TileBytesSource,
    W: Write,
{
    let layout = ExtractLayout::from_manifest(manifest)?;

    let index_bytes =
        serialize_index_bin(layout.index_entries()).map_err(ExtractLayoutError::from)?;
    write_entry(&mut dest, INDEX_BIN_ENTRY_NAME, index_bytes)?;

    for entry in layout.index_entries() {
        // Infallible in practice: the layout was constructed from valid base tile IDs.
        let graph_id = entry.graph_id().map_err(ExtractLayoutError::from)?;
        let path = tar_entry_path(graph_id)?;
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
                write_entry(&mut dest, &path, tile_bytes).map_err(ExtractWriteError::from)
            })
            .map_err(|source| ExtractWriteError::Source { graph_id, source })??;
    }

    // The standard end-of-archive marker: two zero blocks.
    dest.write_all(&ZERO_BLOCK)?;
    dest.write_all(&ZERO_BLOCK)?;
    dest.flush()?;

    Ok(layout.total_len())
}

/// Writes a single tar entry: a 512-byte header, the payload, and zero padding to a block boundary.
fn write_entry<W: Write>(dest: &mut W, path: &str, payload: &[u8]) -> std::io::Result<()> {
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
    dest.write_all(payload)?;

    let padding = payload.len().next_multiple_of(ZERO_BLOCK.len()) - payload.len();
    dest.write_all(&ZERO_BLOCK[..padding])
}

/// Constructs the spec-compliant tar entry path for a tile.
///
/// The first component is the bare level digit;
/// the remaining components are the tile index,
/// zero-padded to the level's width and split into 3-digit groups
/// (e.g. `2/000/762/485.gph`).
/// Tar entry names always use `/` separators, regardless of platform.
fn tar_entry_path(graph_id: GraphId) -> Result<String, InvalidGraphIdError> {
    let path = graph_id.file_path("gph")?;
    let components: Vec<_> = path
        .iter()
        .map(|component| component.to_string_lossy())
        .collect();
    Ok(components.join("/"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_fixtures;
    use crate::tile_provider::parse_index_bin;
    use std::collections::HashMap;
    use std::io::Read;
    use tar::Archive;

    /// Helper to construct a base tile [`GraphId`].
    fn tile(level: u8, tile_id: u64) -> GraphId {
        GraphId::try_from_components(level, tile_id, 0).expect("valid tile ID in test")
    }

    /// An in-memory byte source for driving the writer without any I/O.
    struct MemorySource(HashMap<GraphId, Vec<u8>>);

    /// The error of a [`MemorySource`] when it does not contain a tile.
    #[derive(Debug, Error, PartialEq, Eq)]
    #[error("the tile is not in memory")]
    struct NotInMemory;

    impl MemorySource {
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
            Self(tiles)
        }
    }

    impl TileBytesSource for MemorySource {
        type Error = NotInMemory;

        fn with_tile_bytes<F, T>(&self, graph_id: GraphId, process: F) -> Result<T, Self::Error>
        where
            F: FnOnce(&[u8]) -> T,
        {
            self.0
                .get(&graph_id.tile_base_id())
                .map(|tile_bytes| process(tile_bytes))
                .ok_or(NotInMemory)
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

    #[test]
    fn test_tar_entry_path() {
        // Levels 0 and 1 pad the tile index to 6 digits (two components);
        // level 2 pads to 9 digits (three components).
        assert_eq!(tar_entry_path(tile(0, 3015)).unwrap(), "0/003/015.gph");
        assert_eq!(tar_entry_path(tile(0, 49)).unwrap(), "0/000/049.gph");
        assert_eq!(tar_entry_path(tile(1, 47_701)).unwrap(), "1/047/701.gph");
        assert_eq!(tar_entry_path(tile(1, 0)).unwrap(), "1/000/000.gph");
        assert_eq!(
            tar_entry_path(tile(2, 762_485)).unwrap(),
            "2/000/762/485.gph"
        );
        assert_eq!(tar_entry_path(tile(2, 2)).unwrap(), "2/000/000/002.gph");
        assert_eq!(
            tar_entry_path(tile(2, 1_036_799)).unwrap(),
            "2/001/036/799.gph"
        );
    }

    #[test]
    fn test_layout_offsets() {
        let layout = ExtractLayout::from_manifest(&scrambled_manifest())
            .expect("the manifest is well-formed");

        // 5 tiles × 16 bytes = 80 bytes of index, padded to one block;
        // with the index header, the first tile header lands at 1024.
        //
        // All offsets were computed by hand from the layout rules:
        // each tile is a 512-byte header plus its payload padded to 512.
        let expected = [
            // (graph_id, payload offset, size), in canonical (level, tile index) order
            (tile(0, 3015), 1536, 512),   // exactly one block; no padding
            (tile(1, 47_700), 2560, 511), // padded to one block
            (tile(1, 47_701), 3584, 513), // padded to two blocks
            (tile(2, 762_484), 5120, 1024), // exactly two blocks; no padding
            (tile(2, 762_485), 6656, 100), // padded to one block
        ];

        assert_eq!(layout.index_entries().len(), expected.len());
        for (entry, (graph_id, offset, size)) in layout.index_entries().iter().zip(expected) {
            assert_eq!(entry.graph_id().unwrap(), graph_id);
            assert_eq!(entry.offset(), offset);
            assert_eq!(entry.size(), size);
        }

        // Last tile payload ends at 6656 + 512 (padded), plus the 1024-byte end-of-archive marker.
        assert_eq!(layout.total_len(), 7168 + 1024);
        assert!(layout.total_len().is_multiple_of(512));
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
    fn test_write_rejects_size_mismatch() {
        let manifest = [(tile(0, 3015), 100)];
        // The source produces 99 bytes where the manifest promises 100.
        let source = MemorySource::from_manifest(&[(tile(0, 3015), 99)]);

        let result = write_extract_from_source(&manifest, &source, Vec::new());
        assert!(matches!(
            result,
            Err(ExtractWriteError::SizeMismatch {
                expected: 100,
                actual: 99,
                ..
            })
        ));
    }

    #[test]
    fn test_write_rejects_missing_tiles() {
        let manifest = [(tile(0, 3015), 100)];
        let source = MemorySource(HashMap::new());

        let result = write_extract_from_source(&manifest, &source, Vec::new());
        assert!(matches!(
            result,
            Err(ExtractWriteError::Source {
                graph_id,
                source: NotInMemory
            }) if graph_id == tile(0, 3015)
        ));
    }

    #[test]
    fn test_archive_invariants() {
        let manifest = scrambled_manifest();
        let source = MemorySource::from_manifest(&manifest);

        let mut archive_bytes = Vec::new();
        let written = write_extract_from_source(&manifest, &source, &mut archive_bytes)
            .expect("the manifest and source are well-formed");

        assert_eq!(written, archive_bytes.len() as u64);
        assert!(archive_bytes.len().is_multiple_of(512));

        // The archive must list index.bin first,
        // then the tiles in canonical (level, tile index) order under spec-compliant paths.
        let mut archive = Archive::new(archive_bytes.as_slice());
        let entry_paths: Vec<String> = archive
            .entries()
            .expect("the archive is readable")
            .map(|entry| {
                entry
                    .expect("every entry is readable")
                    .path()
                    .expect("every entry path is valid")
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
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

        // The index payload starts right after the index header
        // and describes every tile payload in the archive.
        let mut archive = Archive::new(archive_bytes.as_slice());
        let mut index_bytes = Vec::new();
        archive
            .entries()
            .expect("the archive is readable")
            .next()
            .expect("the archive has entries")
            .expect("the index entry is readable")
            .read_to_end(&mut index_bytes)
            .expect("the index payload is readable");

        let index_entries = parse_index_bin(&index_bytes).expect("the index parses");
        assert_eq!(index_entries.len(), manifest.len());

        for index_entry in index_entries {
            let offset = index_entry.offset();
            assert!(offset > 0);
            assert!(offset.is_multiple_of(512));

            // The payload at the indexed offset is byte-identical to the source tile.
            let graph_id = index_entry.graph_id().expect("the entry ID is valid");
            let start = usize::try_from(offset).expect("the offset fits in memory");
            let payload = &archive_bytes[start..start + index_entry.size() as usize];
            source
                .with_tile_bytes(graph_id, |tile_bytes| assert_eq!(payload, tile_bytes))
                .expect("the tile is in the source");
        }
    }

    #[test]
    fn test_determinism() {
        let manifest = scrambled_manifest();
        let source = MemorySource::from_manifest(&manifest);

        let mut first = Vec::new();
        write_extract_from_source(&manifest, &source, &mut first).expect("first write succeeds");

        let mut second = Vec::new();
        // A reordered manifest must not change the output either:
        // the writer sorts its own copy.
        let mut reversed = manifest.clone();
        reversed.reverse();
        write_extract_from_source(&reversed, &source, &mut second).expect("second write succeeds");

        assert_eq!(first, second);
    }

    // Tragically, memory maps are not supported by Miri!
    #[cfg(not(miri))]
    #[test]
    fn test_andorra_round_trip() {
        let fixture_path = test_fixtures::andorra_tiles_tar();
        let source_provider = TarballTileProvider::new_readonly(fixture_path)
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
        assert!(source_provider.tile_size(excluded).is_some());

        // A tile which is not in the fixture at all.
        let not_in_fixture = tile(2, 0);
        assert!(matches!(
            write_extract(&source_provider, &[tile(0, 3015), not_in_fixture], Vec::new()),
            Err(ExtractWriteError::MissingTile(graph_id)) if graph_id == not_in_fixture
        ));

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
            let base_id = graph_id.tile_base_id();
            extract_provider
                .with_tile_bytes(base_id, |extract_bytes| {
                    source_provider
                        .with_tile_bytes(base_id, |source_bytes| {
                            assert_eq!(extract_bytes, source_bytes);
                        })
                        .expect("the tile is in the source");
                })
                .expect("the tile is in the extract");
        }

        // Tiles outside the subset did not leak into the extract.
        assert!(extract_provider.tile_size(excluded).is_none());
    }
}
