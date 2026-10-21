//! A streaming tar writer for tile extracts.
//!
//! The writer computes every offset from the tile sizes before it writes,
//! so it writes the archive in one pass. The archive contains:
//!
//! 1. `index.bin`, which Valhalla requires as the first entry of a remote tarball.
//! 2. The tiles at the paths of [`GraphId::relative_path`],
//!    in ascending (level, tile index) order.
//!    This is not the `Ord` order of [`GraphId`].
//! 3. The two-block end-of-archive marker.

use crate::GraphId;
use crate::graph_id::InvalidGraphIdError;
use crate::tile_provider::{
    GraphTileProviderError, INDEX_BIN_ENTRY_NAME, INDEX_ENTRY_SIZE, InvalidIndexBinError,
    TAR_BLOCK_SIZE, TILE_FILE_EXTENSION, TileBytesSource, TileIndexBinEntry, serialize_index_bin,
};
use std::io::Write;
use tar::{EntryType, Header};
use thiserror::Error;

/// Zeros for the payload padding and the end-of-archive marker.
#[expect(clippy::cast_possible_truncation, reason = "512 fits in every usize")]
const ZERO_BLOCK: [u8; TAR_BLOCK_SIZE as usize] = [0; TAR_BLOCK_SIZE as usize];

/// The length of the end-of-archive marker: two zero blocks.
const END_OF_ARCHIVE_LEN: u64 = 2 * TAR_BLOCK_SIZE;

/// An error in the set of tiles of an extract.
///
/// The writer finds these errors before it writes any bytes.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum ExtractLayoutError {
    /// The tile list is empty.
    #[error("the extract contains no tiles")]
    EmptyManifest,
    /// The tile list contains a tile more than once.
    ///
    /// Graph IDs that differ only in the feature index are the same tile.
    #[error("the extract contains tile {0} more than once")]
    DuplicateTile(GraphId),
    /// The source gives a tile a size of zero.
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
    /// The source produced a tile whose length differs from the size that it reported,
    /// for example because a tile file changed during the write.
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

/// Writes an extract with the tiles of `tile_ids` from `source` into `dest`,
/// and returns the number of bytes written.
///
/// The writer copies each tile verbatim, and it does not seek or buffer the archive.
/// The order of `tile_ids` and their feature indexes do not change the output,
/// so the same set of tiles always gives the same bytes.
///
/// # Errors
///
/// Returns an error before any write if `tile_ids` is empty,
/// names a tile more than once, or names a tile that is not in `source`.
/// Returns an error during the write if `source` fails,
/// if the length of a tile differs from its reported size, or if `dest` fails.
/// After an error during the write, `dest` contains a partial archive.
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

/// The payload offset of each tile and the total length of an extract.
#[derive(Debug)]
struct ExtractLayout {
    /// One index entry for each tile, in archive order.
    entries: Vec<TileIndexBinEntry>,
    /// The total length of the archive in bytes, including the end-of-archive marker.
    total_len: u64,
}

impl ExtractLayout {
    /// Computes the layout for `(GraphId, size)` pairs in any order.
    ///
    /// # Errors
    ///
    /// Returns an error if `manifest` is empty, contains a tile more than once,
    /// contains a tile with a size of zero, or contains an ID that is not a base tile ID.
    fn from_manifest(manifest: &[(GraphId, u32)]) -> Result<Self, ExtractLayoutError> {
        if manifest.is_empty() {
            return Err(ExtractLayoutError::EmptyManifest);
        }

        let mut sorted = manifest.to_vec();
        sorted.sort_unstable_by_key(|(graph_id, _)| (graph_id.level(), graph_id.tile_id()));

        let index_len = (INDEX_ENTRY_SIZE * sorted.len()) as u64;
        let mut next_entry_offset = entry_len(index_len);

        let mut entries = Vec::with_capacity(sorted.len());
        for (i, &(graph_id, size)) in sorted.iter().enumerate() {
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

    /// The index entries, in archive order.
    #[inline]
    fn index_entries(&self) -> &[TileIndexBinEntry] {
        &self.entries
    }

    /// The total length of the archive in bytes.
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
        // The layout holds only valid base tile IDs, so this does not fail.
        let graph_id = entry.graph_id().map_err(ExtractLayoutError::from)?;
        let path = graph_id.relative_path(TILE_FILE_EXTENSION)?;
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

/// Writes a tar entry for `payload` at `path`, and returns the offset of the payload.
fn write_entry<W: Write>(
    dest: &mut CountingWriter<W>,
    path: &str,
    payload: &[u8],
) -> std::io::Result<u64> {
    // Keep all metadata fixed, so that the same tiles always give the same bytes.
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

/// A writer that counts the bytes written through it.
struct CountingWriter<W> {
    inner: W,
    /// The offset of the next byte in the archive.
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

    fn tile(level: u8, tile_id: u64) -> GraphId {
        GraphId::try_from_components(level, tile_id, 0).expect("valid tile ID in test")
    }

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
        fn from_manifest(manifest: &[(GraphId, u32)]) -> Self {
            let tiles = manifest
                .iter()
                .map(|(graph_id, size)| {
                    // A nonzero fill for each tile, so that tiles and padding differ.
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

    /// Tiles out of archive order, with sizes at, above, and below a block boundary.
    fn scrambled_manifest() -> Vec<(GraphId, u32)> {
        vec![
            (tile(2, 762_485), 100),
            (tile(0, 3015), 512),
            (tile(2, 762_484), 1024),
            (tile(1, 47_701), 513),
            (tile(1, 47_700), 511),
        ]
    }

    /// Returns the path and payload offset of each entry, as the `tar` crate reads them.
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

        // The index entry (a header and 5 × 16 bytes) fills blocks 0 and 1.
        // Each payload starts one block after its header.
        let expected = [
            // (graph_id, payload offset, size)
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

        let index_bytes = read_index_bytes(&archive_bytes);
        let index_entries = parse_index_bin(&index_bytes).expect("the index parses");
        assert_eq!(index_entries.len(), manifest.len());

        for (index_entry, (_, payload_offset)) in index_entries.iter().zip(&entries[1..]) {
            assert_eq!(index_entry.offset(), *payload_offset);

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

        let mut reversed = tile_ids;
        reversed.reverse();
        let mut second = Vec::new();
        write_extract(&source, &reversed, &mut second).expect("second write succeeds");

        assert_eq!(first, second);
    }

    proptest! {
        #[test]
        fn test_archive_matches_independent_reader(
            // Unique tiles on levels 0 to 2, with sizes of one to just over four blocks.
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

            let entries = read_entries(&archive_bytes);
            prop_assert_eq!(entries.len(), manifest.len() + 1);
            for (index_entry, (path, payload_offset)) in layout.index_entries().iter().zip(&entries[1..]) {
                let graph_id = index_entry.graph_id().expect("the entry ID is valid");
                prop_assert_eq!(index_entry.offset(), *payload_offset);
                prop_assert_eq!(path, &graph_id.relative_path(TILE_FILE_EXTENSION).expect("valid tile"));
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

        // Out of archive order, and with one nonzero feature index.
        let tile_ids = [
            tile(2, 763_926),
            tile(0, 3015),
            GraphId::try_from_components(1, 47_701, 42).expect("valid graph ID in test"),
            tile(2, 762_485),
        ];
        let excluded = tile(2, 763_925);
        assert!(source_provider.tile_size(excluded).unwrap().is_some());

        let mut archive_bytes = Vec::new();
        let written = write_extract(&source_provider, &tile_ids, &mut archive_bytes)
            .expect("the extract writes cleanly");
        assert_eq!(written, archive_bytes.len() as u64);

        let mut second = Vec::new();
        write_extract(&source_provider, &tile_ids, &mut second).expect("second write succeeds");
        assert_eq!(archive_bytes, second);

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

        assert!(extract_provider.tile_size(excluded).unwrap().is_none());
    }

    // Tragically, memory maps are not supported by Miri!
    #[cfg(not(miri))]
    #[test]
    fn test_directory_and_tarball_sources_write_the_same_extract() {
        // The two fixtures contain the same tiles.
        let tarball = TarballTileProvider::new_readonly(test_fixtures::andorra_tiles_tar())
            .expect("Unable to init the tarball tile provider");
        let directory = DirectoryGraphTileProvider::new(
            test_fixtures::andorra_tiles_dir(),
            NonZeroUsize::new(1).unwrap(),
        );

        let tile_ids: Vec<GraphId> = tarball.tile_ids().copied().collect();
        assert!(tile_ids.len() > 1);

        let mut from_tarball = Vec::new();
        write_extract(&tarball, &tile_ids, &mut from_tarball)
            .expect("the extract writes cleanly from the tarball");
        let mut from_directory = Vec::new();
        write_extract(&directory, &tile_ids, &mut from_directory)
            .expect("the extract writes cleanly from the directory");
        assert_eq!(from_tarball, from_directory);

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
