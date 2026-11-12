//! Writes tile extracts with `index.bin` followed by tiles in ascending (level, tile ID) order.

use crate::GraphId;
use crate::graph_id::InvalidGraphIdError;
use crate::graph_tile::handles::GraphTileHandle;
use crate::tile_provider::{
    GraphTileProvider, GraphTileProviderError, INDEX_BIN_FILE_NAME, INDEX_ENTRY_SIZE,
    InvalidIndexBinError, TAR_BLOCK_SIZE, TILE_FILE_EXTENSION, TileIndexBinEntry,
    serialize_index_bin,
};
use std::io::Write;
use std::path::Path;
use tar::{EntryType, Header};
use thiserror::Error;

#[expect(clippy::cast_possible_truncation, reason = "512 fits in every usize")]
const ZERO_BLOCK: [u8; TAR_BLOCK_SIZE as usize] = [0; TAR_BLOCK_SIZE as usize];

const END_OF_ARCHIVE_MARKER_LEN: u64 = 2 * TAR_BLOCK_SIZE;

/// An error from a tile extract operation.
#[derive(Debug, Error)]
pub enum ExtractError {
    /// The tile list is empty.
    #[error("the extract contains no tiles")]
    NoTiles,
    /// The provider does not have a requested tile.
    #[error("the provider does not have tile {0}")]
    MissingTile(GraphId),
    /// A requested graph ID has no tar entry path.
    #[error("invalid graph ID: {0}")]
    InvalidGraphId(#[from] InvalidGraphIdError),
    /// A tile has no valid `index.bin` entry.
    #[error("invalid index.bin: {0}")]
    InvalidIndexBin(#[from] InvalidIndexBinError),
    /// The tile length differs from the size that the provider reported.
    #[error(
        "the provider gave {actual} bytes for tile {graph_id}, but it reported a size of {expected} bytes"
    )]
    SizeMismatch {
        /// The base graph ID of the tile.
        graph_id: GraphId,
        /// The size that the provider reported before the write.
        expected: u32,
        /// The length of the tile bytes from the provider.
        actual: usize,
    },
    /// The provider failed to give the size of a tile, or to read or decode a tile.
    #[error("the provider failed to give tile {graph_id}: {source}")]
    Provider {
        /// The base graph ID of the tile.
        graph_id: GraphId,
        /// The error from the provider.
        source: GraphTileProviderError,
    },
    /// A destination write or flush failed.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

impl ExtractError {
    fn from_provider(graph_id: GraphId, source: GraphTileProviderError) -> Self {
        match source {
            GraphTileProviderError::TileDoesNotExist => Self::MissingTile(graph_id),
            source => Self::Provider { graph_id, source },
        }
    }
}

/// Writes the tiles that contain `tile_ids` from `provider` to `dest` as an extract tarball.
/// Returns the number of bytes written.
///
/// The archive has `index.bin` first, then the tiles in ascending (level, tile ID) order,
/// with `/` path separators.
/// The function ignores duplicate tile IDs and feature indexes.
/// The output is deterministic: the same tiles always give the same bytes.
///
/// # Performance
///
/// This function does not buffer writes to `dest`.
/// Wrap an unbuffered destination in a [`BufWriter`](std::io::BufWriter).
///
/// # Errors
///
/// Returns an error if `tile_ids` is empty, if the provider cannot give a valid tile,
/// or if a write to `dest` fails.
///
/// An empty `tile_ids` or a failure to get a tile size leaves `dest` unchanged.
/// Other errors can leave a partial archive in `dest`.
pub fn write_extract<P, I, W>(provider: &P, tile_ids: I, mut dest: W) -> Result<u64, ExtractError>
where
    P: GraphTileProvider,
    I: IntoIterator<Item = GraphId>,
    W: Write,
{
    let mut tiles: Vec<GraphId> = tile_ids
        .into_iter()
        .map(|graph_id| graph_id.tile_base_id())
        .collect();
    // Possibility for the future: hilbert ordering or something to try optimizing for spatial clustering???
    tiles.sort_unstable_by_key(|graph_id| (graph_id.level(), graph_id.tile_id()));
    tiles.dedup();
    if tiles.is_empty() {
        return Err(ExtractError::NoTiles);
    }

    let manifest = tiles
        .into_iter()
        .map(|graph_id| {
            provider
                .tile_size(graph_id)
                .map(|size| (graph_id, size))
                .map_err(|source| ExtractError::from_provider(graph_id, source))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let layout = ExtractLayout::from_manifest(&manifest)?;

    let index_bytes = serialize_index_bin(&layout.entries)?;
    write_entry(&mut dest, INDEX_BIN_FILE_NAME, index_bytes)?;

    for &(graph_id, expected) in &manifest {
        let path = graph_id.file_path(TILE_FILE_EXTENSION)?;
        let tile = provider
            .get_handle_for_tile_containing(graph_id)
            .map_err(|source| ExtractError::from_provider(graph_id, source))?;

        let tile_bytes = tile.tile_bytes();
        if tile_bytes.len() != expected as usize {
            return Err(ExtractError::SizeMismatch {
                graph_id,
                expected,
                actual: tile_bytes.len(),
            });
        }
        write_entry(&mut dest, &path, tile_bytes)?;
    }

    // Write the end-of-archive marker and flush
    dest.write_all(&ZERO_BLOCK)?;
    dest.write_all(&ZERO_BLOCK)?;
    dest.flush()?;

    Ok(layout.total_len)
}

#[derive(Debug)]
struct ExtractLayout {
    /// The `index.bin` entry of each tile, in archive order.
    entries: Vec<TileIndexBinEntry>,
    /// The length of the archive in bytes, with the end-of-archive marker.
    total_len: u64,
}

impl ExtractLayout {
    /// Computes the layout from `manifest` pairs of (base tile ID, size in bytes), in archive order.
    fn from_manifest(manifest: &[(GraphId, u32)]) -> Result<Self, InvalidIndexBinError> {
        let index_len = (INDEX_ENTRY_SIZE * manifest.len()) as u64;
        let mut next_entry_offset = entry_len(index_len);

        let mut entries = Vec::with_capacity(manifest.len());
        for &(graph_id, size) in manifest {
            let payload_offset = next_entry_offset + TAR_BLOCK_SIZE;
            entries.push(TileIndexBinEntry::new(graph_id, payload_offset, size)?);
            next_entry_offset += entry_len(u64::from(size));
        }

        Ok(Self {
            entries,
            total_len: next_entry_offset + END_OF_ARCHIVE_MARKER_LEN,
        })
    }
}

/// The length of a tar entry with a payload of `payload_len` bytes:
/// a header block, then the payload padded to a whole number of blocks.
const fn entry_len(payload_len: u64) -> u64 {
    TAR_BLOCK_SIZE + payload_len.next_multiple_of(TAR_BLOCK_SIZE)
}

fn write_entry<W: Write>(
    dest: &mut W,
    path: impl AsRef<Path>,
    payload: &[u8],
) -> std::io::Result<()> {
    // Fixed metadata (no time, owner, or source file mode) gives the same bytes for the same tiles.
    // Readers find tiles through index.bin and do not extract the archive, so nothing reads it.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph_tile::GraphTileView;
    use crate::graph_tile::handles::OwnedGraphTileHandle;
    use crate::test_fixtures;
    use crate::tile_provider::{DirectoryGraphTileProvider, parse_index_bin};
    use geo::{CoordFloat, Point};
    use num_traits::FromPrimitive;
    use std::collections::{HashMap, HashSet};
    use std::io::Read;
    use std::num::NonZeroUsize;
    use std::path::Path;
    use std::sync::Arc;
    use tar::Archive;

    fn tile((level, tile_id): (u8, u64)) -> GraphId {
        GraphId::try_from_components(level, tile_id, 0).expect("valid tile ID in test")
    }

    fn directory_provider(base: &Path) -> DirectoryGraphTileProvider {
        DirectoryGraphTileProvider::new(base.to_path_buf(), NonZeroUsize::MIN)
    }

    /// The Andorra tile directory, with sizes and read errors that a test can change.
    struct TestProvider {
        inner: DirectoryGraphTileProvider,
        reported_sizes: HashMap<GraphId, u32>,
        size_failures: HashSet<GraphId>,
        read_failures: HashSet<GraphId>,
    }

    impl TestProvider {
        fn new() -> Self {
            Self {
                inner: directory_provider(&test_fixtures::andorra_tiles_dir()),
                reported_sizes: HashMap::new(),
                size_failures: HashSet::new(),
                read_failures: HashSet::new(),
            }
        }
    }

    impl GraphTileProvider for TestProvider {
        type TileHandle = Arc<OwnedGraphTileHandle>;

        fn with_tile_containing<F, T>(
            &self,
            graph_id: GraphId,
            process: F,
        ) -> Result<T, GraphTileProviderError>
        where
            F: FnOnce(&GraphTileView) -> T,
        {
            self.inner.with_tile_containing(graph_id, process)
        }

        fn get_handle_for_tile_containing(
            &self,
            graph_id: GraphId,
        ) -> Result<Self::TileHandle, GraphTileProviderError> {
            if self.read_failures.contains(&graph_id.tile_base_id()) {
                return Err(GraphTileProviderError::TileFetchError(String::new()));
            }
            self.inner.get_handle_for_tile_containing(graph_id)
        }

        fn tile_size(&self, graph_id: GraphId) -> Result<u32, GraphTileProviderError> {
            let base_graph_id = graph_id.tile_base_id();
            if self.size_failures.contains(&base_graph_id) {
                return Err(GraphTileProviderError::TileFetchError(String::new()));
            }
            if let Some(size) = self.reported_sizes.get(&base_graph_id) {
                return Ok(*size);
            }
            self.inner.tile_size(graph_id)
        }

        fn tiles_within_radius<N: CoordFloat + FromPrimitive>(
            &self,
            center: Point<N>,
            radius: N,
        ) -> Vec<GraphId> {
            self.inner.tiles_within_radius(center, radius)
        }
    }

    fn read_entries(archive_bytes: &[u8]) -> Vec<(String, u64)> {
        Archive::new(archive_bytes)
            .entries()
            .expect("the archive is readable")
            .map(|entry| {
                let entry = entry.expect("every entry is readable");
                let path = String::from_utf8_lossy(&entry.path_bytes()).into_owned();
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

    fn copy_small_tile() -> (tempfile::TempDir, std::path::PathBuf) {
        let base = tempfile::tempdir().expect("Unable to create a temporary directory");
        let relative_path = test_fixtures::smallest_andorra_tile()
            .file_path(TILE_FILE_EXTENSION)
            .expect("valid tile");
        let tile_path = base.path().join(&relative_path);
        std::fs::create_dir_all(tile_path.parent().expect("the tile path has a parent"))
            .expect("Unable to create the tile directory");
        // Miri does not support the `copy_file_range` call that `fs::copy` uses on Linux.
        let bytes = std::fs::read(test_fixtures::andorra_tiles_dir().join(&relative_path))
            .expect("Unable to read the tile");
        std::fs::write(&tile_path, bytes).expect("Unable to write the tile");
        (base, tile_path)
    }

    /// Checks an archive with the `tar` crate as an oracle,
    /// then checks that each index entry gives the offset of its tile payload,
    /// and that each payload equals the tile file in `tile_dir`.
    fn check_archive(archive_bytes: &[u8], expected_tiles: &[GraphId], tile_dir: &Path) {
        assert!(
            archive_bytes.len().is_multiple_of(ZERO_BLOCK.len()),
            "The archive must be a whole number of tar blocks"
        );
        let marker_start = archive_bytes.len() - ZERO_BLOCK.len() * 2;
        assert!(
            archive_bytes[marker_start..].iter().all(|byte| *byte == 0),
            "The archive must end with two zero blocks"
        );

        let entries = read_entries(archive_bytes);
        let mut expected_paths = vec![INDEX_BIN_FILE_NAME.to_string()];
        // Tar entry names use `/` on every platform.
        expected_paths.extend(expected_tiles.iter().map(|graph_id| {
            let file_path = graph_id.file_path(TILE_FILE_EXTENSION).expect("valid tile");
            let components: Vec<&str> = file_path
                .iter()
                .map(|component| component.to_str().expect("tile paths are ASCII"))
                .collect();
            components.join("/")
        }));
        let entry_paths: Vec<&String> = entries.iter().map(|(path, _)| path).collect();
        assert_eq!(
            entry_paths,
            expected_paths.iter().collect::<Vec<_>>(),
            "The archive must contain index.bin, then the tiles in archive order"
        );

        let index_bytes = read_index_bytes(archive_bytes);
        let index_entries = parse_index_bin(&index_bytes).expect("the index parses");
        assert_eq!(
            index_entries.len(),
            expected_tiles.len(),
            "The index must have one entry for each tile"
        );
        for (index_entry, (path, payload_offset)) in index_entries.iter().zip(&entries[1..]) {
            assert_eq!(
                index_entry.offset(),
                *payload_offset,
                "The index offset of {path} must be where the tar reader finds its payload"
            );

            let start = usize::try_from(index_entry.offset()).expect("the offset fits in memory");
            let payload = &archive_bytes[start..start + index_entry.size() as usize];
            let tile_file = std::fs::read(tile_dir.join(path)).expect("the tile file is readable");
            assert!(
                payload == tile_file.as_slice(),
                "The payload of {path} must be the bytes of its tile file"
            );
        }
    }

    #[test]
    fn test_layout_offsets() {
        const B: u64 = TAR_BLOCK_SIZE;

        let manifest = [
            (tile((0, 3015)), 512),
            (tile((1, 47_700)), 511),
            (tile((1, 47_701)), 513),
            (tile((2, 762_484)), 1024),
            (tile((2, 762_485)), 100),
        ];
        let layout = ExtractLayout::from_manifest(&manifest).expect("the manifest is well-formed");

        // The index occupies blocks 0 and 1. Each tile header precedes its payload by one block.
        let expected_offsets = [3 * B, 5 * B, 7 * B, 10 * B, 13 * B];

        assert_eq!(
            layout.entries.len(),
            manifest.len(),
            "The layout must have one entry for each tile"
        );
        for ((entry, (graph_id, size)), offset) in
            layout.entries.iter().zip(manifest).zip(expected_offsets)
        {
            let expected =
                TileIndexBinEntry::new(graph_id, offset, size).expect("the entry is well-formed");
            assert_eq!(
                *entry, expected,
                "The entry of {graph_id} must keep the manifest order and size, and its payload must start one block after its header"
            );
        }

        assert_eq!(
            layout.total_len,
            16 * B,
            "The last payload ends at block 14, then the end-of-archive marker is 2 blocks"
        );
    }

    #[test]
    fn test_layout_rejects_non_base_tile_ids() {
        let with_feature_index =
            GraphId::try_from_components(1, 47_701, 7).expect("valid graph ID in test");
        assert_eq!(
            ExtractLayout::from_manifest(&[(with_feature_index, 100)]).unwrap_err(),
            InvalidIndexBinError::FeatureIndex(with_feature_index),
            "Only base tile IDs can be indexed"
        );
    }

    #[test]
    fn test_write_rejects_empty_tile_list() {
        let mut dest = Vec::new();
        assert!(
            matches!(
                write_extract(&TestProvider::new(), [], &mut dest),
                Err(ExtractError::NoTiles)
            ),
            "An extract must contain at least one tile"
        );
        assert!(
            dest.is_empty(),
            "An empty tile list is found before any write"
        );
    }

    #[test]
    fn test_write_rejects_missing_tiles() {
        let missing = tile((2, 0));
        let mut dest = Vec::new();
        assert!(
            matches!(
                write_extract(&TestProvider::new(), [test_fixtures::smallest_andorra_tile(), missing], &mut dest),
                Err(ExtractError::MissingTile(graph_id)) if graph_id == missing
            ),
            "A tile that is not in the provider must be a MissingTile error"
        );
        assert!(dest.is_empty(), "A missing tile is found before any write");
    }

    #[test]
    fn test_write_reports_size_errors_before_write() {
        let mut provider = TestProvider::new();
        provider
            .size_failures
            .insert(test_fixtures::smallest_andorra_tile());

        let mut dest = Vec::new();
        assert!(
            matches!(
                write_extract(&provider, [test_fixtures::smallest_andorra_tile()], &mut dest),
                Err(ExtractError::Provider {
                    graph_id,
                    source: GraphTileProviderError::TileFetchError(_),
                }) if graph_id == test_fixtures::smallest_andorra_tile()
            ),
            "A failure to get a tile size must be a Provider error"
        );
        assert!(
            dest.is_empty(),
            "A tile size error is found before any write"
        );
    }

    #[test]
    fn test_write_reports_read_errors() {
        let mut provider = TestProvider::new();
        provider
            .read_failures
            .insert(test_fixtures::smallest_andorra_tile());

        assert!(
            matches!(
                write_extract(&provider, [test_fixtures::smallest_andorra_tile()], Vec::new()),
                Err(ExtractError::Provider {
                    graph_id,
                    source: GraphTileProviderError::TileFetchError(_),
                }) if graph_id == test_fixtures::smallest_andorra_tile()
            ),
            "A failure to read a tile must be a Provider error"
        );
    }

    #[test]
    fn test_write_rejects_size_mismatch() {
        let mut provider = TestProvider::new();
        let real_size = provider
            .tile_size(test_fixtures::smallest_andorra_tile())
            .expect("the tile has a size");
        provider
            .reported_sizes
            .insert(test_fixtures::smallest_andorra_tile(), real_size + 1);

        assert!(
            matches!(
                write_extract(&provider, [test_fixtures::smallest_andorra_tile()], Vec::new()),
                Err(ExtractError::SizeMismatch {
                    graph_id,
                    expected,
                    actual,
                }) if graph_id == test_fixtures::smallest_andorra_tile()
                    && expected == real_size + 1
                    && actual == real_size as usize
            ),
            "Tile bytes of a different length than the reported size must be an error"
        );
    }

    #[test]
    fn test_write_rejects_tile_changed_after_cache() {
        let (base, tile_path) = copy_small_tile();
        let provider = directory_provider(base.path());
        let cached = provider
            .get_handle_for_tile_containing(test_fixtures::smallest_andorra_tile())
            .expect("Unable to get tile");
        let cached_len = cached.tile_bytes().len();

        let mut file = std::fs::OpenOptions::new()
            .append(true)
            .open(&tile_path)
            .expect("Unable to open the tile file");
        file.write_all(&[0]).expect("Unable to grow the tile file");

        assert!(
            matches!(
                write_extract(&provider, [test_fixtures::smallest_andorra_tile()], Vec::new()),
                Err(ExtractError::SizeMismatch {
                    expected,
                    actual,
                    ..
                }) if expected as usize == cached_len + 1 && actual == cached_len
            ),
            "A tile file that changed after the provider cached it must be a SizeMismatch"
        );
    }

    #[test]
    fn test_write_rejects_empty_tile_file() {
        let (base, tile_path) = copy_small_tile();
        std::fs::File::create(&tile_path).expect("Unable to empty the tile file");

        assert!(
            matches!(
                write_extract(&directory_provider(base.path()), [test_fixtures::smallest_andorra_tile()], Vec::new()),
                Err(ExtractError::Provider {
                    graph_id,
                    source: GraphTileProviderError::DecodingError(_),
                }) if graph_id == test_fixtures::smallest_andorra_tile()
            ),
            "An empty tile file must fail to decode"
        );
    }

    #[test]
    fn test_write_small_tile() {
        let provider = TestProvider::new();
        let mut archive_bytes = Vec::new();
        let written = write_extract(
            &provider,
            [test_fixtures::smallest_andorra_tile()],
            &mut archive_bytes,
        )
        .expect("the extract writes cleanly");

        assert_eq!(
            written,
            archive_bytes.len() as u64,
            "The return value must be the number of bytes written"
        );
        check_archive(
            &archive_bytes,
            &[test_fixtures::smallest_andorra_tile()],
            &test_fixtures::andorra_tiles_dir(),
        );
    }

    // Miri is too slow to decode all of the Andorra tiles, and it does not support memory maps.
    #[cfg(not(miri))]
    mod all_andorra_tiles {
        use super::*;
        use crate::tile_provider::TarballTileProvider;
        use core::fmt::Write as _;
        use proptest::collection::vec;
        use proptest::prelude::ProptestConfig;
        use proptest::sample::select;
        use proptest::{prop_assert, prop_assert_eq, proptest};
        use sha2::{Digest, Sha256};

        /// The tiles of the Andorra fixtures, in archive order.
        const ANDORRA_TILES: [(u8, u64); 7] = [
            (0, 3015),
            (1, 47_701),
            (2, 762_485),
            (2, 762_486),
            (2, 763_925),
            (2, 763_926),
            (2, 763_927),
        ];

        fn andorra_tiles() -> Vec<GraphId> {
            ANDORRA_TILES.into_iter().map(tile).collect()
        }

        #[test]
        fn test_write_all_andorra_tiles() {
            let provider = TestProvider::new();
            let mut archive_bytes = Vec::new();
            let written = write_extract(&provider, andorra_tiles(), &mut archive_bytes)
                .expect("the extract writes cleanly");

            assert_eq!(
                written,
                archive_bytes.len() as u64,
                "The return value must be the number of bytes written"
            );
            check_archive(
                &archive_bytes,
                &andorra_tiles(),
                &test_fixtures::andorra_tiles_dir(),
            );
        }

        #[test]
        fn test_order_and_duplicates_do_not_change_output() {
            let provider = TestProvider::new();
            let mut original_tile_order_bytes = Vec::new();
            write_extract(&provider, andorra_tiles(), &mut original_tile_order_bytes)
                .expect("first write succeeds");

            let scrambled = andorra_tiles().into_iter().rev().flat_map(|graph_id| {
                let with_feature_index = graph_id
                    .with_feature_index(42)
                    .expect("valid feature index");
                [graph_id, with_feature_index]
            });
            let mut scrambled_tile_order_bytes = Vec::new();
            write_extract(&provider, scrambled, &mut scrambled_tile_order_bytes)
                .expect("second write succeeds");

            assert!(
                original_tile_order_bytes == scrambled_tile_order_bytes,
                "Reordering or duplicating tile IDs should not change the output"
            );
        }

        #[test]
        fn test_andorra_round_trip() {
            let source_provider =
                TarballTileProvider::new_readonly(test_fixtures::andorra_tiles_tar())
                    .expect("Unable to init the source tile provider");

            let tile_ids = [
                tile((2, 763_926)),
                tile((0, 3015)),
                GraphId::try_from_components(1, 47_701, 42).expect("valid graph ID in test"),
                tile((2, 762_485)),
            ];
            let excluded = tile((2, 763_925));
            assert!(
                source_provider.tile_size(excluded).is_ok(),
                "The excluded tile must be in the source"
            );

            let mut archive_bytes = Vec::new();
            write_extract(&source_provider, tile_ids, &mut archive_bytes)
                .expect("the extract writes cleanly");

            let mut archive_file =
                tempfile::NamedTempFile::new().expect("a temporary file is created");
            archive_file
                .write_all(&archive_bytes)
                .expect("the extract is written to disk");
            let extract_provider = TarballTileProvider::new_readonly(archive_file.path())
                .expect("the generated extract opens cleanly");

            for graph_id in tile_ids {
                let extract_tile = extract_provider
                    .get_handle_for_tile_containing(graph_id)
                    .expect("the tile is in the extract");
                let source_tile = source_provider
                    .get_handle_for_tile_containing(graph_id)
                    .expect("the tile is in the source");
                assert!(
                    extract_tile.tile_bytes() == source_tile.tile_bytes(),
                    "Tile {graph_id} must have the same bytes in the extract and in the source"
                );
            }
            assert!(
                matches!(
                    extract_provider.tile_size(excluded),
                    Err(GraphTileProviderError::TileDoesNotExist)
                ),
                "A tile that was not requested must not be in the extract"
            );
        }

        #[test]
        fn test_all_andorra_tiles_sha256() {
            let mut archive_bytes = Vec::new();
            write_extract(&TestProvider::new(), andorra_tiles(), &mut archive_bytes)
                .expect("the extract writes cleanly");

            let digest =
                Sha256::digest(&archive_bytes)
                    .iter()
                    .fold(String::new(), |mut hex, byte| {
                        write!(hex, "{byte:02x}").expect("a write to a String does not fail");
                        hex
                    });
            insta::assert_snapshot!(digest);
        }

        #[test]
        fn test_directory_and_tarball_providers_write_the_same_extract() {
            // The two fixtures contain the same tiles.
            let tarball = TarballTileProvider::new_readonly(test_fixtures::andorra_tiles_tar())
                .expect("Unable to init the tarball tile provider");
            let directory = directory_provider(&test_fixtures::andorra_tiles_dir());

            let mut from_tarball_bytes = Vec::new();
            write_extract(&tarball, andorra_tiles(), &mut from_tarball_bytes)
                .expect("the extract writes cleanly from the tarball");
            let mut from_directory_bytes = Vec::new();
            write_extract(&directory, andorra_tiles(), &mut from_directory_bytes)
                .expect("the extract writes cleanly from the directory");
            assert!(
                from_tarball_bytes == from_directory_bytes,
                "The tarball and the directory of the same tiles must give the same extract"
            );
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(32))]

            #[test]
            fn test_archive_matches_independent_reader(
                tile_ids in vec((select(&ANDORRA_TILES[..]), 0u64..4), 1..12)
            ) {
                let tile_ids: Vec<GraphId> = tile_ids
                    .into_iter()
                    .map(|(tile_key, feature_index)| {
                        tile(tile_key)
                            .with_feature_index(feature_index)
                            .expect("valid feature index")
                    })
                    .collect();
                let mut expected_tiles: Vec<GraphId> =
                    tile_ids.iter().map(GraphId::tile_base_id).collect();
                expected_tiles.sort_unstable_by_key(|graph_id| (graph_id.level(), graph_id.tile_id()));
                expected_tiles.dedup();

                let mut archive_bytes = Vec::new();
                let written = write_extract(&TestProvider::new(), tile_ids, &mut archive_bytes)
                    .expect("the extract writes cleanly");

                prop_assert_eq!(written, archive_bytes.len() as u64);
                prop_assert!(!expected_tiles.is_empty());
                check_archive(&archive_bytes, &expected_tiles, &test_fixtures::andorra_tiles_dir());
            }
        }
    }
}
