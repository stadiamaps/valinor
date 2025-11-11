use super::GraphTileProviderError;
use crate::GraphId;
use crate::graph_tile::{MmapTilePointer, TileOffset};
use memmap2::{MmapOptions, MmapRaw};
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::sync::Arc;
use tar::Archive;
use zerocopy::{FromBytes, LE, U32, U64};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes, Unaligned};

/// A tile provider backed by a memory-mapped tarball archive.
///
/// # Tarball requirements/assumptions
///
/// Valhalla is capable of reading almost any tarball containing graph tiles.
/// At the moment, our aspirations are not so lofty,
/// so we *require* an `index.bin` file.
/// See the documentation for [`TileIndexBinEntry`] for details on the format.
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
pub struct TarballTileProvider<const MUT: bool> {
    /// The file backing the mmap.
    ///
    /// This is unused, but we need to keep it in scope since the memmap only has a reference to it,
    /// not ownership!
    _file: File,
    /// The actual memory map.
    mmap: Arc<MmapRaw>,
    /// An index of offsets and sizes which enables quick tile extraction from the memory map.
    tile_index: HashMap<GraphId, TileOffset>,
}

impl<const MUT: bool> TarballTileProvider<MUT> {
    fn init<P: AsRef<Path>>(path: P) -> Result<Self, GraphTileProviderError> {
        let mut archive = Archive::new(File::open(&path)?);
        let mut entries = archive.entries()?;

        let Some(entry) = entries.next() else {
            return Err(GraphTileProviderError::InvalidTarball(
                "No entries in the archive".to_string(),
            ));
        };

        let mut entry = entry?;
        if entry.path()?.to_string_lossy() != "index.bin" {
            return Err(GraphTileProviderError::InvalidTarball(
                "Expected index.bin at the start of the archive".to_string(),
            ));
        }

        // Read the index file
        let mut index_bytes = Vec::with_capacity(entry.header().size()? as usize);
        entry.read_to_end(&mut index_bytes)?;

        let index_entries = parse_index_bin(&index_bytes)?;

        // Index the index
        let mut tile_index: HashMap<GraphId, TileOffset> =
            HashMap::with_capacity(index_entries.len());
        for entry in index_entries {
            let graph_id = entry.graph_id()?;
            let offset = entry.offset.get();
            if offset == 0 || !offset.is_multiple_of(512) {
                return Err(GraphTileProviderError::InvalidTarball(format!(
                    "Expected all index offsets to lie on a 512-byte boundary, but the index entry for {} has offset {}",
                    graph_id.to_string(),
                    offset,
                )));
            }

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

        Ok(Self {
            _file: file,
            mmap,
            tile_index,
        })
    }

    /// Creates a new tarball tile provider from an existing extract.
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
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self, GraphTileProviderError> {
        Self::init(path)
    }
}

// This can't currently implement the existing trait because it operates on unowned data.
impl<const MUT: bool> TarballTileProvider<MUT> {
    pub async fn get_tile_containing(
        &self,
        graph_id: GraphId,
    ) -> Result<MmapTilePointer, GraphTileProviderError> {
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

impl TarballTileProvider<false> {
    /// Creates a new tarball tile provider from an existing extract.
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
        Self::new(path)
    }
}

impl TarballTileProvider<true> {
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
        Self::new(path)
    }

    /// Flushes outstanding memory map modifications to disk.
    ///
    /// See [`MmapRaw::flush`] for more details.
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
#[derive(FromBytes, IntoBytes, Immutable, Unaligned, PartialEq)]
#[repr(C)]
pub struct TileIndexBinEntry {
    /// Byte offset from the beginning of the tar
    offset: U64<LE>,
    /// Just the level and tile index, hence fitting in 32 bits
    tile_id: U32<LE>,
    /// The size of the tile in bytes.
    size: U32<LE>,
}

impl TileIndexBinEntry {
    fn graph_id(&self) -> Result<GraphId, GraphTileProviderError> {
        // SAFETY: We know that the bit field cannot contain a value
        // larger than the max allowed value (it's limited to 46 bits).
        // Therefore, this is guaranteed to be a valid Graph ID bit pattern.
        let graph_id = unsafe { GraphId::from_id_unchecked(self.tile_id.into()) };

        if graph_id.index() == 0 {
            Ok(graph_id)
        } else {
            Err(GraphTileProviderError::InvalidTarball(format!(
                "Invalid GraphID {}; expected the index bits to be zero.",
                self.tile_id.get()
            )))
        }
    }
}

/// Parses an `index.bin` file to enable random access.
///
/// See [`TileIndexBinEntry`] for a description of the tile format.
pub fn parse_index_bin(index_bytes: &[u8]) -> Result<&[TileIndexBinEntry], GraphTileProviderError> {
    const INDEX_ENTRY_SIZE: usize = size_of::<TileIndexBinEntry>();

    if index_bytes.is_empty() || !index_bytes.len().is_multiple_of(INDEX_ENTRY_SIZE) {
        return Err(GraphTileProviderError::InvalidTarball(format!(
            "Malformed index.bin: expected length to be non-zero and a multiple of {INDEX_ENTRY_SIZE}; was {}",
            index_bytes.len()
        )));
    }

    // Decode the index as a sequence of TileIndexEntry
    let num_tiles = index_bytes.len() / INDEX_ENTRY_SIZE;

    let (index_entries, tail) =
        <[TileIndexBinEntry]>::ref_from_prefix_with_elems(&index_bytes, num_tiles).map_err(
            |e| GraphTileProviderError::InvalidTarball(format!("Malformed index.bin: {e:?}")),
        )?;

    assert!(
        tail.is_empty(),
        "Expected no remaining bytes after parsing the index. This is a programming error in Valinor, not your code. Please report an issue."
    );

    Ok(index_entries)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::graph_tile::{GraphTile, GraphTileView};
    use crate::tile_provider::{DirectoryGraphTileProvider, GraphTileProvider};
    use std::num::NonZeroUsize;
    use std::path::PathBuf;

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
        assert!(
            matches!(
                parse_index_bin(&[]),
                Err(GraphTileProviderError::InvalidTarball(_))
            ),
            "Empty indexes are invalid"
        );
        assert!(
            matches!(
                parse_index_bin(&[0x00, 0x5a]),
                Err(GraphTileProviderError::InvalidTarball(_)),
            ),
            "Index must contain at least one full entry"
        );
        assert!(
            matches!(
                parse_index_bin(&[
                    // Contains one extra byte
                    0x00, 0x5a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x4f, 0x00, 0x00, 0x9c,
                    0x08, 0x12, 0x00, 0x00
                ]),
                Err(GraphTileProviderError::InvalidTarball(_)),
            ),
            "Index must be completely parseable with no bytes leftover"
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

    #[cfg(not(miri))]
    #[tokio::test]
    async fn test_get_tile() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles.tar");
        let provider: TarballTileProvider<false> =
            TarballTileProvider::new(path).expect("Unable to init tile provider");
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let tile_pointer = provider
            .get_tile_containing(graph_id)
            .await
            .expect("Unable to get tile");
        let tile_bytes = unsafe { tile_pointer.as_tile_bytes() };
        let tile = GraphTileView::try_from(tile_bytes).expect("Unable to deserialize tile");

        // Minimally test that we got the correct tile
        assert_eq!(tile.header().graph_id(), graph_id);
        assert_eq!(tile.header().graph_id().value(), graph_id.value());
    }

    // #[cfg(not(miri))]
    // #[test]
    // fn test_get_opp_edge() {
    //     let mut rng = rng();
    //
    //     let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    //         .join("fixtures")
    //         .join("andorra-tiles.tar");
    //     let provider = TarballTileProvider::new(path).expect("Unable to init tile provider");
    //     let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
    //     let tile_pointer = futures::executor::block_on(provider.get_tile_containing(graph_id))
    //         .expect("Unable to get tile");
    //     let tile_bytes = unsafe { tile_pointer.as_tile_bytes() };
    //     let tile = GraphTileView::try_from(tile_bytes).expect("Unable to deserialize tile");
    //
    //     // Cross-check the default implementation of the opposing edge ID function.
    //     // We only check a subset because it takes too long otherwise.
    //     // See the performance note on get_opposing_edge.
    //     let range = Uniform::try_from(0..u64::from(tile.header().directed_edge_count())).unwrap();
    //     for index in range.sample_iter(&mut rng).take(100) {
    //         let edge_id = graph_id.with_index(index).expect("Invalid graph ID.");
    //         let opp_edge_index = tile
    //             .get_opp_edge_index(edge_id)
    //             .expect("Unable to get opp edge index.");
    //         let (opp_edge_id, _) = futures::executor::block_on(provider.get_opposing_edge(edge_id))
    //             .expect("Unable to get opposing edge.");
    //         assert_eq!(u64::from(opp_edge_index), opp_edge_id.index());
    //     }
    // }

    #[cfg(not(miri))]
    #[tokio::test]
    async fn test_tiles_are_identical_to_directory() {
        // This test uses the directory tile provider as an oracle
        // to make sure the tarball reader is working as expected.
        // Probably goes without saying, but the tarball was created using
        // valhalla_build_extract from the andorra-tiles directory.

        let tile_ids = &[
            GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID"),
            GraphId::try_from_components(1, 47701, 0).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 762485, 0).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 762486, 0).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 763925, 0).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 763926, 0).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 763927, 0).expect("Unable to create graph ID"),
        ];

        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let directory_provider =
            DirectoryGraphTileProvider::new(base, NonZeroUsize::new(1).unwrap());

        let tarball_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles.tar");
        let tarball_provider =
            TarballTileProvider::new_readonly(tarball_path).expect("Unable to init tile provider");

        for graph_id in tile_ids {
            let directory_tile = directory_provider
                .get_tile_containing(*graph_id)
                .await
                .expect("Unable to get tile");
            let tarball_tile_pointer = tarball_provider
                .get_tile_containing(*graph_id)
                .await
                .expect("Unable to get tile");
            let tarball_tile_bytes = unsafe { tarball_tile_pointer.as_tile_bytes() };

            assert_eq!(directory_tile.borrow_owner(), tarball_tile_bytes);
        }
    }
}
