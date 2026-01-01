use crate::GraphId;
use crate::graph_tile::{
    LookupError,
    handles::{MmapTilePointer, TileOffset},
};
use crate::tile_provider::{GraphTileProviderError, TarballTileProvider};
use crate::traffic_tile::{TRAFFIC_TILE_VERSION, TrafficSpeed, TrafficTileHeader};
use std::path::Path;

/// The traffic tarball tile provider.
///
/// This provides an interface to querying and (in some cases)
/// writing data.
///
/// # Safety
///
/// This structure is entirely safe in read-only mode when it is the only consumer of the `mmap`,
/// and can guarantee that the file/shared memory are not modified externally.
/// Otherwise, the situation gets a bit more complicated.
///
/// Whether this struct (and the backing memory map) support mutability is determined
/// by the value of the const generic parameter `MUT`.
/// When `MUT` is `false` methods enabling mutation are hidden.
///
/// Given the inherently unsafe nature of working with shared mutable memory this way
/// (a random process can modify your memory _at any time_),
/// we use exclusively volatile memory operations internally.
/// Unfortunately, Rust does not have a great way to ensure everything is as specified as we'd like,
/// and there is not clear consensus on what mix of atomics and volatile are the "correct" way
/// to do shared `mmap`'d files.
///
/// **It is the responsibility of the caller to ensure that the platform is able to perform
/// loads and stores of 64-bit values atomically.**
pub struct TrafficTileProvider<const MUT: bool> {
    tarball_tile_provider: TarballTileProvider<MUT>,
}

impl<const MUT: bool> TrafficTileProvider<MUT> {
    /// Creates a new traffic tile provider from an existing tarball extract.
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
        let tarball_tile_provider = TarballTileProvider::new(path)?;
        Ok(Self {
            tarball_tile_provider,
        })
    }

    /// Gets speed information for the edge identified by `graph_id`.
    ///
    /// # Safety
    ///
    /// Basically assumes pointer alignment (will panic otherwise) and that the edge info is valid.
    /// See the [type-level documentation](TrafficTileProvider) for details.
    ///
    /// # Errors
    ///
    /// Fails if the edge doesn't exist in the traffic tile.
    pub unsafe fn get_speeds_for_edge(
        &self,
        graph_id: GraphId,
    ) -> Result<TrafficSpeed, GraphTileProviderError> {
        // SAFETY: Assumes the header is present and valid,
        // by assuming we are the only writer process.
        let speed_pointer = unsafe { self.get_pointer_for_edge(graph_id)? };

        // SAFETY: Assumes the count in the tile header is correct (see above assumptions).
        // If the header reports a higher than directed edge count, this could read out of bounds.
        // Also assumes that the architecture is able to guarantee atomicity of the operation
        // (no torn reads/writes).
        // This is true for our current architectures, which do atomic loads and stores
        // of 64-bit aligned pointers.
        // The alignment is asserted internally.
        Ok(TrafficSpeed::from_bits(unsafe {
            speed_pointer.read_volatile()
        }))
    }

    /// Gets a pointer structure for the given edge.
    ///
    /// # Safety
    ///
    /// Assumes that the header is present and valid.
    /// It is the responsibility of the caller to ensure this.
    unsafe fn get_pointer_for_edge(
        &self,
        graph_id: GraphId,
    ) -> Result<MmapTilePointer, GraphTileProviderError> {
        const HEADER_SIZE: usize = size_of::<TrafficTileHeader>();
        const SPEED_SIZE: usize = size_of::<TrafficSpeed>();

        let tile_pointer = self
            .tarball_tile_provider
            .get_pointer_for_tile_containing(graph_id)?;
        let header_pointer = MmapTilePointer {
            mmap: tile_pointer.mmap.clone(),
            offsets: TileOffset {
                // Same offset
                offset: tile_pointer.offsets.offset,
                size: HEADER_SIZE as u32,
            },
        };

        // SAFETY: TBH this probably isn't possible to make completely safe
        // given the current architecture of Valhalla and fundamental unsafety of shared memory maps.
        // However, at the time of this writing, all fields are u32 or u64,
        // which will *probably* prevent any sort of read/write tearing.
        // Additionally, Valhalla (at the time of this writing) has no mechanism for hot swapping
        // the underlying graph, which means we can assume the directed edge count will never change
        // for a given tile during the life of the program.
        let header: TrafficTileHeader = unsafe { header_pointer.read_volatile() };

        if header.traffic_tile_version() != TRAFFIC_TILE_VERSION {
            return Err(GraphTileProviderError::UnsupportedTileVersion);
        }

        if graph_id.feature_index() >= u64::from(header.directed_edge_count()) {
            return Err(GraphTileProviderError::GraphTileLookupError(
                LookupError::InvalidIndex,
            ));
        }

        Ok(MmapTilePointer {
            mmap: tile_pointer.mmap.clone(),
            offsets: TileOffset {
                // Tile structure: header + [TileSpeed]
                offset: tile_pointer.offsets.offset
                    + (HEADER_SIZE as u64)
                    + (SPEED_SIZE as u64 * graph_id.feature_index()),
                size: SPEED_SIZE as u32,
            },
        })
    }

    /// An iterator over all tile IDs contained in the tarball, in arbitrary order.
    pub fn tile_ids(&self) -> impl Iterator<Item = &GraphId> {
        self.tarball_tile_provider.tile_ids()
    }
}

impl TrafficTileProvider<false> {
    /// Creates a new traffic tile provider from an existing tarball extract.
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

impl TrafficTileProvider<true> {
    /// Creates a new traffic tile provider from an existing tarball extract.
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
    /// If this method returns with an `Ok` result,
    /// the data has been persisted to disk.
    /// Modifications may also be _eventually_ flushed in other situations,
    /// such as when the memory is unmapped again.
    /// But this is the only way to ensure durability.
    ///
    /// # Errors
    ///
    /// Returns a relevant I/O error if the flush fails.
    pub fn flush(&self) -> std::io::Result<()> {
        self.tarball_tile_provider.flush()
    }

    /// Updates the speed data stored for an edge.
    ///
    /// NOTE: this will update the memory map immediately,
    /// but it does not guarantee that the data has been durably stored until you call
    /// [`TrafficTileProvider<true>::flush`]!
    ///
    /// # Safety
    ///
    /// Basically assumes pointer alignment (will panic otherwise) and that the edge info is valid.
    /// Additionally, this assumes that the platform supports atomic 64-bit integer store operations.
    /// See the [type-level documentation](TrafficTileProvider) for details.
    ///
    /// # Errors
    ///
    /// Fails if the edge doesn't exist in the traffic tile.
    pub unsafe fn update_speed_for_edge(
        &self,
        graph_id: GraphId,
        speed: TrafficSpeed,
    ) -> Result<(), GraphTileProviderError> {
        // SAFETY: Assumes the header is present and valid,
        // by assuming we are the only writer process.
        let speed_pointer = unsafe { self.get_pointer_for_edge(graph_id)? };

        // SAFETY: Assumes the count in the tile header is correct (see above assumptions).
        // If the header reports a higher than directed edge count, this could read out of bounds.
        // Also assumes the memory is writable (would panic if not) and aligned (checked internally).
        unsafe { speed_pointer.write_volatile(speed) };
        Ok(())
    }
}

#[cfg(all(test, not(miri)))]
mod tests {
    use crate::GraphId;
    use crate::tile_provider::TrafficTileProvider;
    use crate::traffic_tile::{SpeedValue, TrafficSpeed};
    use std::path::PathBuf;

    #[test]
    fn test_get_speed() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-traffic.tar");
        let provider =
            TrafficTileProvider::new_readonly(path).expect("Unable to init tile provider");

        // This edge has no speed info
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let edge_speed = unsafe {
            provider
                .get_speeds_for_edge(graph_id)
                .expect("Unable to get tile")
        };

        assert!(!edge_speed.has_valid_speed());

        // This edge DOES have speed info
        let graph_id =
            GraphId::try_from_components(0, 3015, 42).expect("Unable to create graph ID");
        let edge_speed = unsafe {
            provider
                .get_speeds_for_edge(graph_id)
                .expect("Unable to get speed")
        };

        assert_eq!(edge_speed.overall_speed(), Some(32));
    }

    #[test]
    fn test_set_speed() {
        const DESIRED_SPEED: u8 = 32;

        let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-traffic.tar");

        // let tmp_path = PathBuf::from("/Users/ianthetechie/valhalla-docker/valhalla/traffic.tar");
        let tmp_dir = option_env!("RUNNER_TEMP").unwrap_or("/tmp");
        let tmp_path = PathBuf::from(tmp_dir).join("traffic-test-set-speed.tar");
        std::fs::copy(fixture_path, &tmp_path).expect("Failed to copy");
        let provider =
            TrafficTileProvider::new_mutable(tmp_path).expect("Unable to init tile provider");
        let graph_id =
            GraphId::try_from_components(0, 3015, 42).expect("Unable to create graph ID");
        let edge_speed = unsafe {
            provider
                .get_speeds_for_edge(graph_id)
                .expect("Unable to get speed")
        };

        assert_eq!(
            edge_speed.overall_speed(),
            Some(32),
            "It looks like the traffic tar may have been cached from a previous run"
        );

        unsafe {
            provider
                .update_speed_for_edge(
                    graph_id,
                    TrafficSpeed::single_speed(SpeedValue::try_new(DESIRED_SPEED).unwrap(), None),
                )
                .expect("Failed to set speed for edge");
        }

        let edge_speed = unsafe {
            provider
                .get_speeds_for_edge(graph_id)
                .expect("Unable to get speed")
        };
        assert!(edge_speed.has_valid_speed());
        assert_eq!(edge_speed.overall_speed(), Some(DESIRED_SPEED));
    }
}
