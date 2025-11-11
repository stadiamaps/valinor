use crate::GraphId;
use crate::graph_tile::{LookupError, MmapTilePointer, TileOffset};
use crate::tile_provider::{GraphTileProviderError, TarballTileProvider};
use crate::traffic_tile::{TrafficSpeed, TrafficTileHeader};
use std::path::Path;

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
    /// # Errors
    ///
    /// Fails if the edge doesn't exist in the traffic tile.
    pub async fn get_speeds_for_edge(
        &self,
        graph_id: GraphId,
    ) -> Result<TrafficSpeed, GraphTileProviderError> {
        let speed_pointer = self.get_pointer_for_edge(graph_id).await?;

        // Safety: Assumes the count in the tile header is correct (see above assumptions).
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

    #[cfg(target_has_atomic = "8")]
    async fn get_pointer_for_edge(
        &self,
        graph_id: GraphId,
    ) -> Result<MmapTilePointer, GraphTileProviderError> {
        const HEADER_SIZE: usize = size_of::<TrafficTileHeader>();
        const SPEED_SIZE: usize = size_of::<TrafficSpeed>();

        let tile_pointer = self
            .tarball_tile_provider
            .get_tile_containing(graph_id)
            .await?;
        let header_pointer = MmapTilePointer {
            mmap: tile_pointer.mmap.clone(),
            offsets: TileOffset {
                // Same offset
                offset: tile_pointer.offsets.offset,
                size: HEADER_SIZE as u32,
            },
        };

        // Safety: TBH this probably isn't possible to make completely safe
        // given the current architecture of Valhalla and fundamental unsafety of shared memory maps.
        // However, at the time of this writing, all fields are u32 or u64,
        // which will *probably* prevent any sort of read/write tearing.
        // Additionally, Valhalla (at the time of this writing) has no mechanism for hot swapping
        // the underlying graph, which means we can assume the directed edge count will never change
        // for a given tile during the life of the program.
        let header: TrafficTileHeader = unsafe { header_pointer.read_volatile() };
        if graph_id.index() >= u64::from(header.directed_edge_count()) {
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
                    + (SPEED_SIZE as u64 * graph_id.index()),
                size: SPEED_SIZE as u32,
            },
        })
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
    /// # Errors
    ///
    /// Fails if the edge doesn't exist in the traffic tile.
    pub async fn update_speed_for_edge(
        &self,
        graph_id: GraphId,
        speed: TrafficSpeed,
    ) -> Result<(), GraphTileProviderError> {
        let speed_pointer = self.get_pointer_for_edge(graph_id).await?;

        // Safety: Assumes the count in the tile header is correct (see above assumptions).
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
    use crate::traffic_tile::TrafficSpeed;
    use std::path::PathBuf;

    #[tokio::test]
    async fn test_get_speed() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-traffic.tar");
        let provider =
            TrafficTileProvider::new_readonly(path).expect("Unable to init tile provider");

        // This edge has no speed info
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let edge_speed = provider
            .get_speeds_for_edge(graph_id)
            .await
            .expect("Unable to get tile");

        assert!(!edge_speed.has_valid_speed());

        // This edge DOES have speed info
        let graph_id =
            GraphId::try_from_components(0, 3015, 42).expect("Unable to create graph ID");
        let edge_speed = provider
            .get_speeds_for_edge(graph_id)
            .await
            .expect("Unable to get speed");

        assert_eq!(edge_speed.overall_speed(), Some(32));
    }

    #[tokio::test]
    async fn test_set_speed() {
        const DESIRED_SPEED: u8 = 32;

        let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-traffic.tar");

        let tmp_dir = option_env!("RUNNER_TEMP").unwrap_or("/tmp");
        let tmp_path = PathBuf::from(tmp_dir).join("traffic-test-set-speed.tar");
        std::fs::copy(fixture_path, &tmp_path).expect("Failed to copy");
        let provider =
            TrafficTileProvider::new_mutable(tmp_path).expect("Unable to init tile provider");
        let graph_id =
            GraphId::try_from_components(0, 3015, 42).expect("Unable to create graph ID");
        let edge_speed = provider
            .get_speeds_for_edge(graph_id)
            .await
            .expect("Unable to get speed");

        assert_eq!(edge_speed.overall_speed(), Some(32), "It looks like the traffic tar may have been cached from a previous run");

        provider
            .update_speed_for_edge(graph_id, TrafficSpeed::single_speed(DESIRED_SPEED).unwrap())
            .await
            .expect("Failed to set speed for edge");

        let edge_speed = provider
            .get_speeds_for_edge(graph_id)
            .await
            .expect("Unable to get speed");
        assert!(edge_speed.has_valid_speed());
        assert_eq!(edge_speed.overall_speed(), Some(DESIRED_SPEED));
    }
}
