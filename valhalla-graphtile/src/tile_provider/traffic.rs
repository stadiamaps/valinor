use crate::GraphId;
use crate::graph_tile::{LookupError, MmapTilePointer, TileOffset};
use crate::tile_provider::{GraphTileProviderError, TarballTileProvider};
use crate::traffic_tile::{TrafficSpeed, TrafficTileHeader};
use std::path::Path;
use std::sync::atomic::Ordering;

pub struct TrafficTileProvider {
    tarball_tile_provider: TarballTileProvider,
}

impl TrafficTileProvider {
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

    pub async fn get_speeds_for_edge(
        &self,
        graph_id: GraphId,
    ) -> Result<TrafficSpeed, GraphTileProviderError> {
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
        // given the current architecture of Valhalla.
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

        let speed_pointer = MmapTilePointer {
            mmap: tile_pointer.mmap.clone(),
            offsets: TileOffset {
                // Tile structure: header + [TileSpeed]
                offset: tile_pointer.offsets.offset
                    + (HEADER_SIZE as u64)
                    + (SPEED_SIZE as u64 * graph_id.index()),
                size: SPEED_SIZE as u32,
            },
        };

        // Safety: Assumes the count in the tile header is correct (see above assumptions).
        // If the header reports a higher than directed edge count, this could read out of bounds.
        let atomic_handle = unsafe { speed_pointer.as_atomic_u64() };
        Ok(TrafficSpeed::from_bits(
            atomic_handle.load(Ordering::Acquire).into(),
        ))
    }
}

#[cfg(all(test, not(miri)))]
mod tests {
    use crate::GraphId;
    use crate::tile_provider::TrafficTileProvider;
    use std::path::PathBuf;

    #[tokio::test]
    async fn test_get_speed() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-traffic.tar");
        let provider = TrafficTileProvider::new(path).expect("Unable to init tile provider");
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let edge_speed = provider
            .get_speeds_for_edge(graph_id)
            .await
            .expect("Unable to get tile");

        assert!(!edge_speed.has_valid_speed());
    }
}
