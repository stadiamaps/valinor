use crate::GraphId;
use crate::graph_id::InvalidGraphIdError;
use crate::graph_tile::GraphTileHandle;
use crate::graph_tile::{GraphTileBuildError, GraphTileBuilder};
use crate::tile_provider::{GraphTileProvider, GraphTileProviderError, LockTable};
use lru::LruCache;
use std::io::ErrorKind;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;
use tokio::{
    fs::File,
    io::{AsyncWriteExt, BufWriter},
};

pub struct DirectoryTileProvider {
    base_directory: PathBuf,
    lock_table: LockTable<GraphId>,
    // TODO: This is a bit hackish for now, but even so it speeds things up MASSIVELY for many workloads!
    lru_cache: Mutex<LruCache<GraphId, Arc<GraphTileHandle>>>,
}

impl DirectoryTileProvider {
    pub fn new(base_directory: PathBuf, num_cached_tiles: NonZeroUsize) -> Self {
        DirectoryTileProvider {
            base_directory,
            lock_table: LockTable::new(),
            lru_cache: Mutex::new(LruCache::new(num_cached_tiles)),
        }
    }

    /// Replaces the tile stored at the designated location
    /// with the tile produced by this builder.
    ///
    /// # Data race safety
    ///
    /// The implementation takes the following steps to ensure data race safety:
    ///
    /// - Acquires a lock at the start of the call, ensuring that calls to [`DirectoryTileProvider::get_tile_containing`]
    ///   block until this method exits.
    /// - Writes to a temporary file initially, so if anything goes wrong, the original file is not affected.
    ///   After successfully writing the temp file, it is atomically renamed on top of the original.
    /// - Clears the internal tile cache (local to _this_ [`DirectoryTileProvider`] instance!)
    ///   once the rename succeeds.
    /// - Releases the lock, unblocking access to this tile, only after everything succeeds,
    ///   or fails mid-write (in which case, only the temporary file is affected).
    ///
    /// In this way, a (single!) [`DirectoryTileProvider`] should be safe to use in async contexts,
    /// without fear of races from writers.
    /// Additionally, since readers always have to wait for a writer to finish,
    /// readers will never get a partially written tile, nor will they get a stale tile
    /// if there is an open write operation.
    ///
    /// ## Edge cases
    ///
    /// Once you have a handle to a graph tile from [`DirectoryTileProvider::get_tile_containing`],
    /// the lock is freed and a writer may then proceed.
    /// Your handle will _not_ change or block writers,
    /// creating an opportunity for edge cases (especially if you plan to create a builder from this tile
    /// to write changes!).
    ///
    /// So, if your workload involves both reads and writes,
    /// **you _must_ ensure that your tile references cannot be stale.**
    /// This probably means some sort of partition mutex in your processing loop.
    ///
    /// Additionally, if the write operation fails, your graph tile builder is gone.
    /// The original file on disk is not in a dirty state, but to retry again,
    /// the caller would need to reconstruct the same builder from scratch.
    pub async fn overwrite_tile(
        &self,
        graph_tile_builder: GraphTileBuilder<'_>,
    ) -> Result<(), GraphTileBuildError> {
        let graph_id = graph_tile_builder.graph_id();

        let lock = self.lock_table.lock_for(graph_id);
        let _guard = lock.lock().await;

        let path = self.path_for_graph_id(graph_id)?;

        // Write to a temp file
        let tmp_path = path.with_extension(".tmp");
        let file = File::create(&tmp_path).await?;
        let mut writer = BufWriter::new(file);

        for section in graph_tile_builder.into_byte_iter()? {
            writer.write_all(&section).await?;
        }

        writer.flush().await?;

        // Replace the original file atomically
        tokio::fs::rename(tmp_path, path).await?;

        let mut cache = self
            .lru_cache
            .lock()
            .map_err(|e| GraphTileBuildError::PoisonedCacheLock(e.to_string()))?;
        // Invalidate the cache
        cache.pop(&graph_id);

        Ok(())
    }

    /// Computes the path for the given graph ID.
    ///
    /// NOTE: This function assumes that the graph ID is already a base ID.
    fn path_for_graph_id(&self, graph_id: GraphId) -> Result<PathBuf, InvalidGraphIdError> {
        Ok(self.base_directory.join(graph_id.file_path("gph")?))
    }
}

#[async_trait]
impl GraphTileProvider for DirectoryTileProvider {
    async fn get_tile_containing(
        &self,
        graph_id: GraphId,
    ) -> Result<Arc<GraphTileHandle>, GraphTileProviderError> {
        let lock = self.lock_table.lock_for(graph_id);
        let _guard = lock.lock().await;

        // Build up the path from the base directory + tile ID components
        // TODO: Do we want to move the base ID check inside file_path?
        let base_graph_id = graph_id.tile_base_id();
        let mut cache = self
            .lru_cache
            .lock()
            .map_err(|e| GraphTileProviderError::PoisonedCacheLock(e.to_string()))?;
        let tile = cache
            .try_get_or_insert(base_graph_id, || {
                let path = self.path_for_graph_id(base_graph_id)?;
                // Open the file and read all bytes into a buffer
                // NOTE: Does not handle compressed tiles
                let data = std::fs::read(path).map_err(|e| match e.kind() {
                    ErrorKind::NotFound => GraphTileProviderError::TileDoesNotExist,
                    _ => GraphTileProviderError::IoError(e),
                })?;
                let tile = GraphTileHandle::try_from(data)?;
                Ok::<_, GraphTileProviderError>(Arc::new(tile))
            })
            .cloned()?;

        // Construct a graph tile with the bytes
        Ok(tile)
    }
}

#[cfg(test)]
mod test {
    use super::DirectoryTileProvider;
    use crate::GraphId;
    use crate::graph_tile::GraphTile;
    use crate::tile_provider::GraphTileProvider;
    use rand::{
        distr::{Distribution, Uniform},
        rng,
    };
    use std::num::NonZeroUsize;
    use std::path::PathBuf;

    #[tokio::test]
    async fn test_get_tile() {
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryTileProvider::new(base, NonZeroUsize::new(1).unwrap());
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let tile = provider
            .get_tile_containing(graph_id)
            .await
            .expect("Unable to get tile");

        // Minimally test that we got the correct tile
        assert_eq!(tile.header().graph_id(), graph_id);
        assert_eq!(tile.header().graph_id().value(), graph_id.value());
    }

    #[tokio::test]
    async fn test_get_opp_edge() {
        let mut rng = rng();

        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryTileProvider::new(base, NonZeroUsize::new(1).unwrap());
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let tile = provider
            .get_tile_containing(graph_id)
            .await
            .expect("Unable to get tile");

        // Cross-check the default implementation of the opposing edge ID function.
        // We only check a subset because it takes too long otherwise.
        // See the performance note on get_opposing_edge.
        let range = Uniform::try_from(0..u64::from(tile.header().directed_edge_count())).unwrap();
        for index in range.sample_iter(&mut rng).take(100) {
            let edge_id = graph_id.with_index(index).expect("Invalid graph ID.");
            let opp_edge_index = tile
                .get_opp_edge_index(edge_id)
                .expect("Unable to get opp edge index.");
            let (opp_edge_id, _) = provider
                .get_opposing_edge(edge_id)
                .await
                .expect("Unable to get opposing edge.");
            assert_eq!(u64::from(opp_edge_index), opp_edge_id.index());
        }
    }
}
