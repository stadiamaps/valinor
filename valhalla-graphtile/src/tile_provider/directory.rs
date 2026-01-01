use crate::GraphId;
use crate::graph_id::InvalidGraphIdError;
use crate::graph_tile::{GraphTileBuildError, GraphTileBuilder};
use crate::graph_tile::{GraphTileView, handles::OwnedGraphTileHandle};
use crate::spatial::bbox_with_center;
use crate::tile_hierarchy::STANDARD_LEVELS;
use crate::tile_provider::{
    GraphTileProvider, GraphTileProviderError, LockTable, OwnedGraphTileProvider,
};
use geo::{CoordFloat, Point};
use lru::LruCache;
use num_traits::FromPrimitive;
use std::io::{ErrorKind, Write};
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::{fs::File, io::BufWriter};

/// A graph tile provider that is backed by a directory of tiles.
///
/// # Resource consumption
///
/// To minimize file handle churn and re-validation of the mapped tile memory,
/// this includes an internal LRU cache.
/// This is configurable with a max number of cached tiles.
/// Any cached tiles will remain in memory.
pub struct DirectoryGraphTileProvider {
    base_directory: PathBuf,
    lock_table: LockTable<GraphId>,
    // TODO: This is a bit hackish for now, but even so it speeds things up MASSIVELY for many workloads!
    lru_cache: Mutex<LruCache<GraphId, Arc<OwnedGraphTileHandle>>>,
}

impl DirectoryGraphTileProvider {
    pub fn new(base_directory: PathBuf, num_cached_tiles: NonZeroUsize) -> Self {
        DirectoryGraphTileProvider {
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
    /// - Acquires a lock at the start of the call, ensuring that calls to [`DirectoryGraphTileProvider::get_tile_containing`]
    ///   block until this method exits.
    /// - Writes to a temporary file initially, so if anything goes wrong, the original file is not affected.
    ///   After successfully writing the temp file, it is atomically renamed on top of the original.
    /// - Clears the internal tile cache (local to _this_ [`DirectoryGraphTileProvider`] instance!)
    ///   once the rename succeeds.
    /// - Releases the lock, unblocking access to this tile, only after everything succeeds,
    ///   or fails mid-write (in which case, only the temporary file is affected).
    ///
    /// In this way, a (single!) [`DirectoryGraphTileProvider`] should be safe to use in async contexts,
    /// without fear of races from writers.
    /// Additionally, since readers always have to wait for a writer to finish,
    /// readers will never get a partially written tile, nor will they get a stale tile
    /// if there is an open write operation.
    ///
    /// ## Edge cases
    ///
    /// Once you have a handle to a graph tile from [`DirectoryGraphTileProvider::get_tile_containing`],
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
    ///
    /// # Errors
    ///
    /// This function may fail in a variety of cases that are returned as errors:
    ///
    /// - The tile was explicitly constructed with an invalid graph ID
    /// - The graph tile builder is invalid (see [`GraphTileBuilder::into_byte_iter`] for details)
    /// - Writing the temporary file fails
    /// - The atomic file rename fails
    /// - The internal tile cache lock is corrupted (this should never happen; if it does, it's an error in Valinor)
    pub fn overwrite_tile(
        &self,
        graph_tile_builder: GraphTileBuilder<'_>,
    ) -> Result<(), GraphTileBuildError> {
        let graph_id = graph_tile_builder.graph_id();

        let lock = self.lock_table.lock_for(graph_id);
        let _guard = lock.lock();

        let path = self.path_for_graph_id(graph_id)?;

        // Write to a temp file
        let tmp_path = path.with_extension(".tmp");
        let file = File::create(&tmp_path)?;
        let mut writer = BufWriter::new(file);

        for section in graph_tile_builder.into_byte_iter()? {
            writer.write_all(&section)?;
        }

        writer.flush()?;

        // Replace the original file atomically
        std::fs::rename(tmp_path, path)?;

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

impl GraphTileProvider for DirectoryGraphTileProvider {
    #[inline]
    fn with_tile_containing<F, T>(
        &self,
        graph_id: GraphId,
        process: F,
    ) -> Result<T, GraphTileProviderError>
    where
        F: FnOnce(&GraphTileView) -> T,
    {
        let tile = self.get_handle_for_tile_containing(graph_id)?;
        Ok(process(tile.borrow_dependent()))
    }

    fn enumerate_tiles_within_radius<N: CoordFloat + FromPrimitive>(
        &self,
        center: Point<N>,
        radius: N,
    ) -> Vec<GraphId> {
        let mut out: Vec<GraphId> = Vec::new();

        let (north, east, south, west) = bbox_with_center(center, radius);

        for level in STANDARD_LEVELS.iter() {
            for gid in level.tiles_intersecting_bbox(north, east, south, west) {
                if self.get_handle_for_tile_containing(gid).is_ok() {
                    out.push(gid);
                }
            }
        }

        out
    }
}

impl OwnedGraphTileProvider<Arc<OwnedGraphTileHandle>> for DirectoryGraphTileProvider {
    fn get_handle_for_tile_containing(
        &self,
        graph_id: GraphId,
    ) -> Result<Arc<OwnedGraphTileHandle>, GraphTileProviderError> {
        let lock = self.lock_table.lock_for(graph_id);
        let _guard = lock.lock();

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
                let tile = OwnedGraphTileHandle::try_from(data)?;
                Ok::<_, GraphTileProviderError>(Arc::new(tile))
            })
            .cloned()?;

        // Construct a graph tile with the bytes
        Ok(tile)
    }
}

#[cfg(test)]
mod test {
    use super::DirectoryGraphTileProvider;
    use crate::GraphId;
    use crate::graph_tile::GraphTile;
    use crate::tile_hierarchy::STANDARD_LEVELS;
    use crate::tile_provider::{GraphTileProvider, OwnedGraphTileProvider};
    use core::num::NonZeroUsize;
    use rand::{
        distr::{Distribution, Uniform},
        rng,
    };
    use std::collections::HashSet;
    use std::path::PathBuf;

    #[test]
    fn test_get_tile() {
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryGraphTileProvider::new(base, NonZeroUsize::new(1).unwrap());
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let tile = provider
            .get_handle_for_tile_containing(graph_id)
            .expect("Unable to get tile");

        // Minimally test that we got the correct tile
        assert_eq!(tile.header().graph_id(), graph_id);
        assert_eq!(tile.header().graph_id().value(), graph_id.value());
    }

    #[test]
    fn test_get_opp_edge() {
        let mut rng = rng();

        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryGraphTileProvider::new(base, NonZeroUsize::new(1).unwrap());
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let tile = provider
            .get_handle_for_tile_containing(graph_id)
            .expect("Unable to get tile");

        // Cross-check the default implementation of the opposing edge ID function.
        // We only check a subset because it takes too long otherwise.
        let range = Uniform::try_from(0..u64::from(tile.header().directed_edge_count())).unwrap();
        for index in range.sample_iter(&mut rng).take(100) {
            let edge_id = graph_id
                .with_feature_index(index)
                .expect("Invalid graph ID.");
            let opp_edge_index = tile
                .get_opp_edge_index(edge_id)
                .expect("Unable to get opp edge index.");
            let opp_edge_id_1 = provider
                .graph_id_for_opposing_edge_index(opp_edge_index, tile.borrow_dependent())
                .expect("Unable to get the full ID for the opposing edge index!");

            let opp_edge_id_2 = provider
                .get_opposing_edge_id(edge_id, tile.borrow_dependent())
                .expect("Unable to get opposing edge.");
            assert_eq!(opp_edge_id_1, opp_edge_id_2);
        }
    }

    #[test]
    fn test_get_shortcut_fixture() {
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryGraphTileProvider::new(base, NonZeroUsize::new(1).unwrap());

        // This test relies on the state of the andorra-tiles fixtures.
        // TODO: Once we get full-on tile construction from scratch, build a test case rather than relying on the fixture.
        // This test was created with Valhalla as an oracle by adding the following code to valhalla_ways_to_edges.cc
        // and scanning for a few representative shortcuts:
        // if (edge->is_shortcut()) {
        //   auto shortcuts = reader.RecoverShortcut(edge_id);
        //
        //   std::ostringstream oss;
        //   oss << "[";
        //   for (size_t i = 0; i < shortcuts.size(); ++i) {
        //     if (i > 0)
        //       oss << ", ";
        //     oss << std::to_string(shortcuts[i]);
        //   }
        //   oss << "]";
        //
        //   LOG_INFO("Shortcut " + std::to_string(edge_id) + " contains edges: " + oss.str());
        // }
        let expected_shortcut_id = GraphId::try_from_components(0, 3015, 1).unwrap();
        let graph_id = GraphId::try_from_components(0, 3015, 4).unwrap();
        let shortcut_id = provider
            .get_shortcut(graph_id)
            .expect("Unable to get shortcut")
            .unwrap();

        assert_eq!(shortcut_id, expected_shortcut_id);

        let graph_id = GraphId::try_from_components(0, 3015, 19).unwrap();
        let shortcut_id = provider
            .get_shortcut(graph_id)
            .expect("Unable to get shortcut")
            .unwrap();

        assert_eq!(shortcut_id, expected_shortcut_id);
    }

    // TODO: An explicit test for a case spanning tiles would be nice, but the extract is too small.

    #[cfg(not(miri))]
    #[test]
    fn test_level_zero_shortcut_sanity() {
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryGraphTileProvider::new(base, NonZeroUsize::new(1).unwrap());

        let base_id = GraphId::try_from_components(0, 3015, 0).unwrap();
        provider.with_tile_containing_or_panic(base_id, |tile| {
            let mut found_non_superseded_edge_with_shortcuts = false;
            let mut edges_inside_shortcuts = 0;
            let mut unique_shortcut_ids = HashSet::new();
            for (idx, edge) in tile.directed_edges().iter().enumerate() {
                let graph_id = base_id
                    .with_feature_index(idx as u64)
                    .unwrap();

                // Property test style assertions through all edges in this (small) level zero tile
                let shortcut_id = if edge.is_superseded() {
                    let shortcut_id = provider
                        .get_shortcut(graph_id)
                        .unwrap();

                    assert!(
                        shortcut_id.is_some(),
                        "Superseded edges must be traceable back to a shortcut"
                    );
                    shortcut_id
                } else {
                    found_non_superseded_edge_with_shortcuts = true;
                    provider
                        .get_shortcut(graph_id)
                        .unwrap()
                };

                if let Some(shortcut_id) = shortcut_id {
                    // NOTE: This fixture also assumes we never go beyond a single tile
                    let shortcut_edge = tile
                        .get_directed_edge(shortcut_id)
                        .unwrap();
                    let edge_geom = tile.get_edge_info(edge).unwrap().decode_raw_shape::<f32>().unwrap();
                    let mut shortcut_edge_geom = tile.get_edge_info(shortcut_edge).unwrap().decode_raw_shape::<f32>().unwrap();

                    if edge.edge_info_is_forward() != shortcut_edge.edge_info_is_forward() {
                        shortcut_edge_geom.reverse();
                    }

                    assert!(shortcut_edge_geom.len() >= edge_geom.len(), "Shortcuts should be at least as long as the underlying edge geom");

                    if shortcut_edge_geom.len() == edge_geom.len() {
                        assert_eq!(shortcut_edge_geom, edge_geom);
                    } else {
                        // Make sure the shortcut edge contains the underlying geom
                        let mut found_match = false;
                        for s_offset in 0..shortcut_edge_geom.len() {
                            if shortcut_edge_geom[s_offset..].starts_with(&edge_geom) {
                                found_match = true;
                                break;
                            }
                        }

                        assert!(found_match, "Couldn't find any matching sub-geometry. Shortcut = {shortcut_edge_geom:?}; Edge = {edge_geom:?}");
                    }

                    edges_inside_shortcuts += 1;
                    unique_shortcut_ids.insert(shortcut_id);
                }
            }

            assert!(found_non_superseded_edge_with_shortcuts, "Expected to find non-superseded edges with shortcuts too");
            // You can verify and ballpark check (respectively) these numbers using the above C++ snippet in valhalla_ways_to_edges.cpp
            assert_eq!(unique_shortcut_ids.len(), 414);
            // We do a precise check here (even though it would break with a fixture tile rebuild)
            // to ensure we don't accidentally break the get_shortcut method in a subtle way
            // so that some shortcuts aren't reported.
            assert_eq!(edges_inside_shortcuts, 2448);
        });
    }

    #[test]
    fn test_hierarchy_properties() {
        // This test isn't quite so much about Valinor's correctness as it is about documenting
        // how the tile structure works.
        // Specifically, there is only a single "copy" of a feature in the routing graph,
        // and all features of a specific road class exist in specific tile levels.
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryGraphTileProvider::new(base, NonZeroUsize::new(1).unwrap());
        let graph_ids = vec![
            GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID"),
            GraphId::try_from_components(1, 47701, 0).expect("Unable to create graph ID"),
            GraphId::try_from_components(2, 762485, 0).expect("Unable to create graph ID"),
        ];

        for graph_id in graph_ids {
            let level = graph_id.level();
            let tile = provider
                .get_handle_for_tile_containing(graph_id)
                .expect("Unable to get tile");

            // Minimally test that we got the correct tile
            assert_eq!(tile.header().graph_id(), graph_id);
            assert_eq!(tile.header().graph_id().value(), graph_id.value());

            // Make sure the edges contain the types of edges we expect
            let level_info = &STANDARD_LEVELS[level as usize];
            assert_eq!(level_info.level, level);

            for edge in tile.directed_edges() {
                if level == 2 {
                    assert!(
                        !edge.is_shortcut(),
                        "We never expect to see a shortcut at level 2"
                    )
                }

                assert!(
                    edge.classification() <= level_info.minimum_road_class,
                    "Violated minimum road class restriction for this level"
                );

                if level > 0 {
                    assert!(
                        edge.classification()
                            > STANDARD_LEVELS[(level - 1) as usize].minimum_road_class,
                        "Unexpected feature with classification {:?} in tile level {level}",
                        edge.classification()
                    );
                }
            }
        }
    }
}
