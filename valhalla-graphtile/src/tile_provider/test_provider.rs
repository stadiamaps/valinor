//! Tile providers and tile directories for tests.

use crate::GraphId;
use crate::graph_tile::GraphTileView;
use crate::graph_tile::handles::OwnedGraphTileHandle;
use crate::test_fixtures;
use crate::tile_provider::{
    DirectoryGraphTileProvider, GraphTileProvider, GraphTileProviderError, TILE_FILE_EXTENSION,
};
use core::num::NonZeroUsize;
use geo::{CoordFloat, Point};
use num_traits::FromPrimitive;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tempfile::TempDir;

/// Returns a directory provider for `base` with a cache of one tile.
pub(crate) fn directory_provider(base: &Path) -> DirectoryGraphTileProvider {
    DirectoryGraphTileProvider::new(base.to_path_buf(), NonZeroUsize::MIN)
}

/// Copies [`test_fixtures::smallest_andorra_tile`] into a new temporary tile directory.
/// Returns the directory and the path of the tile file.
pub(crate) fn copy_small_tile() -> (TempDir, PathBuf) {
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

/// The Andorra tile directory, with sizes and read errors that a test can change.
pub(crate) struct TestProvider {
    inner: DirectoryGraphTileProvider,
    /// Sizes that [`GraphTileProvider::tile_size`] returns in place of the real sizes.
    pub(crate) reported_sizes: HashMap<GraphId, u32>,
    /// Base tile IDs for which [`GraphTileProvider::tile_size`] fails.
    pub(crate) size_failures: HashSet<GraphId>,
    /// Base tile IDs for which [`GraphTileProvider::get_handle_for_tile_containing`] fails.
    pub(crate) read_failures: HashSet<GraphId>,
}

impl TestProvider {
    pub(crate) fn new() -> Self {
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
