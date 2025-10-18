use crate::GraphId;
use crate::graph_tile::GraphTileHandle;
use crate::tile_provider::{GraphTileProvider, GraphTileProviderError};
use lru::LruCache;
use std::cell::RefCell;
use std::io::ErrorKind;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::rc::Rc;

pub struct DirectoryTileProvider {
    base_directory: PathBuf,
    // TODO: This is SUPER hackish for now...
    lru_cache: RefCell<LruCache<GraphId, Rc<GraphTileHandle>>>,
}

impl DirectoryTileProvider {
    pub fn new(base_directory: PathBuf, num_cached_tiles: NonZeroUsize) -> Self {
        DirectoryTileProvider {
            base_directory,
            lru_cache: RefCell::new(LruCache::new(num_cached_tiles)),
        }
    }
}

impl GraphTileProvider for DirectoryTileProvider {
    fn get_tile_containing(
        &self,
        graph_id: GraphId,
    ) -> Result<Rc<GraphTileHandle>, GraphTileProviderError> {
        // Build up the path from the base directory + tile ID components
        // TODO: Do we want to move the base ID check inside file_path?
        let base_graph_id = graph_id.tile_base_id();
        let mut cache = self.lru_cache.borrow_mut();
        let tile = cache
            .try_get_or_insert(base_graph_id, || {
                let path = self.base_directory.join(base_graph_id.file_path("gph")?);
                // Open the file and read all bytes into a buffer
                // NOTE: Does not handle compressed tiles
                let data = std::fs::read(path).map_err(|e| match e.kind() {
                    ErrorKind::NotFound => GraphTileProviderError::TileDoesNotExist,
                    _ => GraphTileProviderError::IoError(e),
                })?;
                let tile = GraphTileHandle::try_from(data)?;
                Ok::<_, GraphTileProviderError>(Rc::new(tile))
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

    #[test]
    fn test_get_tile() {
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        let provider = DirectoryTileProvider::new(base, NonZeroUsize::new(1).unwrap());
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let tile = provider
            .get_tile_containing(graph_id)
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
        let provider = DirectoryTileProvider::new(base, NonZeroUsize::new(1).unwrap());
        let graph_id = GraphId::try_from_components(0, 3015, 0).expect("Unable to create graph ID");
        let tile = provider
            .get_tile_containing(graph_id)
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
                .expect("Unable to get opposing edge.");
            assert_eq!(u64::from(opp_edge_index), opp_edge_id.index());
        }
    }
}
