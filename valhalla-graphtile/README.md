# valhalla-graphtile

This crate exposes (mostly!) safe interfaces for reading and writing Valhalla graph tiles.

## Goals

- Zero-copy (using the eponymous crate from Google for most of the heavy lifting)
- Safe public interface
- Maintainability and testability improvements over the original C++ implementation
- Portability, where reasonable

## Example

Most usage of this crate will probably start with a [`GraphTileProvider`](valhalla_graphtile::tile_provider::GraphTileProvider).
For example, here's how you can query a tile for nearby nodes:

```rust
use std::path::PathBuf;
use std::num::NonZeroUsize;
use valhalla_graphtile::GraphId;
use valhalla_graphtile::tile_provider::{DirectoryGraphTileProvider, GraphTileProvider};
use geo::Point;

// This example uses the directory tile provider, but there are also others (e.g. memory mapped tarball)
let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("andorra-tiles");
let provider = DirectoryGraphTileProvider::new(base, NonZeroUsize::new(4).unwrap());

// nodes_within_radius is a high-level helper function that gets nodes near a certain point
// The result of nodes_within_radius is an un-sorted iterator that lets you get results quickly with ~zero overhead.
let mut results = provider
    .nodes_within_radius(
        // A filter predicate (e.g. to filter for only nodes with specific properties)
        // which is applied *before* distance checks. Here we pass all nodes.
        |_| true,
        // Our point query
        Point::new(1.515459, 42.544805),
        // Radius in meters
        25.0,
    )
    .map(|result| result.map(|node_ref| (node_ref.graph_id(), node_ref.approx_distance())))
    .collect::<Result<Vec<(GraphId, f64)>, _>>()
    .expect("Something went wrong fetching tiles");

// Sort by distance
results.sort_unstable_by(|a, b| a.1.total_cmp(&b.1));
```

## Testing

This crate heavily leverages snapshot tests in addition to regular unit tests.
The test suite covers reading graph tiles from a test fixture (a real tile) and exercises the entire public interface
to minimize the risk of non-obvious bugs being introduced.
Tile fixtures are generated using standard Valhalla tooling.

Additionally, all tests are run in CI, both normally and under Miri to detect any latent undefined behavior (since this sort of packed binary format casting is rather tricky).
Tests are also run under the `s390x-unknown-linux-gnu` target (via QEMU; both regular tests and Miri)
to ensure that everything works on a big endian architecture.
