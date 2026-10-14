//! # Offline tile extract generation
//!
//! This module writes *sub-extracts* of a full Valhalla tile extract:
//! smaller, fully spec-compliant tarballs which contain a subset of the source tiles.
//! The output is interchangeable with `valhalla_build_extract` output,
//! so it is consumable by both stock Valhalla
//! and [`TarballTileProvider`](crate::tile_provider::TarballTileProvider).
//!
//! # Writing
//!
//! The writer streams the archive in a single pass:
//! an `index.bin` entry first
//! (see [`serialize_index_bin`](crate::tile_provider::serialize_index_bin)),
//! followed by the graph tiles sorted ascending by (level, tile index)
//! (note that this differs from the `Ord` impl of [`GraphId`](crate::GraphId),
//! which deliberately orders levels in reverse).
//! Output is deterministic:
//! the same source extract and tile set always produce byte-identical output.
//! See [`ExtractLayout`] and [`write_extract_from_source`] for the details.

mod writer;

pub use writer::{
    ExtractLayout, ExtractLayoutError, ExtractWriteError, TileBytesSource, write_extract,
    write_extract_from_source,
};
