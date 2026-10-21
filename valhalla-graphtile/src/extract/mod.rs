//! # Offline tile extract generation
//!
//! This module writes *sub-extracts* of an existing set of Valhalla graph tiles:
//! fully spec-compliant tarballs which contain a subset of the source tiles.
//! The source can be any [`TileBytesSource`](crate::tile_provider::TileBytesSource),
//! such as an extract tarball
//! ([`TarballTileProvider`](crate::tile_provider::TarballTileProvider))
//! or a tile directory
//! ([`DirectoryGraphTileProvider`](crate::tile_provider::DirectoryGraphTileProvider)).
//! The output is interchangeable with `valhalla_build_extract` output,
//! so it is consumable by both stock Valhalla
//! and [`TarballTileProvider`](crate::tile_provider::TarballTileProvider).
//!
//! # Writing
//!
//! [`write_extract`] streams the archive in a single pass:
//! an `index.bin` entry first
//! (see [`serialize_index_bin`](crate::tile_provider::serialize_index_bin)),
//! followed by the graph tiles sorted ascending by (level, tile index)
//! (note that this differs from the `Ord` impl of [`GraphId`](crate::GraphId),
//! which deliberately orders levels in reverse).
//! Output is deterministic:
//! the same source tiles and tile set always produce byte-identical output.

mod writer;

pub use writer::{ExtractLayoutError, ExtractWriteError, write_extract};
