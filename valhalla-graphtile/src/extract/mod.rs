//! Offline tile extracts: tarballs with a subset of the tiles of a
//! [`GraphTileProvider`](crate::tile_provider::GraphTileProvider).

mod writer;

pub use writer::{ExtractWriteError, write_extract};
