//! Offline tile extracts: tarballs with a subset of the tiles of a
//! [`TileBytesSource`](crate::tile_provider::TileBytesSource).
//!
//! [`write_extract`] writes an extract in the format of `valhalla_build_extract`,
//! so stock Valhalla and [`TarballTileProvider`](crate::tile_provider::TarballTileProvider)
//! can read it.

mod writer;

pub use writer::{ExtractLayoutError, ExtractWriteError, write_extract};
