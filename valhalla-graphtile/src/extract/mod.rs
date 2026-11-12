//! Tile extracts: tarballs with a subset of the tiles of a
//! [`GraphTileProvider`](crate::tile_provider::GraphTileProvider).

#[cfg(test)]
mod test_archive;
mod writer;

pub use writer::{ExtractError, write_extract};
