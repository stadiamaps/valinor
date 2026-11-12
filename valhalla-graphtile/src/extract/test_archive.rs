//! Checks for extract tarballs in tests, with the `tar` crate as an independent reader.

use crate::GraphId;
use crate::tile_provider::{
    INDEX_BIN_FILE_NAME, TAR_BLOCK_SIZE, TILE_FILE_EXTENSION, parse_index_bin,
};
use std::io::Read;
use std::path::Path;
use tar::Archive;

#[expect(clippy::cast_possible_truncation, reason = "512 fits in every usize")]
const BLOCK_LEN: usize = TAR_BLOCK_SIZE as usize;

fn read_entries(archive_bytes: &[u8]) -> Vec<(String, u64)> {
    Archive::new(archive_bytes)
        .entries()
        .expect("the archive is readable")
        .map(|entry| {
            let entry = entry.expect("every entry is readable");
            let path = String::from_utf8_lossy(&entry.path_bytes()).into_owned();
            (path, entry.raw_file_position())
        })
        .collect()
}

fn read_index_bytes(archive_bytes: &[u8]) -> Vec<u8> {
    let mut index_bytes = Vec::new();
    Archive::new(archive_bytes)
        .entries()
        .expect("the archive is readable")
        .next()
        .expect("the archive has entries")
        .expect("the index entry is readable")
        .read_to_end(&mut index_bytes)
        .expect("the index payload is readable");
    index_bytes
}

/// Checks an archive with the `tar` crate as an oracle,
/// then checks that each index entry gives the offset of its tile payload,
/// and that each payload equals the tile file in `tile_dir`.
pub(crate) fn check_archive(archive_bytes: &[u8], expected_tiles: &[GraphId], tile_dir: &Path) {
    assert!(
        archive_bytes.len().is_multiple_of(BLOCK_LEN),
        "The archive must be a whole number of tar blocks"
    );
    let marker_start = archive_bytes.len() - BLOCK_LEN * 2;
    assert!(
        archive_bytes[marker_start..].iter().all(|byte| *byte == 0),
        "The archive must end with two zero blocks"
    );

    let entries = read_entries(archive_bytes);
    let mut expected_paths = vec![INDEX_BIN_FILE_NAME.to_string()];
    // Tar entry names use `/` on every platform.
    expected_paths.extend(expected_tiles.iter().map(|graph_id| {
        let file_path = graph_id.file_path(TILE_FILE_EXTENSION).expect("valid tile");
        let components: Vec<&str> = file_path
            .iter()
            .map(|component| component.to_str().expect("tile paths are ASCII"))
            .collect();
        components.join("/")
    }));
    let entry_paths: Vec<&String> = entries.iter().map(|(path, _)| path).collect();
    assert_eq!(
        entry_paths,
        expected_paths.iter().collect::<Vec<_>>(),
        "The archive must contain index.bin, then the tiles in archive order"
    );

    let index_bytes = read_index_bytes(archive_bytes);
    let index_entries = parse_index_bin(&index_bytes).expect("the index parses");
    assert_eq!(
        index_entries.len(),
        expected_tiles.len(),
        "The index must have one entry for each tile"
    );
    for (index_entry, (path, payload_offset)) in index_entries.iter().zip(&entries[1..]) {
        assert_eq!(
            index_entry.offset(),
            *payload_offset,
            "The index offset of {path} must be where the tar reader finds its payload"
        );

        let start = usize::try_from(index_entry.offset()).expect("the offset fits in memory");
        let payload = &archive_bytes[start..start + index_entry.size() as usize];
        let tile_file = std::fs::read(tile_dir.join(path)).expect("the tile file is readable");
        assert!(
            payload == tile_file.as_slice(),
            "The payload of {path} must be the bytes of its tile file"
        );
    }
}
