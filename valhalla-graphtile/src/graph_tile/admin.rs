use crate::AsCowStr;
use std::borrow::Cow;
use zerocopy::{LE, U32};
use zerocopy_derive::{FromBytes, Immutable, Unaligned};

#[derive(FromBytes, Immutable, Unaligned, Debug)]
#[repr(C)]
pub struct Admin {
    /// The offset into the graph tile text list for the country name.
    pub country_name_offset: U32<LE>,
    /// The offset into the graph tile text list for the principal subdivision name.
    pub principal_subdivision_offset: U32<LE>,
    country_iso: [u8; 2],
    principal_subdivision_iso: [u8; 3],
    // padding for alignment
    _spare: [u8; 3],
}

impl Admin {
    /// Gets the ISO 3166-1 country code
    pub fn country_iso(&self) -> Cow<'_, str> {
        self.country_iso.as_cow_str()
    }

    /// Gets the ISO 3166-2 principal subdivision code
    pub fn principal_subdivision_iso(&self) -> Cow<'_, str> {
        self.principal_subdivision_iso.as_cow_str()
    }
}

#[cfg(test)]
mod tests {
    use crate::graph_tile::{GraphTile, TEST_GRAPH_TILE_L0};

    #[test]
    fn test_parse_admin_count() {
        let tile = &*TEST_GRAPH_TILE_L0;

        assert_eq!(tile.admins().len(), tile.header().admin_count() as usize);
    }

    #[test]
    fn test_parse_admins() {
        let tile = &*TEST_GRAPH_TILE_L0;

        let country_isos = tile
            .admins()
            .iter()
            .map(|admin| admin.country_iso())
            .collect::<Vec<_>>();
        let principal_subdivision_isos = tile
            .admins()
            .iter()
            .map(|admin| admin.principal_subdivision_iso())
            .collect::<Vec<_>>();

        // insta internally does a fork operation, which is not supported under Miri
        if !cfg!(miri) {
            insta::assert_debug_snapshot!("raw_admin_snapshot", tile.admins());
            insta::assert_debug_snapshot!("country_iso", country_isos);
            insta::assert_debug_snapshot!("principal_subdivision_iso", principal_subdivision_isos);
        }
    }
}
