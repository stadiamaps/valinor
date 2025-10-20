use super::{
    AccessRestriction, Admin, DirectedEdge, DirectedEdgeExt, GraphTileError, GraphTileHandle,
    GraphTileHeader, GraphTileView, NodeInfo, NodeTransition, Sign, TransitDeparture, TransitRoute,
    TransitSchedule, TransitStop, TransitTransfer, TurnLane,
};
use crate::GraphId;
use crate::graph_tile::header::{GraphTileHeaderBuilder, VERSION_LEN};
use crate::graph_tile::predicted_speeds::COEFFICIENT_COUNT;
use chrono::{DateTime, Utc};
use geo::Coord;
use std::borrow::Cow;
use zerocopy::{I16, IntoBytes, LE, U32};

/// The writer version.
///
/// Historically this meant the version of baldr/mjolnir and was stored as a simple semver string,
/// but this is a bit fuzzy now that there are multiple writer implementations ;)
const DEFAULT_WRITER_VERSION: [u8; VERSION_LEN] = {
    const VERSION: &str = env!("CARGO_PKG_VERSION");
    const BYTES: [&[u8]; 2] = ["valinor-".as_bytes(), VERSION.as_bytes()];

    let mut out = [0u8; 16];
    let mut i = 0;
    let mut l = 0;
    while l < BYTES.len() {
        let mut c = 0;
        while c < BYTES[l].len() {
            out[i] = BYTES[l][c];
            i += 1;
            c += 1;
        }
        l += 1;
    }
    out
};

fn writer_version_to_bytes(version: &str) -> Option<[u8; 16]> {
    let bytes = version.as_bytes();
    if bytes.len() <= 16 {
        let mut out = [0u8; 16];
        out[..bytes.len()].copy_from_slice(bytes);
        Some(out)
    } else {
        None
    }
}

/// A builder for constructing new / modified graph tiles.
///
/// # Design principles
///
/// We made some conscious design choices when building this.
/// Here is a brief discussion of these and their rationale for posterity.
///
/// ## Use of copy-on-write internal fields
///
/// One of the more common usage patterns is to construct the builder
/// from an existing graph tile handle.
/// To avoid needless copying (especially when the edits are localized to a small section of the tile),
/// we lazily copy as needed.
///
/// ## Late materialization of derived structures
///
/// Things like headers are not computed every time.
/// Rather, we keep enough information around to derive what the header fields should be.
pub struct GraphTileBuilder<'a> {
    writer_version: [u8; VERSION_LEN],
    graph_id: GraphId,
    dataset_id: u64,
    sw_corner: Coord<f32>,
    create_date: DateTime<Utc>,
    remove_me_header: GraphTileHeader,
    nodes: Cow<'a, [NodeInfo]>,
    transitions: Cow<'a, [NodeTransition]>,
    directed_edges: Cow<'a, [DirectedEdge]>,
    ext_directed_edges: Cow<'a, [DirectedEdgeExt]>,
    access_restrictions: Cow<'a, [AccessRestriction]>,
    transit_departures: Cow<'a, [TransitDeparture]>,
    transit_stops: Cow<'a, [TransitStop]>,
    transit_routes: Cow<'a, [TransitRoute]>,
    transit_schedules: Cow<'a, [TransitSchedule]>,
    transit_transfers: Cow<'a, [TransitTransfer]>,
    signs: Cow<'a, [Sign]>,
    turn_lanes: Cow<'a, [TurnLane]>,
    admins: Cow<'a, [Admin]>,
    edge_bins: Cow<'a, [GraphId]>,
    complex_forward_restrictions_memory: Cow<'a, [u8]>,
    complex_reverse_restrictions_memory: Cow<'a, [u8]>,
    edge_info_memory: Cow<'a, [u8]>,
    text_memory: Cow<'a, [u8]>,
    lane_connectivity_memory: Cow<'a, [u8]>,
    predicted_speed_offsets: Cow<'a, [U32<LE>]>,
    /// Raw profile memory (n_profiles x COEFFICIENT_COUNT entries back to back)
    predicted_speed_profile_memory: Cow<'a, [I16<LE>]>,
}

impl<'a> From<&'a GraphTileHandle> for GraphTileBuilder<'a> {
    fn from(value: &'a GraphTileHandle) -> Self {
        let GraphTileView {
            header,
            nodes,
            transitions,
            directed_edges,
            ext_directed_edges,
            access_restrictions,
            transit_departures,
            transit_stops,
            transit_routes,
            transit_schedules,
            transit_transfers,
            signs,
            turn_lanes,
            admins,
            edge_bins,
            complex_forward_restrictions_memory,
            complex_reverse_restrictions_memory,
            edge_info_memory,
            text_memory,
            lane_connectivity_memory,
            predicted_speeds,
        } = value.borrow_dependent();

        let (predicted_speed_offsets, predicted_speed_profile_memory) =
            predicted_speeds.map_or(Default::default(), |ps| {
                let (offsets, profiles) = ps.as_offsets_and_profiles();
                (Cow::Borrowed(offsets), Cow::Borrowed(profiles))
            });

        GraphTileBuilder {
            writer_version: header.version,
            graph_id: header.graph_id(),
            dataset_id: header.dataset_id.get(),
            sw_corner: header.sw_corner(),
            create_date: header.create_date(),
            remove_me_header: *header,
            nodes: Cow::Borrowed(nodes),
            transitions: Cow::Borrowed(transitions),
            directed_edges: Cow::Borrowed(directed_edges),
            ext_directed_edges: Cow::Borrowed(ext_directed_edges),
            access_restrictions: Cow::Borrowed(access_restrictions),
            transit_departures: Cow::Borrowed(transit_departures),
            transit_stops: Cow::Borrowed(transit_stops),
            transit_routes: Cow::Borrowed(transit_routes),
            transit_schedules: Cow::Borrowed(transit_schedules),
            transit_transfers: Cow::Borrowed(transit_transfers),
            signs: Cow::Borrowed(signs),
            turn_lanes: Cow::Borrowed(turn_lanes),
            admins: Cow::Borrowed(admins),
            edge_bins: Cow::Borrowed(edge_bins.as_slice()),
            complex_forward_restrictions_memory: Cow::Borrowed(complex_forward_restrictions_memory),
            complex_reverse_restrictions_memory: Cow::Borrowed(complex_reverse_restrictions_memory),
            edge_info_memory: Cow::Borrowed(edge_info_memory),
            text_memory: Cow::Borrowed(text_memory),
            lane_connectivity_memory: Cow::Borrowed(lane_connectivity_memory),
            predicted_speed_offsets,
            predicted_speed_profile_memory,
        }
    }
}

impl GraphTileBuilder<'_> {
    pub fn with_version(self, version: &str) -> Result<Self, GraphTileError> {
        let writer_version = writer_version_to_bytes(version).ok_or_else(|| {
            GraphTileError::CastError(
                "Illegal version string {version}. Must be <= 16 bytes in UTF-8".to_string(),
            )
        })?;

        Ok(Self {
            writer_version,
            ..self
        })
    }

    // TODO: Can we make this generic so that it yields an iterator?
    pub fn to_bytes(&self) -> Result<Vec<u8>, GraphTileError> {
        const HEADER_SIZE: usize = size_of::<GraphTileHeader>();
        let mut body: Vec<u8> = Vec::new();

        body.extend(self.nodes.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.transitions.iter().flat_map(|value| value.as_bytes()));
        body.extend(
            self.directed_edges
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.ext_directed_edges
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.access_restrictions
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.transit_departures
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(self.transit_stops.iter().flat_map(|value| value.as_bytes()));
        body.extend(
            self.transit_routes
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.transit_schedules
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.transit_transfers
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(self.signs.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.turn_lanes.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.admins.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.edge_bins.iter().flat_map(|value| value.as_bytes()));
        body.extend(
            self.complex_forward_restrictions_memory
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.complex_reverse_restrictions_memory
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.edge_info_memory
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(self.text_memory.iter().flat_map(|value| value.as_bytes()));
        body.extend(
            self.lane_connectivity_memory
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.predicted_speed_offsets
                .iter()
                .flat_map(|value| value.as_bytes()),
        );
        body.extend(
            self.predicted_speed_profile_memory
                .iter()
                .flat_map(|value| value.as_bytes()),
        );

        let mut result = Vec::with_capacity(HEADER_SIZE + body.len());

        // TODO: Compute the header instead of slapping in the original
        let header = GraphTileHeaderBuilder {
            version: self.writer_version,
            graph_id: self.graph_id,
            density: self.remove_me_header.density(),
            has_elevation: self.remove_me_header.has_elevation(),
            has_ext_directed_edges: !self.ext_directed_edges.is_empty(),
            sw_corner: self.sw_corner,
            dataset_id: self.dataset_id,
            node_count: self.nodes.len(),
            directed_edge_count: self.directed_edges.len(),
            predicted_speed_profile_count: self.predicted_speed_profile_memory.len()
                / COEFFICIENT_COUNT,
            transition_count: self.transitions.len(),
            turn_lane_count: self.turn_lanes.len(),
            transfer_count: self.transit_transfers.len(),
            departure_count: self.transit_departures.len(),
            stop_count: self.transit_stops.len(),
            route_count: self.transit_routes.len(),
            schedule_count: self.transit_schedules.len(),
            sign_count: self.signs.len(),
            access_restriction_count: self.access_restrictions.len(),
            admin_count: self.admins.len(),
            create_date: self.create_date,
            bin_offsets: self
                .remove_me_header
                .bin_offsets
                .map(|offset| offset.into()),
            complex_forward_restrictions_size: self.complex_forward_restrictions_memory.len(),
            complex_reverse_restrictions_size: self.complex_reverse_restrictions_memory.len(),
            edge_info_size: self.edge_info_memory.len(),
            text_list_size: self.text_memory.len(),
            lane_connectivity_size: self.lane_connectivity_memory.len(),
        };
        result.extend(header.build()?.as_bytes());

        result.extend(body);

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::graph_tile::{GraphTileBuilder, GraphTileHandle, GraphTileHeader};
    use std::path::Path;
    use walkdir::WalkDir;

    fn assert_round_trip_unmodified_equals_original(path: &Path) {
        const HEADER_SIZE: usize = size_of::<GraphTileHeader>();

        let in_bytes = std::fs::read(path).expect("Unable to read file");
        let tile_handle =
            GraphTileHandle::try_from(in_bytes.clone()).expect("Unable to get tile handle");

        let builder = GraphTileBuilder::from(&tile_handle);
        let out_bytes = builder.to_bytes().expect("Unable to serialize tile");

        let in_header_slice: [u8; HEADER_SIZE] = in_bytes[0..HEADER_SIZE]
            .try_into()
            .expect("oops; couldn't parse header?");
        let in_header: GraphTileHeader = zerocopy::transmute!(in_header_slice);

        let out_header_slice: [u8; HEADER_SIZE] = out_bytes[0..HEADER_SIZE]
            .try_into()
            .expect("oops; couldn't parse header?");
        let out_header: GraphTileHeader = zerocopy::transmute!(out_header_slice);

        assert_eq!(
            in_header, out_header,
            "Failed round-trip builder test (header) for fixture at {:?}",
            path
        );

        assert_eq!(
            in_header_slice, out_header_slice,
            "Failed round-trip builder test (header; slice) for fixture at {:?}",
            path
        );

        assert_eq!(
            in_bytes, out_bytes,
            "Failed round-trip builder test (whole tile) for fixture at {:?}",
            path
        );
    }

    #[test]
    fn round_trip_from_builder_without_changes() {
        let base_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        for entry in WalkDir::new(base_dir) {
            let entry = entry.expect("Unable to traverse directory");

            if entry.file_type().is_file()
                && entry
                    .path()
                    .extension()
                    .is_some_and(|ext| ext.eq_ignore_ascii_case("gph"))
            {
                assert_round_trip_unmodified_equals_original(entry.path());

                if cfg!(miri) {
                    // Only run a single tile test under miri; it's too expensive.
                    return;
                }
            }
        }
    }

    #[test]
    fn round_trip_from_builder_without_changes_including_traffic() {
        let base_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles-with-traffic");
        for entry in WalkDir::new(base_dir) {
            let entry = entry.expect("Unable to traverse directory");

            if entry.file_type().is_file()
                && entry
                    .path()
                    .extension()
                    .is_some_and(|ext| ext.eq_ignore_ascii_case("gph"))
            {
                assert_round_trip_unmodified_equals_original(entry.path());

                if cfg!(miri) {
                    // Only run a single tile test under miri; it's too expensive.
                    return;
                }
            }
        }
    }
}