use super::{AccessRestriction, Admin, DirectedEdge, DirectedEdgeExt, GraphTileHandle, GraphTileHeader, GraphTileView, NodeInfo, NodeTransition, Sign, TransitDeparture, TransitRoute, TransitSchedule, TransitStop, TransitTransfer, TurnLane};
use crate::GraphId;
use std::borrow::Cow;
use zerocopy::{IntoBytes, I16, LE, U32};

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
    graph_id: GraphId,
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
    predicted_speed_profiles: Cow<'a, [I16<LE>]>,
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

        let (predicted_speed_offsets, predicted_speed_profiles) =
            predicted_speeds.map_or(Default::default(), |ps| {
                let (offsets, profiles) = ps.as_offsets_and_profiles();
                (Cow::Borrowed(offsets), Cow::Borrowed(profiles))
            });

        GraphTileBuilder {
            graph_id: header.graph_id(),
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
            predicted_speed_profiles,
        }
    }
}

impl GraphTileBuilder<'_> {
    pub fn to_bytes(&self) -> Vec<u8> {
        const HEADER_SIZE: usize = size_of::<GraphTileHeader>();
        let mut body: Vec<u8> = Vec::new();

        body.extend(self.nodes.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.transitions.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.directed_edges.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.ext_directed_edges.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.access_restrictions.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.transit_departures.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.transit_stops.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.transit_routes.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.transit_schedules.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.transit_transfers.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.signs.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.turn_lanes.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.admins.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.edge_bins.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.complex_forward_restrictions_memory.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.complex_reverse_restrictions_memory.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.edge_info_memory.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.text_memory.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.lane_connectivity_memory.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.predicted_speed_offsets.iter().flat_map(|value| value.as_bytes()));
        body.extend(self.predicted_speed_profiles.iter().flat_map(|value| value.as_bytes()));

        let mut result = Vec::with_capacity(HEADER_SIZE + body.len());

        // TODO: Compute the header instead of slapping in the original
        result.extend(self.remove_me_header.as_bytes());

        result.extend(body);

        result
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use walkdir::WalkDir;
    use crate::graph_tile::{GraphTileBuilder, GraphTileHandle};

    fn assert_round_trip_unmodified_equals_original(path: &Path) {
        let in_bytes = std::fs::read(path).expect("Unable to read file");
        let tile_handle = GraphTileHandle::try_from(in_bytes.clone()).expect("Unable to get tile handle");

        let builder = GraphTileBuilder::from(&tile_handle);
        let out_bytes = builder.to_bytes();

        assert_eq!(in_bytes, out_bytes, "Failed round-trip builder test for fixture at {:?}", path);
    }

    #[test]
    fn round_trip_from_builder_without_changes() {
        let base_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join("andorra-tiles");
        for entry in WalkDir::new(base_dir) {
            let entry = entry.expect("Unable to traverse directory");

            if entry.file_type().is_file() && entry.path().extension().is_some_and(|ext| ext.eq_ignore_ascii_case("gph")) {
                assert_round_trip_unmodified_equals_original(entry.path())
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

            if entry.file_type().is_file() && entry.path().extension().is_some_and(|ext| ext.eq_ignore_ascii_case("gph")) {
                assert_round_trip_unmodified_equals_original(entry.path())
            }
        }
    }
}