use geo::LineString;
use serde::Serialize;
use std::sync::Arc;
use valhalla_graphtile::graph_tile::{DirectedEdge, EdgeInfo, GraphTile, OwnedGraphTileHandle};
use valhalla_graphtile::tile_hierarchy::TileLevel;
use valhalla_graphtile::{GraphId, RoadClass};

// TODO: Do we need this?
pub struct EdgePointer {
    pub graph_id: GraphId,
    pub tile: Arc<OwnedGraphTileHandle>,
}

impl EdgePointer {
    pub(crate) fn edge(&self) -> &DirectedEdge {
        self.tile
            .get_directed_edge(self.graph_id)
            .expect("That wasn't supposed to happen...")
    }
}

#[derive(Serialize)]
struct Tippecanoe {
    layer: &'static str,
    #[serde(rename = "minzoom")]
    min_zoom: u8,
}

impl From<(&TileLevel, RoadClass)> for Tippecanoe {
    fn from((level, road_class): (&TileLevel, RoadClass)) -> Self {
        Self {
            layer: level.name,
            min_zoom: std::cmp::min(
                12,
                level.tiling_system.min_zoom()
                    + match &level.minimum_road_class.discriminant() - road_class.discriminant() {
                        0 => 2,
                        1 => 1,
                        2.. => 0,
                    },
            ),
        }
    }
}

#[derive(Serialize)]
struct Geometry {
    #[serde(rename = "type")]
    geometry_type: &'static str,
    coordinates: Vec<[f32; 2]>,
}

impl From<&LineString> for Geometry {
    fn from(value: &LineString) -> Self {
        Self {
            geometry_type: "LineString",
            // TODO: Truncate to 6 digits
            coordinates: value
                .coords()
                .map(|coord| [coord.x as f32, coord.y as f32])
                .collect(),
        }
    }
}

#[derive(Serialize)]
struct EdgeProperties<'a> {
    #[serde(flatten)]
    edge: &'a DirectedEdge,
    #[serde(flatten)]
    edge_info: EdgeInfo<'a>,
}

impl EdgeProperties<'_> {
    fn new<'a>(edge: &'a DirectedEdge, edge_info: EdgeInfo<'a>) -> EdgeProperties<'a> {
        EdgeProperties { edge, edge_info }
    }
}

#[derive(Serialize)]
pub struct EdgeRecord<'a> {
    // TODO: Figure out how to make this a default?
    #[serde(rename = "type")]
    record_type: &'static str,
    tippecanoe: Tippecanoe,
    geometry: Geometry,
    properties: EdgeProperties<'a>,
}

impl EdgeRecord<'_> {
    pub fn new<'a>(
        tile_level: &TileLevel,
        edge: &'a DirectedEdge,
        edge_info: EdgeInfo<'a>,
    ) -> Result<EdgeRecord<'a>, anyhow::Error> {
        Ok(EdgeRecord {
            record_type: "Feature",
            tippecanoe: Tippecanoe::from((tile_level, edge.classification())),
            geometry: Geometry::from(edge_info.shape()?),
            properties: EdgeProperties::new(edge, edge_info),
        })
    }
}
