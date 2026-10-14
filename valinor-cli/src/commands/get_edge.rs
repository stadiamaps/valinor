//! The `get-edge` subcommand: pretty-prints information about a directed edge.

use std::{
    fs,
    path::{Path, PathBuf},
    str::FromStr,
};

use anyhow::{Context, anyhow};
use clap::Args;
use serde_json::Value as JsonValue;
use tracing::info;
use valhalla_graphtile::tile_provider::TrafficTileProvider;
use valhalla_graphtile::{
    GraphId,
    graph_tile::GraphTile,
    tile_provider::{DirectoryGraphTileProvider, GraphTileProvider, TarballTileProvider},
};

/// Pretty-print information about a directed edge (incl. live traffic, if available)
#[derive(Args, Debug)]
pub(crate) struct GetEdgeArgs {
    /// Graph ID (u64) or slash-form level/tile/index
    graph_id: String,
}

fn parse_graph_id(input: &str) -> anyhow::Result<GraphId> {
    // Try to parse as a pure integer.
    if let Ok(id) = input.parse::<u64>() {
        return GraphId::try_from_id(id).map_err(|e| anyhow!(e));
    }

    // Try slash-separated level/tile/index
    let parts: Vec<&str> = input.split('/').collect();
    if parts.len() == 3 {
        let level = u8::from_str(parts[0]).context("invalid level in graph id")?;
        let tile_id = u64::from_str(parts[1]).context("invalid tile id in graph id")?;
        let index = u64::from_str(parts[2]).context("invalid index in graph id")?;
        return GraphId::try_from_components(level, tile_id, index).map_err(|e| anyhow!(e));
    }

    Err(anyhow!(
        "Unrecognized graph id format. Use a u64 integer or level/tile/index"
    ))
}

#[derive(Debug, Clone)]
struct DataSources {
    routing_graph: Option<RoutingGraphDataSource>,
    traffic_extract: Option<PathBuf>,
}

#[derive(Debug, Clone)]
enum RoutingGraphDataSource {
    Tarball(PathBuf),
    TileDir(PathBuf),
}

fn parse_valhalla_data_paths(path: &Path) -> anyhow::Result<DataSources> {
    let bytes =
        fs::read(path).with_context(|| format!("Failed to read config at {}", path.display()))?;
    let json: JsonValue =
        serde_json::from_slice(&bytes).context("Invalid JSON in valhalla config")?;

    let get_path_if_exists = |key: &str| -> Option<PathBuf> {
        if let JsonValue::String(s) = &json["mjolnir"][key]
            && !s.is_empty()
            && fs::exists(s).unwrap_or_default()
        {
            Some(PathBuf::from(s))
        } else {
            None
        }
    };

    let tile_extract = get_path_if_exists("tile_extract");
    let tile_dir = get_path_if_exists("tile_dir");
    let traffic_extract = get_path_if_exists("traffic_extract");
    Ok(DataSources {
        routing_graph: match (tile_extract, tile_dir) {
            (Some(tarball), _) => Some(RoutingGraphDataSource::Tarball(tarball)),
            (_, Some(dir)) => Some(RoutingGraphDataSource::TileDir(dir)),
            (None, None) => None,
        },
        traffic_extract,
    })
}

fn pretty_print_edge_info<T: GraphTileProvider>(
    provider: &T,
    traffic_provider: Option<&TrafficTileProvider<false>>,
    gid: GraphId,
) -> anyhow::Result<()> {
    let output = provider.with_tile_containing(gid, |tile| {
        let edge = tile.get_directed_edge(gid)?;
        let edge_info = tile.get_edge_info(edge)?;
        let traffic_info = traffic_provider.map(|tp| unsafe { tp.get_speeds_for_edge(gid).ok() });

        Ok::<JsonValue, anyhow::Error>(serde_json::json!({
            "graph_id": gid,
            "directed_edge": edge,
            "edge_info": edge_info,
            "traffic": traffic_info,
        }))
    })??;
    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}

/// Runs the `get-edge` subcommand with the given Valhalla config.
pub(crate) fn run(valhalla_config: &Path, args: &GetEdgeArgs) -> anyhow::Result<()> {
    let gid = parse_graph_id(&args.graph_id)?;
    let sources = parse_valhalla_data_paths(valhalla_config)?;
    let traffic_extract = if let Some(path) = sources.traffic_extract {
        info!(path = path.to_str(), "Using traffic extract");
        Some(TrafficTileProvider::new_readonly(path)?)
    } else {
        info!("No traffic extract could be found");
        None
    };

    // Prefer tarball if set, fall back to directory.
    if let Some(graph) = sources.routing_graph {
        match graph {
            RoutingGraphDataSource::Tarball(path) => {
                info!(path = path.to_str(), "Using tarball tile extract");

                let provider = TarballTileProvider::new_readonly(&path)?;
                pretty_print_edge_info(&provider, traffic_extract.as_ref(), gid)
            }
            RoutingGraphDataSource::TileDir(path) => {
                info!(path = path.to_str(), "Using tile directory");

                let provider =
                    DirectoryGraphTileProvider::new(path, std::num::NonZeroUsize::new(1).unwrap());
                pretty_print_edge_info(&provider, traffic_extract.as_ref(), gid)
            }
        }
    } else {
        Err(anyhow!(
            "No routing graph data sources could be loaded. Expected a valid 'tile_extract' (tarball) or 'tile_dir' in the config."
        ))
    }
}
