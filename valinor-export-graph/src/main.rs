use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use std::borrow::Cow;
use std::fs::File;
use std::io::BufWriter;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::time::Duration;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Layer};
use valhalla_graphtile::graph_tile::{DirectedEdge, GraphTile, GraphTileView};
use valhalla_graphtile::tile_hierarchy::STANDARD_LEVELS;
use valhalla_graphtile::tile_provider::{
    DirectoryGraphTileProvider, GraphTileProvider, GraphTileProviderError,
};
use valhalla_graphtile::{GraphId, RoadUse};

static PROGRESS_STYLE: OnceLock<ProgressStyle> = OnceLock::new();

mod writer;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Path to the Valhalla graph tiles.
    ///
    /// This currently expects a tile folder,
    /// but tarball support will be added eventually.
    #[arg(env)]
    tile_path: PathBuf,

    /// Path to the output FlatGeobuf (will be overwritten if it exists).
    #[arg(env)]
    output_file: PathBuf,

    /// Disables progress output.
    #[arg(env, long)]
    no_progress: bool,

    /// Skips transit features.
    ///
    /// I don't think these are even correctly handled anyway.
    #[arg(env, long, default_value = "true")]
    skip_transit: bool,

    /// Skips ferries.
    #[arg(env, long)]
    skip_ferries: bool,

    /// Skips roads with no name.
    #[arg(env, long)]
    skip_unnamed: bool,

    /// Write tippecanoe properties which will improve the PMTiles output.
    ///
    /// This is only needed if you plan to export to PMTiles later.
    #[arg(env, long)]
    write_tippecanoe_properties: bool,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let tile_path = cli.tile_path.clone();
    let reader = DirectoryGraphTileProvider::new(tile_path.clone(), NonZeroUsize::new(25).unwrap());

    let should_skip_edge = |edge: &DirectedEdge, names: &Vec<Cow<str>>| {
        (cli.skip_transit && edge.is_transit_line())
            || (cli.skip_ferries && edge.road_use() == RoadUse::Ferry)
            || (cli.skip_unnamed && names.is_empty())
    };

    if !cli.no_progress {
        _ = PROGRESS_STYLE.set(
            ProgressStyle::with_template(
                "[{elapsed}] {bar:40.cyan/blue} {msg} {percent}% ETA {eta}",
            )?
            .progress_chars("##-"),
        );
    }

    tracing_subscriber::registry()
        // Standard logger, configured via the RUST_LOG env variable
        .with(tracing_subscriber::fmt::layer().with_filter(EnvFilter::from_default_env()))
        .init();

    // TODO: Almost all code below feels like it can be abstracted into a graph traversal helper...
    // We could even make processing plugins with WASM LOL

    // Enumerate edges in available tiles
    let mut tile_set = Vec::new();
    let mut edge_count: usize = 0;
    for level in &*STANDARD_LEVELS {
        // For each tile in that level...
        let n_tiles = level.tiling_system.n_rows * level.tiling_system.n_cols;

        let progress_bar = PROGRESS_STYLE.get().map(|style| {
            let bar = ProgressBar::new(u64::from(n_tiles));
            bar.set_message(format!("Scanning tiles in level {}...", level.level));
            bar.set_style(style.clone());
            bar
        });

        for tile_id in 0..n_tiles {
            progress_bar.as_ref().inspect(|bar| bar.inc(1));
            // Get the index pointer for each tile in the level
            let graph_id = GraphId::try_from_components(level.level, u64::from(tile_id), 0)?;
            match reader.get_handle_for_tile_containing(graph_id) {
                Ok(tile) => {
                    tile_set.push(graph_id);
                    let tile_edge_count = tile.header().directed_edge_count() as usize;
                    edge_count += tile_edge_count;
                }
                Err(GraphTileProviderError::TileDoesNotExist) => {
                    // Ignore; not all tiles will exist for extracts
                }
                Err(e) => return Err(e.into()),
            }
        }

        progress_bar.inspect(ProgressBar::finish);
    }

    // Drop mutability
    let tile_set = tile_set;
    let progress_bar = PROGRESS_STYLE.get().map(|style| {
        let bar = ProgressBar::new(edge_count as u64);
        bar.set_message(format!(
            "Exporting {edge_count} edges in {} tiles...",
            tile_set.len()
        ));
        bar.set_style(style.clone());
        bar
    });

    // Create the FGB writer
    let current_file = File::create(cli.output_file)?;
    let buf = BufWriter::new(current_file);
    let mut writer = writer::StreamingEdgeWriter::new("roads")?;

    // Iterate over the tiles and export edges
    for tile_id in &tile_set {
        reader.with_tile_containing(*tile_id, |tile| {
            // TODO: Anything we need to do for nodes? Not for most, but maybe things like bollards??
            export_edges_for_tile(
                &mut writer,
                tile,
                *tile_id,
                &progress_bar,
                &should_skip_edge,
                cli.write_tippecanoe_properties,
            )
        })??;
    }

    progress_bar.inspect(ProgressBar::finish);

    let progress_bar = PROGRESS_STYLE.get().map(|_| {
        let bar = ProgressBar::new_spinner();
        bar.set_message("Finalizing FlatGeobuf...");
        bar.enable_steady_tick(Duration::from_millis(100));
        bar
    });

    writer.finalize(buf)?;

    progress_bar.inspect(ProgressBar::finish);

    Ok(())
}

fn export_edges_for_tile(
    writer: &mut writer::StreamingEdgeWriter,
    tile: &GraphTileView,
    tile_id: GraphId,
    progress_bar: &Option<ProgressBar>,
    should_skip_edge: &impl Fn(&DirectedEdge, &Vec<Cow<str>>) -> bool,
    write_tippecanoe_properties: bool,
) -> anyhow::Result<()> {
    for index in 0..tile.header().directed_edge_count() as usize {
        // Get the edge
        let edge_id = tile_id.with_feature_index(index as u64)?;
        let edge = tile.get_directed_edge(edge_id)?;

        progress_bar.as_ref().inspect(|bar| bar.inc(1));

        // Skip certain edge types based on the config
        let edge_info = tile.get_edge_info(edge)?;
        let names = edge_info.get_names();
        if should_skip_edge(edge, &names) {
            continue;
        }

        writer.write_feature(edge_id, edge, &edge_info, write_tippecanoe_properties)?;
    }

    Ok(())
}
