use crate::models::{EdgePointer, EdgeRecord};
use bit_set::BitSet;
use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use rayon::prelude::*;
use std::borrow::Cow;
use std::collections::HashMap;
use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, OnceLock};
use tracing::warn;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Layer};
use valhalla_graphtile::graph_tile::{DirectedEdge, GraphTile, LookupError, OwnedGraphTileHandle};
use valhalla_graphtile::tile_hierarchy::STANDARD_LEVELS;
use valhalla_graphtile::tile_provider::{
    DirectoryGraphTileProvider, GraphTileProvider, GraphTileProviderError,
};
use valhalla_graphtile::{GraphId, RoadUse};
use zstd::Encoder;

static PROGRESS_STYLE: OnceLock<ProgressStyle> = OnceLock::new();

// mod helpers;
mod models;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Path to the Valhalla graph tiles.
    ///
    /// This currently expects a tile folder,
    /// but tarball support will be added eventually.
    #[arg(env)]
    tile_path: PathBuf,

    /// Path to the output directory where files will be created.
    /// The special value - will write all data to stdout.
    ///
    /// These will be newline-delimited GeoJSON,
    /// and any existing files will be overwritten.
    /// The directory will be created if necessary.
    /// NB: Any existing files will be left intact.
    #[arg(env)]
    output_dir: PathBuf,

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

    /// Disable zstd compression of output. The file extension will be .geojson  instead of .geojson.zst.
    #[arg(env, long, default_value_t = false)]
    no_compression: bool,
}

impl Cli {
    fn write_to_stdout(&self) -> bool {
        self.output_dir == PathBuf::from("-")
    }
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let tile_path = cli.tile_path.clone();
    let reader = DirectoryGraphTileProvider::new(tile_path.clone(), NonZeroUsize::new(25).unwrap());

    let write_to_stdout = cli.write_to_stdout();

    let should_skip_edge = |edge: &DirectedEdge, names: &Vec<Cow<str>>| {
        // TODO: Actually, visualizing the shortcuts as a separate layer COULD be quite interesting!
        (cli.skip_transit && edge.is_transit_line())
            || edge.is_shortcut()
            || (cli.skip_ferries && edge.edge_use() == RoadUse::Ferry)
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
    let mut tile_set = HashMap::new();
    let mut edge_count: usize = 0;
    for level in &*STANDARD_LEVELS {
        // For each tile in that level...
        let n_tiles = level.tiling_system.n_rows * level.tiling_system.n_cols;

        let progress_bar = PROGRESS_STYLE.get().map(|style| {
            let bar = ProgressBar::new(u64::from(n_tiles));
            bar.set_message(format!(
                "Scanning {n_tiles} tiles in level {}...",
                level.level
            ));
            bar.set_style(style.clone());
            bar
        });

        for tile_id in 0..n_tiles {
            progress_bar.as_ref().inspect(|bar| bar.inc(1));
            // Get the index pointer for each tile in the level
            let graph_id = GraphId::try_from_components(level.level, u64::from(tile_id), 0)?;
            // We use a thread local executor for simplicity here rather than full tokio.
            // This is essentially a synchronous program
            // built on rayon for CPU parallelism.
            // There should not be much waiting for file I/O,
            // and all the blocking is naturally fine as these are on a thread pool.
            match futures::executor::block_on(reader.get_tile_containing(graph_id)) {
                Ok(tile) => {
                    let tile_edge_count = tile.header().directed_edge_count() as usize;
                    tile_set.insert(graph_id, edge_count);
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

    // An efficient way of tracking whether we've seen an edge before
    // FIXME: Only works on 64-bit (or higher?) platforms
    // TODO: Does this crate actually work for 64-bit values? I also have some doubts about efficiency.
    // TODO: Should we ever export nodes too in certain cases? Ex: a bollard on an otherwise driveable road?
    let processed_edges = Mutex::new(BitSet::with_capacity(edge_count));

    let progress_bar = PROGRESS_STYLE.get().map(|style| {
        let bar = ProgressBar::new(edge_count as u64);
        bar.set_message(format!(
            "Exporting {edge_count} edges in {} tiles...",
            tile_set.len()
        ));
        bar.set_style(style.clone());
        bar
    });

    if !write_to_stdout {
        // Create directories as needed
        std::fs::create_dir_all(cli.output_dir.clone())?;
    }

    let out_dir = cli.output_dir.clone();

    // Iterate over the tiles and export edges
    tile_set
        .par_iter()
        .try_for_each(|(tile_id, edge_index_offset)| {
            // NOTE: We can't share readers across threads (at least for now)
            let reader =
                DirectoryGraphTileProvider::new(tile_path.clone(), NonZeroUsize::new(25).unwrap());

            let tile = futures::executor::block_on(reader.get_tile_containing(*tile_id))?;

            // Create a base writer to either stdout or a file with appropriate extension
            let base: Box<dyn Write> = if write_to_stdout {
                Box::new(io::stdout())
            } else {
                let ext = if cli.no_compression {
                    "geojson"
                } else {
                    "geojson.zst"
                };
                let path = out_dir.join(tile.graph_id().file_path(ext)?);
                let parent = path.parent().expect("Unexpected path structure");
                // Create the output directory
                std::fs::create_dir_all(parent)?;
                Box::new(File::create(path)?)
            };

            // Wrap base in a buffered writer, then optionally zstd
            if cli.no_compression {
                let writer = BufWriter::new(base);
                export_edges_for_tile(
                    writer,
                    tile,
                    *tile_id,
                    *edge_index_offset,
                    &reader,
                    &tile_set,
                    &processed_edges,
                    &progress_bar,
                    &should_skip_edge,
                )?
            } else {
                // NB: level=0 is the zstd default.
                let writer = Encoder::new(BufWriter::new(base), 0)?.auto_finish();
                export_edges_for_tile(
                    writer,
                    tile,
                    *tile_id,
                    *edge_index_offset,
                    &reader,
                    &tile_set,
                    &processed_edges,
                    &progress_bar,
                    &should_skip_edge,
                )?
            }

            Ok::<_, anyhow::Error>(())
        })?;

    // TODO: Anything we need to do for nodes? Not for most, but maybe things like bollards??

    progress_bar.inspect(ProgressBar::finish);

    Ok(())
}

fn export_edges_for_tile<W: Write>(
    mut writer: W,
    tile: Arc<OwnedGraphTileHandle>,
    tile_id: GraphId,
    edge_index_offset: usize,
    reader: &DirectoryGraphTileProvider,
    tile_set: &HashMap<GraphId, usize>,
    processed_edges: &Mutex<BitSet>,
    progress_bar: &Option<ProgressBar>,
    should_skip_edge: &impl Fn(&DirectedEdge, &Vec<Cow<str>>) -> bool,
) -> anyhow::Result<()> {
    for index in 0..tile.header().directed_edge_count() as usize {
        let mut pe = processed_edges.lock().unwrap();
        if pe.contains(edge_index_offset + index) {
            // Skip edges we've already processed
            continue;
        }

        // TODO: Some TODO about transition edges in the original source

        // Get the edge
        let edge_id = tile_id.with_index(index as u64)?;
        let edge = tile.get_directed_edge(edge_id)?;

        // TODO: Mark the edge as seen (maybe? Weird TODO in the Valhalla source)
        pe.insert(edge_index_offset + index);

        progress_bar.as_ref().inspect(|bar| bar.inc(1));

        // Skip certain edge types based on the config
        let edge_info = tile.get_edge_info(edge)?;
        let names = edge_info.get_names();
        if should_skip_edge(edge, &names) {
            continue;
        }

        // Get the opposing edge
        let opposing_edge = match tile.get_opp_edge_index(edge_id) {
            Ok(opp_edge_id) => {
                let opp_graph_id = edge_id.with_index(opp_edge_id as u64)?;
                EdgePointer {
                    graph_id: opp_graph_id,
                    tile: tile.clone(),
                }
            }
            Err(LookupError::InvalidIndex) => {
                return Err(LookupError::InvalidIndex)?;
            }
            Err(LookupError::MismatchedBase) => {
                let (opp_graph_id, tile) =
                    futures::executor::block_on(reader.get_opposing_edge(edge_id))?;
                EdgePointer {
                    graph_id: opp_graph_id,
                    tile,
                }
            }
        };
        progress_bar.as_ref().inspect(|bar| bar.inc(1));
        if let Some(offset) = tile_set.get(&opposing_edge.graph_id.tile_base_id()) {
            pe.insert(offset + opposing_edge.graph_id.index() as usize);
        } else {
            // This happens in extracts, but shouldn't for the planet...
            warn!(
                "Missing opposite edge {} in tile set",
                opposing_edge.graph_id
            );
        }

        drop(pe); // Release the lock

        // Keep some state about this section of road?
        // let mut edges: Vec<EdgePointer> = vec![EdgePointer {
        //     graph_id: edge_id,
        //     tile: tile.clone(),
        // }];

        // TODO: Traverse forward and backward from the edge as an optimization to coalesce segments with no change?
        // This should be an opt-in behavior for visualization of similar roads,
        // but note that it then no longer becomes 1:1
        // Could also be useful for MLT representation?

        // TODO: Visualize the dead ends? End node in another layer at the end of edges that don't connect?

        // TODO: Coalesce with opposing edge.
        // Seems like we may be able to do something like this:
        //   - Find which edge is "forward"
        //   - Omit forward field
        //   - Check if any difference in edge + opp edge tagging; I'd expect reversed access; anything else? Can test this...
        let record = EdgeRecord::new(&STANDARD_LEVELS[tile_id.level() as usize], edge, edge_info)?;
        serde_json::to_writer(&mut writer, &record)?;
        writer.write(&['\n' as u8])?;
    }

    Ok(())
}
