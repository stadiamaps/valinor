mod commands;

use clap::{Parser, Subcommand};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Layer};

use commands::{extract, get_edge};

#[derive(Parser, Debug)]
#[command(name = "valinor-cli", author, version, about, long_about = None)]
struct Cli {
    /// Subcommand/tool to run
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    GetEdge(get_edge::GetEdgeArgs),
    Extract(extract::ExtractArgs),
}

fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        // Standard logger, configured via the RUST_LOG env variable.
        .with(tracing_subscriber::fmt::layer().with_filter(EnvFilter::from_default_env()))
        .init();

    let cli = Cli::parse();

    match cli.command {
        Commands::GetEdge(args) => get_edge::run(&args),
        Commands::Extract(args) => extract::run(&args),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::CommandFactory;
    use valhalla_graphtile::GraphId;

    fn tile(level: u8, tile_index: u64) -> GraphId {
        GraphId::try_from_components(level, tile_index, 0).expect("valid tile ID in test")
    }

    #[test]
    fn clap_derive_is_consistent() {
        Cli::command().debug_assert();
    }

    #[test]
    fn extract_tiles_accept_repeated_and_comma_separated_options() {
        let cli = Cli::try_parse_from([
            "valinor-cli",
            "extract",
            "in.tar",
            "out.tar",
            "--tile",
            "0/3015,1/47701",
            "--tile",
            "2/763926",
        ])
        .expect("the arguments parse");
        let Commands::Extract(args) = cli.command else {
            panic!("expected the extract subcommand");
        };
        assert_eq!(
            args.tiles,
            vec![tile(0, 3015), tile(1, 47_701), tile(2, 763_926)]
        );
    }

    #[test]
    fn extract_tiles_are_required() {
        assert!(Cli::try_parse_from(["valinor-cli", "extract", "in.tar", "out.tar"]).is_err());
    }
}
