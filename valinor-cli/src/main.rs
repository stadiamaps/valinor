mod commands;

use std::path::PathBuf;

use clap::{Parser, Subcommand};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Layer};

use commands::get_edge;

#[derive(Parser, Debug)]
#[command(name = "valinor-cli", author, version, about, long_about = None)]
struct Cli {
    /// Path to valhalla.json
    #[arg(env)]
    valhalla_config: PathBuf,

    /// Subcommand/tool to run
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    GetEdge(get_edge::GetEdgeArgs),
}

fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        // Standard logger, configured via the RUST_LOG env variable.
        .with(tracing_subscriber::fmt::layer().with_filter(EnvFilter::from_default_env()))
        .init();

    let cli = Cli::parse();

    match cli.command {
        Commands::GetEdge(args) => get_edge::run(&cli.valhalla_config, &args),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::CommandFactory;

    #[test]
    fn clap_derive_is_consistent() {
        Cli::command().debug_assert();
    }
}
