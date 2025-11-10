#![doc = include_str!("../README.md")]

use clap::Parser;
use http::StatusCode;
use serde_json::json;
use tracing::{error, info};
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Layer};
use valhalla_microservice::{Error, ValhallaMicroserviceBuilder, WorkerResult};
use valhalla_proto::Api;
use valhalla_proto::options::Action;

mod handlers;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// The upstream socket to listen on.
    #[arg(env, long, default_value = "ipc:///tmp/odin_out")]
    upstream_socket_endpoint: String,

    /// The Valhalla loopback socket endpoint.
    #[arg(env, long, default_value = "ipc:///tmp/loopback")]
    loopback_socket_endpoint: String,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let upstream_socket_endpoint = &cli.upstream_socket_endpoint;
    let loopback_socket_endpoint = &cli.loopback_socket_endpoint;

    tracing_subscriber::registry()
        // Standard logger, configured via the RUST_LOG env variable
        .with(tracing_subscriber::fmt::layer().with_filter(EnvFilter::from_default_env()))
        // TODO: We should probably optionally add Sentry here (behind a feature flag).
        .init();

    let service_builder =
        ValhallaMicroserviceBuilder::new(upstream_socket_endpoint, loopback_socket_endpoint);
    let mut service = service_builder.build(handle_message).await?;

    info!(
        "Ilúvatar service started (upstream = {upstream_socket_endpoint}, loopback = {loopback_socket_endpoint})"
    );

    loop {
        tokio::select! {
            _ = tokio::signal::ctrl_c() => {
                info!("Ctrl-C received; shutting down...");
                return Ok(());
            }
            message = service.tick() => match message {
                Ok(()) => {
                    // All good; carry on...
                }
                Err(Error::UpstreamShuttingDown) => {
                    // Graceful shutdown path.
                    info!("Upstream shutting down...");
                    return Ok(());
                }
                Err(Error::InvalidMessage(e)) => {
                    error!("{e}");
                }
                Err(Error::ZeroMq(e)) => {
                    error!("{e}");
                }
            }
        }
    }
}

fn handle_message(req: Api) -> WorkerResult {
    let Some(options) = &req.options else {
        return WorkerResult::json(
            StatusCode::INTERNAL_SERVER_ERROR,
            json!({
                "message": "This request doesn't seem to have any options attached. This is either a bug in Valhalla or our understanding of the protocol invariants. Please open an issue on GitHub!"
            }),
        );
    };

    match Action::try_from(options.action) {
        Ok(Action::Status) => handlers::status::status(req),
        Ok(_) => {
            // Valhalla literally has a switch fallthrough here, but I'm not sure that's wise...
            unimplemented!("TODO: Narrative builder!");
        }
        Err(_) => WorkerResult::json(
            StatusCode::INTERNAL_SERVER_ERROR,
            json!({
                "message": "This request uses an unknown action variant! This means that we're out of sync with Valhalla's protobuf message definitions. Please open an issue on GitHub!"
            }),
        ),
    }
}
