#![doc = include_str!("../README.md")]

use crate::http_protocol::HttpRequestInfo;
use tracing::trace;
use valhalla_proto::Api;
use zerocopy::{IntoBytes, transmute};
use zeromq::{DealerSocket, PushSocket, ZmqMessage, ZmqResult, prelude::*};

mod error;
pub mod http_protocol;
mod result;

pub use error::Error;
pub use result::WorkerResult;
use valhalla_proto::prost::Message;

/// A Valhalla-compatible microservice.
pub struct ValhallaMicroservice<F: Fn(Api) -> WorkerResult> {
    /// The ZMQ socket upstream from this service.
    ///
    /// The service connects to this to listen for messages from upstream services.
    /// For example, in Valhalla, `odin` (narrative generation)
    /// receives messages from `thor` (path finding).
    ///
    /// In the standard Valhalla configuration,
    /// this is typically named `<this service>_out` (e.g., `thor_out`),
    /// which can be a bit confusing.
    upstream: DealerSocket,
    /// The ZMQ socket downstream from this service.
    ///
    /// The service uses this to push messages to downstream services.
    /// For example, in Valhalla, `thor` (path finding)
    /// pushes messages to `odin` (narrative generation).
    ///
    /// In the standard Valhalla configuration,
    /// this is typically named `<downstream service>_in` (e.g., `odin_in`),
    /// which can be a bit confusing.
    downstream: Option<DealerSocket>,
    // TODO: Interrupt socket
    /// The loopback zmq socket.
    ///
    /// This is used to deliver the final HTTP response,
    /// if this service is capable of generating it (rather than passing it downstream).
    loopback: PushSocket,
    /// The worker function to be invoked for each upstream message.
    worker_fn: F,
}

impl<F: Fn(Api) -> WorkerResult> ValhallaMicroservice<F> {
    /// Advertises our presence to the upstream service, indicating we are ready for the next message.
    async fn advertise(&mut self) -> ZmqResult<()> {
        self.upstream.send(ZmqMessage::from("")).await
    }

    /// Run one iteration of the main "loop" for this service.
    ///
    /// This takes care of advertising presence,
    /// waiting for work from upstream,
    /// executing [`self.worker_fn`],
    /// and publishing the result where appropriate.
    ///
    /// # Errors
    ///
    /// This can go wrong at several points.
    /// [`Error::UpstreamShuttingDown`] indicates that the upstream has sent a shutdown message,
    /// and no further requests will be sent.
    /// At this point, the most reasonable action for the caller is to gracefully exit as well.
    ///
    /// ZeroMQ errors describe the failure modes that are specific to ZeroMQ.
    /// Notably, these *may* not be as serious as the initial connection errors
    /// (in which case the service can't be started).
    /// Whether to continue is left up to the caller.
    ///
    /// [`Error::InvalidMessage`] indicates unexpected data.
    /// Callers should take note of this, but this isn't necessarily cause to terminate the service.
    /// It probably does indicate a programming error on either side,
    /// but since Valhalla uses multi-part (multi-frame) messages,
    /// and ZMQ guarantees "all or none" delivery,
    /// it is safe to continue.
    pub async fn tick(&mut self) -> Result<(), Error> {
        const HTTP_REQ_INFO_SIZE: usize = size_of::<HttpRequestInfo>();

        // Announce that we are ready for the next message.
        // FIXME: The way that Valhalla (prime_server??) implements this, a "dead" process will never be detected.
        // The messaging system will not give it any more work, but it WILL cause a request to get lost in limbo.
        self.advertise().await?;

        //
        // Receive and decode the message
        //

        // TODO: Set up a monitor instead so we've got a channel (stream)!
        // let mut monitor = self.upstream.monitor();
        let message = self.upstream.recv().await?;
        let mut frames = message.into_vecdeque(); // Zero cost unwrap

        // Sanity checks
        if frames.len() != 2 {
            return Err(Error::InvalidMessage(format!(
                "Expected a multipart message with two frames (a header struct and an Api protobuf); got {} frames instead",
                frames.len()
            )));
        }

        // Unpack the data frames. This is infallible because we checked the length above.
        let http_req_info_data = frames.pop_front().unwrap();
        let protobuf_data = frames.pop_front().unwrap();
        drop(frames);

        if http_req_info_data.len() != HTTP_REQ_INFO_SIZE {
            return Err(Error::InvalidMessage(format!(
                "Expected HTTP request info structure of length {HTTP_REQ_INFO_SIZE}; received {}",
                http_req_info_data.len()
            )));
        }

        // The HTTP request info is a fixed-size struct which we can safely transmute after the size check above.
        let slice: [u8; HTTP_REQ_INFO_SIZE] = http_req_info_data[0..HTTP_REQ_INFO_SIZE]
            .try_into()
            .unwrap(); // Infallible due to the size check above.
        let mut req_info: HttpRequestInfo = transmute!(slice);

        trace!("Handling request ID {}", req_info.id());

        // Decode the protobuf frame.
        let request = Api::decode(protobuf_data.as_ref())
            .map_err(|e| Error::InvalidMessage(format!("Failed to decode protobuf frame: {e}")))?;

        //
        // Handle the request
        //

        match (self.worker_fn)(request) {
            WorkerResult::HttpResponse {
                status_code,
                headers,
                body,
            } => {
                // Update the response code.
                req_info.set_response_code(status_code.as_u16());
                let mut message = ZmqMessage::from(req_info.as_bytes().to_vec());

                let http_response = result::serialize_http(req_info, status_code, headers, body);
                message.push_back(http_response.into());

                self.loopback.send(message).await?;
            }
            WorkerResult::PlaceholderDownstreamTBD => todo!("Placeholder"),
        }

        Ok(())
    }
}

pub struct ValhallaMicroserviceBuilder<'a> {
    upstream_socket_endpoint: &'a str,
    downstream_socket_endpoint: Option<&'a str>,
    loopback_socket_endpoint: &'a str,
}

impl<'a> ValhallaMicroserviceBuilder<'a> {
    /// Initializes a Valhalla microservice builder.
    ///
    /// The required socket endpoints are typically IPC sockets like `ipc:///tmp/odin_out`
    /// and `ipc:///tmp/loopback`.
    pub fn new(
        upstream_socket_endpoint: &'a str,
        loopback_socket_endpoint: &'a str,
    ) -> ValhallaMicroserviceBuilder<'a> {
        ValhallaMicroserviceBuilder {
            upstream_socket_endpoint,
            downstream_socket_endpoint: None,
            loopback_socket_endpoint,
        }
    }

    /// Adds a downstream endpoint.
    ///
    /// Terminal (last in the chain) services never need this,
    /// but others do.
    #[must_use]
    pub fn with_downstream_socket_endpoint(
        self,
        downstream_socket_endpoint: &'a str,
    ) -> ValhallaMicroserviceBuilder<'a> {
        ValhallaMicroserviceBuilder {
            downstream_socket_endpoint: Some(downstream_socket_endpoint),
            ..self
        }
    }

    /// Tries to build the service.
    ///
    /// # Rules for worker functions
    ///
    /// - Don't panic; neither this crate nor Valhalla have well-defined behavior for this failure mode.
    /// - The usual Tokio rules for async contexts. If you're going to be working for a while, spawn a blocking thread, use a pool, channels, etc. rather than blocking.
    ///
    /// # Errors
    ///
    /// This may fail if we are unable to configure the ZeroMQ sockets as requested.
    pub async fn build<F: Fn(Api) -> WorkerResult>(
        self,
        worker_fn: F,
    ) -> ZmqResult<ValhallaMicroservice<F>> {
        let mut upstream = DealerSocket::new();
        upstream.connect(self.upstream_socket_endpoint).await?;

        let downstream = if let Some(downstream_socket_endpoint) = self.downstream_socket_endpoint {
            let mut sock = DealerSocket::new();
            sock.connect(downstream_socket_endpoint).await?;
            Some(sock)
        } else {
            None
        };

        let mut loopback = PushSocket::new();
        loopback.connect(self.loopback_socket_endpoint).await?;

        Ok(ValhallaMicroservice {
            upstream,
            downstream,
            loopback,
            worker_fn,
        })
    }
}
