# Valhalla Microservice Foundations

This crate provides a set of common data structures and traits
to hide all the implementation complexity of building a microservice for Valhalla.

## How Valhalla Microservices Work

If you've only ever run `valhalla_service`, you might not realize that Valhalla is actually a collection of microservices!
While the most Valhalla users just use `valhalla_service` (which creates all the microservices in a single process),
you can also run each microservice individually.
The original reason for this was to enable independent service scalability,
but it also provides an extension point which allows for alternate implementations of specific services.
Pretty clever design!

All communication happens via ZeroMQ.
Messages are passed in Protobuf format using a standard schema (see the [valhalla-proto crate](../valhalla-proto)).
The classic `valhalla_service` is a single process running all the services,
but it doesn't have to be this way.
In fact, all the communication happens over ZeroMQ,
so you can run each service in a separate process,
or even on a different machine.

On top of ZeroMQ as the base layer,
Valhalla uses [`prime_server`](https://github.com/kevinkreiser/prime_server)
to define "workers" (the service's processing loop),
and handle the work distribution.

The services are effectively chained together via these sockets,
passing along multi-part ZMQ messages with a header and a protobuf payload.
These get updated as the message is processed,
and the final response is sent back to the client.

## Crate Design Choices

- We do not wrap the underlying C++ libraries; everything is implemented in Rust
- We're using the pure Rust implementation of ZeroMQ, even though it's experimental
  (this really just means it doesn't have feature parity, not that it is unsafe to use)
- We use [tracing](https://github.com/tokio-rs/tracing), and (for binaries) enable configuration with [`RUST_LOG`](https://docs.rs/env_logger/latest/env_logger/#enabling-logging)