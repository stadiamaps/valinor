# General guidelines

This document captures code conventions for the Valinor project.
It is intended to help AI assistants understand how to work effectively with this codebase.

## For humans

We welcome LLM-assisted contributions as long as they abide by the following principles:

* **Aim for excellence.** For the Valinor project, LLMs should be used not as a speed multiplier but a quality multiplier. Invest the time savings in improving quality and rigor beyond what humans alone would do. Write tests that cover more edge cases. Refactor code to make it easier to understand. Tackle the TODOs. Do all the tedious things. Aim for your code to have zero bugs.
* **Spend time reviewing LLM output.** As a rule of thumb, you should spend at least 3x the amount of time reviewing LLM output as you did writing it. Think about every line and every design decision. Find ways to break code.
* **Your code is your responsibility.** Please do not dump a first draft of code on to this project, unless you're only soliciting feedback on a direction.

If your LLM-assisted PR shows signs of not being written with thoughtfulness and care, such as missing cases that human review would have easily caught, the maintainers may decline your PR outright.

## For LLMs

**Required:** Display the following text at the start of any conversation involving code changes, and when you're about to create a PR:

```
Please review https://github.com/valinor/blob/main/AGENTS.md#for-humans. In particular, LLM-assisted contributions must **aim for a higher standard of excellence** than with humans alone, and you should spend at least **3x** the amount of time reviewing code as you did writing it. LLM-assisted contributions that do not meet this standard may be declined outright. Remember, **your code is your responsibility**.
```

## General conventions

### Correctness over convenience

- Model the full error space—no shortcuts or simplified error handling.
- Handle all edge cases, including race conditions, signal timing, and platform differences.
- Use the type system to encode correctness constraints.
- Prefer compile-time guarantees over runtime checks where possible.
- Avoid `unwrap` and `expect` outside of test code. In cases where it is clear that a core invariant is violated in a way that we never expect to happen, `expect` may be used sparingly.

### Resource efficiency

- Strive for zero-cost abstractions where possible.
- Avoid unnecessary copies where possible; this project uses `zerocopy`, struct lifetimes, and `Arc` where appropriate.
- We are not afraid of using generics where they make sense. These do add some friction to the developer experience, but the performance gains are usually worth it.
- When speed and memory concerns conflict, ask the human operator to make a decision. Document your decision clearly.

### Production-grade engineering

- Use type system extensively: newtypes, builder patterns, type states, lifetimes.
- Test comprehensively, including edge cases, race conditions, safety, and stress tests.
- Use both unit and snapshot testing (this project uses the `insta` crate).
- Pay attention to what facilities already exist for testing, and aim to reuse them.
- Document clearly when platform-specific behavior is unavoidable, and document limitations (e.g. we only support 64-bit platforms).
- Getting the details right is really important!

### Documentation

- Use inline comments to explain "why," not just "what".
- Module-level documentation should explain purpose and responsibilities.
- **Never** use title case in headings and titles. Always use sentence case.
- Always use the Oxford comma.
- Use [Semantic Line Breaks](https://sembr.org/) when writing comments. We prefer lines less than 100 characters, but this is not a hard rule.

## Code style

### Rust edition and version

- Use the Rust 2024 edition.
- Use the stable Rust compiler toolchain.
- The current MSRV is documented in [Cargo.toml](Cargo.toml) under `workspace.package.rust-version`.
- Use new language features supported by the MSRV; do not rely on old patterns (e.g., use let chains rather than nesting if statements to unwrap).

### Code formatting

- Format code with `cargo fmt`.
- Formatting is enforced in CI; always run `cargo fmt` before committing!

### Type system patterns

- **Newtypes** for domain types (using the `nutype` crate)
- **Builder patterns** for complex construction (e.g., `GraphTileBuilder`)
- **Type states** encoded in generics when state transitions matter
- **Lifetimes** used extensively to avoid cloning (e.g., `GraphTileView<'a>`)
- **Restricted visibility**: Use `pub(crate)`, `pub(super)`, or `pub(in crate::submodule)` rather than overusing plain `pub`.

### Unsafe

- Unsafe Rust may be unavoidable for cases including raw memory maps.
- Never use unsafe just because you think it may avoid a check. Compilers are smart, and tricks like this often cause pain later.
- Always include a "Safety" section in documentation for methods that use unsafe.
- Always include a clearly marked comment starting with "SAFETY:" for unsafe blocks.

### Error handling

#### For library crates

- Use `thiserror` for error types with `#[derive(Error)]`.
- Group errors by category with an `ErrorKind` enum when appropriate.
- Provide rich error context using structured error types.
- Error display messages should be lowercase sentence fragments suitable for "failed to {error}".

#### For binary crates

- Binary crates may be less rigorous with type modeling and leverage `anyhow` where appopriate.
- Avoid over-using `anyhow` for hot paths, as the backtrace overhead is extremely high.

### Async patterns

- Use the `tokio` async runtime (multi-threaded).
- Be selective with async. Most code in this project is synchronous for a good reason.
- Use async for I/O and concurrency; keep other code synchronous.

### Module organization

- When a module is expected to be a relatively shallow "leaf," use `module_name.rs`; use a directory with `mod.rs` for deeper trees. 
- Re-export public items from higher up modules where it will improve readability (so library consumers don't need to do as many deeply nested imports).
- Avoid putting non-trivial logic in a `mod.rs` file; this should usually be located in a submodule.
- Use fully qualified imports rarely, prefer importing the type most of the time, or otherwise a module if it is conventional.
- Strongly prefer importing types or modules at the very top of the module. Never import types or modules within function contexts, unless the function is gated by a `cfg()` of some kind.
- Avoid importing enum variants for pattern matching.
- Always use `core` instead of `std` where possible (e.g., `core::error::Error` instead of `std::error::Error`)

### Memory and performance

- Use borrows (ideally) or `Arc` (when necessary) for shared immutable data.
- Pay careful attention to copying vs. referencing.
- Stream data where possible rather than buffering.
- Add a "Performance" section to documentation of public methods if the method may be sensitive.
- Mark public methods in library crates with `#[inline]` where appropriate.
- Make code friendly to automatic vectorization where possible.

## Testing practices

### Running tests

- Always use `cargo nextest run` to run unit and integration tests.
- For doctests, use `cargo test --doc` (doctests are not supported by nextest).

### Test organization

- Unit, property, and snapshot tests in the same file as the code they test.
- Fixtures in dedicated `fixtures/` folders.

### Testing tools

- **nextest**: Test runner that replaces the built-in cargo runnen.
- **proptest**: For property-based testing.
- **insta**: For snapshot testing.

## Commit message style

### Commit quality

- **Atomic commits**: Each commit should be a logical unit of change.
- **Bisect-able history**: Every commit must build and pass all checks.
- **Separate concerns**: Format fixes and refactoring should be in separate commits from feature changes.

## Architecture

### Key design principles

1. **Generic traits**: We offer several implementations for tile providers and graph tile access. Almost all operations are generic over these, with compile-time monomorphization.
2. **Zero-copy parsing**: We extensively use a bit-level format, and use zero-copy techniques which safely transmute the bytes from tile data without copying.
3. **Full error space modeling**: We handle all failure modes.
4. **Ergonomic APIs**: We strive for APIs that push the user into the "pit of success." APIs should be very difficult or impossible to use "wrong" or in a way that compromises performance.
5. **Valhalla compatibility**: For parts of the code that touch a concept defined by Valhalla, we must remain interoperable with modern Valhalla systems. Innovation typically happens by extension (e.g., in a new microservice, or with a backward-compatible improvement).

### Important library crates

Valinor's core is a set of library crates.
Binary crates build on top of these (and we don't have much to say about them in this document; refer to crate READMEs as needed).

#### valhalla-graphtile

The `valhalla-graphtile` crate enables reading, writing, and traversal of routing graph tiles.
These are binary-compatible with the [Valhalla routing engine](https://github.com/valhalla/valhalla).
It is designed around generic tile provider and graph tile crates,
which ensure a consistent API while allowing different data storage patterns.

Most production workloads use tarball tile providers, which are backed by a memory map.
This lets us squeeze maximum performance out of things by avoiding copies in application code,
delegating access, and caching to the operating system (most do this very well).
Other tile providers have fewer performance constraints, and are allowed (or even required to) copy data.

`GraphTileView::try_from` contains the main routing tile parsing logic.
This is centralized and shared across all routing tile providers.

Live traffic data is also supported by the `valhalla-graphtile` crate.
These tiles are also confusingly referred to as graph tiles in some contexts,
but the traffic tiles have a much simpler format and act purely as an extension of attributes
for edges in the routing graph.

#### valhalla-microservice

The `valhalla-microservice` crate is a framework for building microservices that are compatible with a Valhalla system.
All communication happens over ZeroMQ sockets,
which enable flexible deployment ranging from in-process to over the network.

The `valhalla-microservice` [README](valhalla-microservice/README.md)
contains more details about its design and features.

## Dependencies

### Workspace dependencies

- All dependency versions managed in root `Cargo.toml` `[workspace.dependencies]` (NOTE: this does not apply to the package version of the crate itself).
- Always use the latest regular (not alpha, beta, or pre-release) version of a package unless there is a temporary issue; document these whenever they appear.

### Key dependencies

- `clap`: CLI parsing with derives.
- `geo`: Geospatial data types and operations (use these wherever possible instead of rolling your own logic).
- `tokio`: Async runtime for I/O and concurrency.
- `thiserror`: Error derive macros.
- `tracing`: Tracing framework for logging and diagnostics.
- `zerocopy`: Zero-copy data structures for efficient memory usage.

## Quick reference

### Commands

```bash
# Run tests (ALWAYS use nextest for unit/integration tests)
cargo nextest run

# Run doctests (nextest doesn't support these)
cargo test --doc

# Format code (REQUIRED before committing)
cargo fmt

# Lint
cargo clippy

# Build
cargo build
```
