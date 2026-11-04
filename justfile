default:
    @just --list

# Format Rust code.
fmt:
    cargo fmt --all

# Check formatting, Rust lints, and spelling.
lint:
    just typos
    cargo fmt --all -- --check
    cargo clippy --workspace --all-targets -- -D warnings

# Check spelling.
typos:
    typos .

# Run unit, integration, and documentation tests.
test: test-unit test-doc

# Run unit and integration tests, with optional nextest arguments.
[positional-arguments]
test-unit *ARGS:
    cargo nextest run --workspace --no-fail-fast "$@"

# Run documentation tests.
test-doc:
    cargo test --workspace --doc

# Run unit and integration tests under Miri, with optional nextest arguments.
[positional-arguments]
miri *ARGS:
    MIRIFLAGS="${MIRIFLAGS:--Zmiri-disable-isolation}" cargo +nightly miri nextest run --workspace --no-fail-fast "$@"

# Run documentation tests under Miri.
miri-doc:
    MIRIFLAGS="${MIRIFLAGS:--Zmiri-disable-isolation}" cargo +nightly miri test --workspace --doc

# Run the Valinor CLI, forwarding all arguments.
[positional-arguments]
cli *ARGS:
    cargo run -p valinor-cli -- "$@"
