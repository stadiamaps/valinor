#!/usr/bin/env bash
# Integration tests of offline tile extracts with C++ Valhalla.
#
# Writes a sub-extract of the full extract with `valinor-cli extract`
# (the tiles are in sub-extract-tiles.txt), serves it with a stock,
# digest-pinned Valhalla Docker image (the C++ engine), and makes sure
# that the sub-extract behaves the same as the full extract:
#
#   1. The service starts cleanly against the sub-extract (no [ERROR] lines).
#   2. A fixed set of interior /route requests (requests.json) returns results
#      identical to the same requests served from the full fixture
#      (shape + maneuvers + summary length/time; see harness.py for the exact
#      projection and the documented excluded/volatile fields).
#   3. /locate succeeds on an interior point (and actually finds edges).
#
# The two extracts are served SEQUENTIALLY, not side by side: Valhalla's
# responses are deterministic for a fixed tileset, so nothing requires both
# servers to be up at once, and sequential runs reuse one port, one container
# name, and one code path per extract (to add an extract, reuse the loop).
#
# The image is pinned by digest in valhalla-image.txt (the single pinning
# point). See the comments in that file before you change it.
#
# Usage: run_integration.sh [<full-extract.tar> [<workdir>]]
#
# The full extract defaults to the Andorra fixture,
# and the work directory defaults to target/integration.
# Set VALINOR_CLI to the path of a valinor-cli binary to use it;
# otherwise the script builds and runs valinor-cli with cargo.
#
# Docker mounts the work directory into the Valhalla container.
# With a Docker VM (for example, colima or Docker Desktop on macOS),
# the work directory must be in a path that the VM shares
# (by default, your home directory; /tmp does not work).
#
# Requires: cargo (unless VALINOR_CLI is set), docker, python3, curl, tar.
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/../.." &>/dev/null && pwd)
PORT=${VALHALLA_PORT:-8002}
READINESS_TIMEOUT_SECONDS=90

if [[ $# -gt 2 ]]; then
    echo "usage: $0 [<full-extract.tar> [<workdir>]]" >&2
    exit 2
fi
FULL_EXTRACT=${1:-$REPO_ROOT/valhalla-graphtile/fixtures/andorra-tiles.tar}
mkdir -p "${2:-$REPO_ROOT/target/integration}"
# Resolve to an absolute path: docker -v rejects relative host paths.
WORKDIR=$(cd -- "${2:-$REPO_ROOT/target/integration}" &>/dev/null && pwd)
SUB_EXTRACT="$WORKDIR/sub-extract.tar"

# The one place the Valhalla image is defined; see the comments in that file.
IMAGE=$(grep -v '^[[:space:]]*#' "$SCRIPT_DIR/valhalla-image.txt" | grep -m1 .)
if [[ "$IMAGE" != *@sha256:* ]]; then
    echo "FATAL: image in valhalla-image.txt is not pinned by digest: $IMAGE" >&2
    exit 1
fi
echo "valhalla image: $IMAGE"

# valinor_cli <args>...
# Runs the given valinor-cli binary, or builds and runs it with cargo.
valinor_cli() {
    if [[ -n "${VALINOR_CLI:-}" ]]; then
        "$VALINOR_CLI" "$@"
    else
        cargo run --quiet --release --manifest-path "$REPO_ROOT/Cargo.toml" \
            --package valinor-cli -- "$@"
    fi
}

# Writes the sub-extract with the tiles in sub-extract-tiles.txt.
write_sub_extract() {
    local tiles
    # Remove comments and blank lines, then join the tiles with commas.
    tiles=$(sed -e 's/#.*//' -e '/^[[:space:]]*$/d' "$SCRIPT_DIR/sub-extract-tiles.txt" \
        | tr -d '[:blank:]' | paste -sd, -)
    if [[ -z "$tiles" ]]; then
        echo "FATAL: sub-extract-tiles.txt contains no tiles" >&2
        exit 1
    fi
    rm -f "$SUB_EXTRACT"
    valinor_cli extract "$FULL_EXTRACT" "$SUB_EXTRACT" --tile "$tiles"
}

CONTAINER=""
cleanup() {
    if [[ -n "$CONTAINER" ]]; then
        docker rm -f "$CONTAINER" >/dev/null 2>&1 || true
    fi
}
trap cleanup EXIT

# Guard against a vacuous comparison: the sub-extract must be a PROPER subset
# of the full fixture's tiles, or this whole job would compare an extract with
# itself and prove nothing.
check_proper_subset() {
    local full_list sub_list
    full_list=$(tar -tf "$FULL_EXTRACT" | sort)
    sub_list=$(tar -tf "$SUB_EXTRACT" | sort)
    if [[ -n "$(comm -13 <(echo "$full_list") <(echo "$sub_list"))" ]]; then
        echo "FATAL: sub-extract contains entries missing from the full fixture" >&2
        exit 1
    fi
    if [[ "$full_list" == "$sub_list" ]]; then
        echo "FATAL: sub-extract is identical to the full fixture; the sub-extract does not remove any tiles" >&2
        exit 1
    fi
    echo "sub-extract is a proper subset of the full fixture:"
    comm -23 <(echo "$full_list") <(echo "$sub_list") | sed 's/^/  only in full: /'
}

# serve_and_query <extract.tar> <name>
# Boots the pinned image against the extract, waits for readiness, runs the
# fixed request set, saves responses to $WORKDIR/responses-<name>, and asserts
# the logs are free of tile errors.
serve_and_query() {
    local extract=$1 name=$2
    local data_dir="$WORKDIR/data-$name"
    local response_dir="$WORKDIR/responses-$name"
    local log_file="$WORKDIR/valhalla-$name.log"
    mkdir -p "$data_dir" "$response_dir"
    cp "$extract" "$data_dir/tiles.tar"

    # Generate the config with the image's OWN valhalla_build_config, so the
    # key set always matches the pinned engine version (a digest bump cannot
    # silently desynchronize a hand-maintained config), then harden it for
    # partial extracts (harness.py forces mjolnir.shortcut_caching=false;
    # see the comment in harness.py for the reason).
    docker run --rm --entrypoint valhalla_build_config "$IMAGE" \
        --mjolnir-tile-extract /data/tiles.tar \
        | python3 "$SCRIPT_DIR/harness.py" make-config --tile-extract /data/tiles.tar \
        >"$data_dir/valhalla.json"

    echo "starting valhalla_service against $name extract..."
    CONTAINER="valinor-integration-$name"
    docker rm -f "$CONTAINER" >/dev/null 2>&1 || true
    docker run -d --name "$CONTAINER" \
        -p "$PORT:8002" \
        -v "$data_dir:/data:ro" \
        --entrypoint valhalla_service \
        "$IMAGE" /data/valhalla.json 1 >/dev/null

    local ready=0
    for _ in $(seq 1 "$READINESS_TIMEOUT_SECONDS"); do
        if curl -sf "http://localhost:$PORT/status" >/dev/null 2>&1; then
            ready=1
            break
        fi
        if [[ "$(docker inspect -f '{{.State.Running}}' "$CONTAINER" 2>/dev/null)" != "true" ]]; then
            break
        fi
        sleep 1
    done
    if [[ "$ready" -ne 1 ]]; then
        echo "FATAL: valhalla_service did not become ready for $name extract; logs:" >&2
        docker logs "$CONTAINER" >&2 || true
        exit 1
    fi

    python3 "$SCRIPT_DIR/harness.py" query \
        "http://localhost:$PORT" "$SCRIPT_DIR/requests.json" "$response_dir"

    # Capture logs BEFORE removing the container, then require them to be free
    # of errors: a partial extract must serve without any tile errors.
    docker logs "$CONTAINER" >"$log_file" 2>&1
    docker rm -f "$CONTAINER" >/dev/null
    CONTAINER=""
    if grep -F '[ERROR]' "$log_file"; then
        echo "FATAL: [ERROR] lines in valhalla_service logs for $name extract (see above; full log: $log_file)" >&2
        exit 1
    fi
    echo "$name extract served cleanly (log: $log_file)"
}

write_sub_extract
check_proper_subset
serve_and_query "$FULL_EXTRACT" full
serve_and_query "$SUB_EXTRACT" sub

python3 "$SCRIPT_DIR/harness.py" compare \
    "$SCRIPT_DIR/requests.json" "$WORKDIR/responses-full" "$WORKDIR/responses-sub"

echo "integration: PASS"
