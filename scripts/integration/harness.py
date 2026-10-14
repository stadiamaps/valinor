#!/usr/bin/env python3
"""Python helpers for the integration tests of offline tile extracts with C++ Valhalla.

Invoked by run_integration.sh; stdlib only (no pip dependencies).

Subcommands:

- ``make-config``: read a raw config from ``valhalla_build_config`` on stdin,
  harden it for partial extracts, and write the final config to stdout.
- ``query``: run the fixed request set (requests.json) against a running
  Valhalla service and save the raw responses.
- ``compare``: assert that the saved /route responses from two servers
  (full fixture vs. sub-extract) are behaviorally identical.
"""

import argparse
import difflib
import json
import sys
import urllib.error
import urllib.request
from pathlib import Path

REQUEST_TIMEOUT_SECONDS = 30


def make_config(args: argparse.Namespace) -> int:
    """Hardens a generated Valhalla config for serving a (possibly partial) extract.

    The raw config comes from the pinned image's own ``valhalla_build_config``,
    so the key set always matches the engine version under test.
    """
    config = json.load(sys.stdin)

    mjolnir = config["mjolnir"]
    # Serve tiles from the mounted extract tarball only.
    mjolnir["tile_extract"] = args.tile_extract
    # MUST NOT enable shortcut_caching: when enabled, stock Valhalla pre-recovers
    # every shortcut at startup and asserts that every level-0/1 tile exists,
    # which aborts on any partial extract. It must remain false for any extract
    # this harness serves.
    mjolnir["shortcut_caching"] = False

    json.dump(config, sys.stdout, indent=2)
    return 0


def _post_json(url: str, request_body: dict) -> dict:
    data = json.dumps(request_body).encode("utf-8")
    http_request = urllib.request.Request(
        url, data=data, headers={"Content-Type": "application/json"}
    )
    with urllib.request.urlopen(http_request, timeout=REQUEST_TIMEOUT_SECONDS) as response:
        if response.status != 200:
            raise RuntimeError(f"{url} returned HTTP {response.status}")
        return json.load(response)


def query(args: argparse.Namespace) -> int:
    """Runs the fixed request set against a Valhalla service and saves responses."""
    requests = json.loads(Path(args.requests).read_text(encoding="utf-8"))
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    failures = []
    for route in requests["routes"]:
        name = route["name"]
        try:
            response = _post_json(f"{args.base_url}/route", route["request"])
        except (urllib.error.URLError, RuntimeError, json.JSONDecodeError) as e:
            failures.append(f"/route {name}: {e}")
            continue
        out_path = out_dir / f"route-{name}.json"
        out_path.write_text(json.dumps(response, indent=2), encoding="utf-8")
        print(f"ok: /route {name}")

    # /locate must succeed on an interior point and actually find edges;
    # an empty result would be a silent "succeeded but found nothing".
    try:
        response = _post_json(f"{args.base_url}/locate", requests["locate"]["request"])
        edge_count = sum(len(result.get("edges") or []) for result in response)
        if edge_count == 0:
            failures.append("/locate: response contains no edges")
        else:
            (out_dir / "locate.json").write_text(
                json.dumps(response, indent=2), encoding="utf-8"
            )
            print(f"ok: /locate ({edge_count} edges)")
    except (urllib.error.URLError, RuntimeError, json.JSONDecodeError) as e:
        failures.append(f"/locate: {e}")

    for failure in failures:
        print(f"FAIL: {failure}", file=sys.stderr)
    return 1 if failures else 0


# Per-maneuver fields included in the compared projection.
MANEUVER_FIELDS = (
    "type",
    "instruction",
    "verbal_pre_transition_instruction",
    "street_names",
    "length",
    "time",
    "begin_shape_index",
    "end_shape_index",
    "travel_mode",
    "travel_type",
)


def _project_route(response: dict) -> dict:
    """Projects a /route response onto the fields the integration tests compare.

    Compared (identical shape, maneuvers, and ETA):
    leg shape polylines, leg and trip summary length/time, maneuver
    instructions and geometry indices, and the trip status/units.

    Deliberately excluded:

    - ``trip.locations``: an echo of the request plus snap metadata; snap
      identity is already implied by identical shape and summaries.
    - ``trip.summary`` bbox members (``min_lat`` etc.): derived from shape.
    - Anything else (warnings, future additive fields): projecting instead of
      byte-comparing keeps the assertion pinned to routing behavior, so
      volatile fields (e.g. timestamps) a future engine may add cannot flake
      this check. As of Valhalla 3.8.2, /route responses contain no
      timestamps; /status (which has ``tileset_last_modified``) is only used
      for readiness and never compared.
    """
    trip = response["trip"]
    return {
        "status": trip.get("status"),
        "units": trip.get("units"),
        "summary": {
            "length": trip["summary"]["length"],
            "time": trip["summary"]["time"],
        },
        "legs": [
            {
                "shape": leg["shape"],
                "summary": {
                    "length": leg["summary"]["length"],
                    "time": leg["summary"]["time"],
                },
                "maneuvers": [
                    {field: maneuver.get(field) for field in MANEUVER_FIELDS}
                    for maneuver in leg["maneuvers"]
                ],
            }
            for leg in trip["legs"]
        ],
    }


def compare(args: argparse.Namespace) -> int:
    """Compares saved /route responses from the full fixture and the sub-extract."""
    requests = json.loads(Path(args.requests).read_text(encoding="utf-8"))
    mismatches = 0
    for route in requests["routes"]:
        name = route["name"]
        projections = []
        for side_dir in (args.full_dir, args.sub_dir):
            path = Path(side_dir) / f"route-{name}.json"
            response = json.loads(path.read_text(encoding="utf-8"))
            projections.append(_project_route(response))
        full_projection, sub_projection = projections
        if full_projection == sub_projection:
            print(f"ok: {name} identical")
            continue
        mismatches += 1
        print(f"FAIL: {name} differs between full fixture and sub-extract:", file=sys.stderr)
        diff = difflib.unified_diff(
            json.dumps(full_projection, indent=2).splitlines(keepends=True),
            json.dumps(sub_projection, indent=2).splitlines(keepends=True),
            fromfile=f"full/{name}",
            tofile=f"sub/{name}",
        )
        sys.stderr.writelines(diff)
    return 1 if mismatches else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="subcommand", required=True)

    config_parser = subparsers.add_parser("make-config")
    config_parser.add_argument("--tile-extract", required=True)
    config_parser.set_defaults(func=make_config)

    query_parser = subparsers.add_parser("query")
    query_parser.add_argument("base_url")
    query_parser.add_argument("requests")
    query_parser.add_argument("out_dir")
    query_parser.set_defaults(func=query)

    compare_parser = subparsers.add_parser("compare")
    compare_parser.add_argument("requests")
    compare_parser.add_argument("full_dir")
    compare_parser.add_argument("sub_dir")
    compare_parser.set_defaults(func=compare)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
