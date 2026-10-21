# Integration tests with C++ Valhalla

This harness makes sure that a sub-extract from `valinor-cli extract`
works in stock C++ Valhalla the same way as the full extract.

The harness does these steps:

1. It writes a sub-extract of the full extract with `valinor-cli extract`.
   The tiles are in [`sub-extract-tiles.txt`](sub-extract-tiles.txt).
   The sub-extract must be a proper subset of the full extract,
   or the comparison would prove nothing.
2. It starts two `valhalla_service` containers with docker-py:
   one for the full extract and one for the sub-extract.
   The image's own `valhalla_build_config` makes the config.
   The harness sets `mjolnir.shortcut_caching` to `false`,
   because Valhalla stops at startup with a partial extract when it is `true`.
3. It sends each request of the [Bruno collection](bruno/) to both servers.
   It saves each response, and it compares the two responses of each request
   (see [`checks.py`](src/valinor_integration/checks.py) for the fields that it compares).
4. It makes sure that the logs of both servers contain no `[ERROR]` lines.

The default full extract is the Andorra fixture
(`valhalla-graphtile/fixtures/andorra-tiles.tar`).

## Requirements

- [uv](https://docs.astral.sh/uv/)
- Docker (Docker Desktop, colima, or a Docker daemon on Linux)
- cargo, if you do not set `VALINOR_CLI`

## Run the test

From the root of the repository:

```bash
uv run --project scripts/integration valinor-integration
```

The command prints `integration: PASS`, or a list of failures with a diff for each difference.
The work directory (`target/integration` by default) contains:

- `sub-extract.tar`: the sub-extract.
- `valhalla.json`: the Valhalla config.
- `responses/full/` and `responses/sub/`: the raw response of each request.
- `valhalla-full.log` and `valhalla-sub.log`: the logs of the two servers.

Use `--help` for the options (a different full extract, work directory, tile list, or collection).

## Send requests by hand with Bruno

```bash
uv run --project scripts/integration valinor-integration serve
```

This serves the full extract at `http://localhost:8002`
and the sub-extract at `http://localhost:8003` until you push Ctrl-C.
Open `scripts/integration/bruno` in [Bruno](https://www.usebruno.com/),
and select the `full` or the `sub` environment.

## Environment variables

All variables are optional.

| Variable | Default | Description |
| --- | --- | --- |
| `VALHALLA_VERSION` | `latest` | The tag of the Valhalla image, such as `3.8.2`. CI sets it in [`integration.yml`](../../.github/workflows/integration.yml). If it is not set, the harness uses `latest` and logs a warning. |
| `VALHALLA_IMAGE` | `ghcr.io/valhalla/valhalla` | The image repository. |
| `VALINOR_CLI` | (none) | The path of a `valinor-cli` binary. If it is not set, the harness runs `cargo run --release -p valinor-cli`. |
| `VALHALLA_PORT` | `8002` | The port of the full extract in `serve` mode. The sub-extract uses the next port. If you change it, change the Bruno environments too. |

## Add a request

1. Add the request to the Bruno collection.
   You can do this in the Bruno app, or you can copy a file in `bruno/route/`.
   Keep all coordinates far inside the tiles of the sub-extract,
   so that the request never needs a tile which the sub-extract does not contain.
2. If the request uses a new endpoint, add a check for the endpoint to
   [`checks.py`](src/valinor_integration/checks.py).
   The harness refuses a request for an endpoint that has no check.

The harness reads a subset of the Bruno YAML format:
the method, the URL (with `{{baseUrl}}`), headers, and a JSON body.
It refuses requests with Bruno scripts or assertions,
because it does not run them; put such checks in `checks.py`.

## Unit tests of the harness

```bash
uv run --project scripts/integration pytest
```

```bash
uv run --project scripts/integration ruff check
```
