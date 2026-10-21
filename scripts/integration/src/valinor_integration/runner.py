"""The two modes of the harness: ``run`` (the test) and ``serve`` (for manual requests)."""

from __future__ import annotations

import json
import logging
import shutil
import time
from contextlib import ExitStack
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import requests

from valinor_integration import valhalla
from valinor_integration.checks import CHECKS, diff_projections
from valinor_integration.collection import BrunoRequest, load_collection
from valinor_integration.errors import HarnessError
from valinor_integration.extract import check_proper_subset, read_tile_list, write_sub_extract
from valinor_integration.settings import Settings

log = logging.getLogger(__name__)

#: The names of the two extracts.
FULL = "full"
SUB = "sub"


@dataclass(frozen=True)
class Inputs:
    """The files of a harness run."""

    full_extract: Path
    workdir: Path
    tile_list: Path
    collection: Path

    @property
    def sub_extract(self) -> Path:
        return self.workdir / "sub-extract.tar"


def run(settings: Settings, inputs: Inputs) -> bool:
    """Serves both extracts, sends every request to both, and compares the responses.

    Returns ``True`` if every check passes.
    The responses, the logs, and the config are saved in the work directory.
    """
    collection = _load_checked_collection(inputs.collection)
    client, config = _prepare(settings, inputs)

    responses_dir = inputs.workdir / "responses"
    shutil.rmtree(responses_dir, ignore_errors=True)

    failures: list[str] = []
    responses: dict[str, dict[str, Any]] = {}
    with ExitStack() as stack:
        servers = {
            name: stack.enter_context(
                valhalla.ValhallaServer(client, settings.image_ref, name, extract, config)
            )
            for name, extract in ((FULL, inputs.full_extract), (SUB, inputs.sub_extract))
        }

        for name, server in servers.items():
            responses[name] = _send_all(server, collection, responses_dir / name, failures)

        # Capture the logs before the containers are removed.
        for name, server in servers.items():
            logs = server.logs()
            log_file = inputs.workdir / f"valhalla-{name}.log"
            log_file.write_text(logs, encoding="utf-8")
            error_lines = [line for line in logs.splitlines() if "[ERROR]" in line]
            if error_lines:
                failures.append(
                    f"{name}: {len(error_lines)} [ERROR] lines in the valhalla_service log "
                    f"({log_file}); the first is: {error_lines[0]}"
                )

    for request in collection:
        full, sub = responses[FULL].get(request.id), responses[SUB].get(request.id)
        if full is None or sub is None:
            continue  # The send failure is already in `failures`.
        check = CHECKS[request.endpoint(_variables(""))]
        diff = diff_projections(request.id, check.project(full), check.project(sub), FULL, SUB)
        if diff:
            failures.append(f"{request.id}: the responses differ:\n{diff}")
        else:
            log.info("ok: %s is identical for both extracts", request.id)

    for failure in failures:
        log.error("FAIL: %s", failure)
    return not failures


def serve(settings: Settings, inputs: Inputs) -> None:
    """Serves both extracts on fixed ports until Ctrl-C or SIGTERM raises ``KeyboardInterrupt``."""
    client, config = _prepare(settings, inputs)
    ports = {FULL: settings.serve_port, SUB: settings.serve_port + 1}

    with ExitStack() as stack:
        servers = [
            stack.enter_context(
                valhalla.ValhallaServer(
                    client, settings.image_ref, name, extract, config, host_port=ports[name]
                )
            )
            for name, extract in ((FULL, inputs.full_extract), (SUB, inputs.sub_extract))
        ]
        log.info(
            "serving the full extract at %s and the sub-extract at %s; "
            "in Bruno, open %s and select the 'full' or 'sub' environment; press Ctrl-C to stop",
            servers[0].base_url,
            servers[1].base_url,
            inputs.collection,
        )
        while True:
            time.sleep(1)


def _load_checked_collection(root: Path) -> list[BrunoRequest]:
    """Loads the collection, and makes sure that every request has a check."""
    collection = load_collection(root)
    for request in collection:
        endpoint = request.endpoint(_variables(""))
        if endpoint not in CHECKS:
            raise HarnessError(
                f"{request.path}: the harness has no check for {endpoint}; "
                f"add one to valinor_integration.checks (known: {sorted(CHECKS)})"
            )
    log.info("loaded %d requests from %s", len(collection), root)
    return collection


def _prepare(settings: Settings, inputs: Inputs) -> tuple[Any, dict[str, Any]]:
    """Writes the sub-extract, and prepares Docker and the Valhalla config."""
    if not inputs.full_extract.is_file():
        raise HarnessError(f"the full extract is not a file: {inputs.full_extract}")
    inputs.workdir.mkdir(parents=True, exist_ok=True)

    tiles = read_tile_list(inputs.tile_list)
    inputs.sub_extract.unlink(missing_ok=True)
    write_sub_extract(settings, inputs.full_extract, tiles, inputs.sub_extract)
    for entry in check_proper_subset(inputs.full_extract, inputs.sub_extract):
        log.info("only in the full extract: %s", entry)

    client = valhalla.connect()
    valhalla.ensure_image(client, settings)
    config = valhalla.build_config(client, settings.image_ref)
    (inputs.workdir / "valhalla.json").write_text(json.dumps(config, indent=2), encoding="utf-8")
    return client, config


def _variables(base_url: str) -> dict[str, str]:
    """The variables of the Bruno environments, for one server."""
    return {"baseUrl": base_url}


def _send_all(
    server: valhalla.ValhallaServer,
    collection: list[BrunoRequest],
    out_dir: Path,
    failures: list[str],
) -> dict[str, Any]:
    """Sends every request to one server, and saves and validates each response."""
    variables = _variables(server.base_url)
    responses = {}
    for request in collection:
        label = f"{server.name}: {request.id}"
        try:
            response = requests.request(
                request.method,
                request.resolve_url(variables),
                json=request.body,
                headers=dict(request.headers),
                timeout=valhalla.REQUEST_TIMEOUT_SECONDS,
            )
        except requests.RequestException as e:
            failures.append(f"{label}: the request failed: {e}")
            continue

        out_path = out_dir / f"{request.id}.json"
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(response.text, encoding="utf-8")

        if response.status_code != 200:
            failures.append(f"{label}: HTTP {response.status_code}: {response.text[:500]}")
            continue
        try:
            body = response.json()
        except ValueError:
            failures.append(f"{label}: the response is not JSON")
            continue

        problems = CHECKS[request.endpoint(variables)].validate(body)
        if problems:
            failures.extend(f"{label}: {problem}" for problem in problems)
            continue
        responses[request.id] = body
    return responses
