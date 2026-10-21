"""Reads the requests of a Bruno collection in the OpenCollection YAML format.

The harness reads an HTTP method, a URL with ``{{variable}}`` placeholders, headers,
and a JSON body. It refuses a request that uses more, such as scripts or assertions,
so that it never sends a different request than Bruno.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any
from urllib.parse import urlsplit

import yaml

from valinor_integration.errors import HarnessError

COLLECTION_FILE = "opencollection.yml"
FOLDER_FILE = "folder.yml"
ENVIRONMENTS_DIR = "environments"

# The keys of a request file that the harness reads, or ignores (`settings` and `docs`).
_REQUEST_KEYS = {"info", "http", "settings", "docs"}
_HTTP_KEYS = {"method", "url", "body", "headers", "auth"}
_VARIABLE = re.compile(r"\{\{\s*([A-Za-z0-9_.-]+)\s*\}\}")


@dataclass(frozen=True)
class BrunoRequest:
    """One HTTP request of the collection."""

    #: The request name, from ``info.name``.
    name: str
    #: The path of the request file, relative to the collection root.
    path: Path
    seq: int
    method: str
    #: The URL, with ``{{variable}}`` placeholders.
    url: str
    headers: Mapping[str, str] = field(default_factory=dict)
    #: The parsed JSON body, or ``None`` if the request has no body.
    body: Any = None

    @property
    def id(self) -> str:
        """A unique ID: the path of the request file without the extension."""
        return self.path.with_suffix("").as_posix()

    def resolve_url(self, variables: Mapping[str, str]) -> str:
        """Replaces the ``{{variable}}`` placeholders of the URL."""

        def replace(match: re.Match[str]) -> str:
            name = match.group(1)
            if name not in variables:
                raise HarnessError(f"{self.path}: the URL uses the unknown variable {{{{{name}}}}}")
            return variables[name]

        return _VARIABLE.sub(replace, self.url)

    def endpoint(self, variables: Mapping[str, str]) -> str:
        """The path of the resolved URL (for example, ``/route``)."""
        return urlsplit(self.resolve_url(variables)).path


def load_collection(root: Path) -> list[BrunoRequest]:
    """Reads every request of the collection at ``root``, in the order of the Bruno app."""
    if not (root / COLLECTION_FILE).is_file():
        raise HarnessError(f"{root} is not a Bruno collection: it has no {COLLECTION_FILE}")

    requests = []
    for path in sorted(root.rglob("*.yml")):
        relative = path.relative_to(root)
        if relative.name in (COLLECTION_FILE, FOLDER_FILE) or relative.parts[0] == ENVIRONMENTS_DIR:
            continue
        requests.append(parse_request(relative, path.read_text(encoding="utf-8")))

    if not requests:
        raise HarnessError(f"the Bruno collection at {root} contains no requests")
    ids = [request.id for request in requests]
    if len(set(ids)) != len(ids):
        raise HarnessError(f"the Bruno collection at {root} contains duplicate request IDs")

    requests.sort(key=lambda request: (request.path.parent.as_posix(), request.seq, request.name))
    return requests


def parse_request(path: Path, text: str) -> BrunoRequest:
    """Parses one request file. ``path`` is only used in error messages and the request ID."""

    def fail(message: str) -> HarnessError:
        return HarnessError(f"{path}: {message}")

    try:
        document = yaml.safe_load(text)
    except yaml.YAMLError as e:
        raise fail(f"invalid YAML: {e}") from None
    if not isinstance(document, dict):
        raise fail("a request file must be a YAML mapping")

    unsupported = set(document) - _REQUEST_KEYS
    if unsupported:
        raise fail(
            f"unsupported sections {sorted(unsupported)}; the harness does not run Bruno "
            "scripts or assertions (put checks in valinor_integration.checks)"
        )

    info = document.get("info") or {}
    if info.get("type") != "http":
        raise fail(f"unsupported request type {info.get('type')!r}; expected 'http'")
    name = info.get("name")
    if not isinstance(name, str) or not name:
        raise fail("info.name must be a non-empty string")
    seq = info.get("seq", 0)
    if not isinstance(seq, int):
        raise fail("info.seq must be an integer")

    http = document.get("http") or {}
    unsupported = set(http) - _HTTP_KEYS
    if unsupported:
        raise fail(f"unsupported http fields {sorted(unsupported)}")
    method = http.get("method")
    url = http.get("url")
    if not isinstance(method, str) or not isinstance(url, str):
        raise fail("http.method and http.url must be strings")
    if http.get("auth", "none") not in ("none", "inherit"):
        raise fail("authentication is not supported")

    return BrunoRequest(
        name=name,
        path=path,
        seq=seq,
        method=method.upper(),
        url=url,
        headers=_parse_headers(http.get("headers"), fail),
        body=_parse_body(http.get("body"), fail),
    )


def _parse_headers(headers: Any, fail: Any) -> dict[str, str]:
    if headers is None:
        return {}
    if not isinstance(headers, list):
        raise fail("http.headers must be a list")
    parsed = {}
    for header in headers:
        if not isinstance(header, dict) or not isinstance(header.get("name"), str):
            raise fail("each header must have a name")
        if header.get("disabled", False):
            continue
        parsed[header["name"]] = str(header.get("value", ""))
    return parsed


def _parse_body(body: Any, fail: Any) -> Any:
    if body is None:
        return None
    if not isinstance(body, dict) or body.get("type") != "json":
        raise fail("only JSON bodies (http.body.type: json) are supported")
    data = body.get("data")
    if not isinstance(data, str):
        raise fail("http.body.data must be a string of JSON")
    try:
        return json.loads(data)
    except json.JSONDecodeError as e:
        raise fail(f"http.body.data is not valid JSON: {e}") from None
