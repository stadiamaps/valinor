from pathlib import Path

import pytest

from valinor_integration.collection import load_collection, parse_request
from valinor_integration.errors import HarnessError
from valinor_integration.settings import DEFAULT_COLLECTION

REQUEST = """\
info:
  name: example
  type: http
  seq: 2

http:
  method: post
  url: "{{baseUrl}}/route"
  headers:
    - name: X-Enabled
      value: "yes"
    - name: X-Disabled
      value: "no"
      disabled: true
  body:
    type: json
    data: |-
      {"costing": "auto"}
  auth: inherit

settings:
  encodeUrl: true
"""


def test_parse_request() -> None:
    request = parse_request(Path("route/example.yml"), REQUEST)
    assert request.name == "example"
    assert request.id == "route/example"
    assert request.seq == 2
    assert request.method == "POST"
    assert request.headers == {"X-Enabled": "yes"}
    assert request.body == {"costing": "auto"}
    assert request.resolve_url({"baseUrl": "http://localhost:1"}) == "http://localhost:1/route"
    assert request.endpoint({"baseUrl": "http://localhost:1"}) == "/route"
    assert request.endpoint({"baseUrl": ""}) == "/route"


def test_unknown_variable_is_an_error() -> None:
    request = parse_request(Path("route/example.yml"), REQUEST)
    with pytest.raises(HarnessError, match="unknown variable"):
        request.resolve_url({})


@pytest.mark.parametrize(
    ("replace", "by", "message"),
    [
        ("settings:", "runtime:\n  scripts: []\nsettings:", "unsupported sections"),
        ("  auth: inherit", "  params: []", "unsupported http fields"),
        ("  auth: inherit", "  auth:\n    type: bearer", "authentication"),
        ("    type: json", "    type: xml", "only JSON bodies"),
        ('{"costing": "auto"}', '{"costing": ', "not valid JSON"),
        ("  type: http", "  type: graphql", "unsupported request type"),
        ("  name: example", "  name: ''", "info.name"),
    ],
)
def test_unsupported_requests_are_rejected(replace: str, by: str, message: str) -> None:
    assert replace in REQUEST
    with pytest.raises(HarnessError, match=message):
        parse_request(Path("route/example.yml"), REQUEST.replace(replace, by, 1))


def test_load_collection_order_and_skipped_files(tmp_path: Path) -> None:
    (tmp_path / "opencollection.yml").write_text("opencollection: 1.0.0\n")
    (tmp_path / "environments").mkdir()
    (tmp_path / "environments" / "local.yml").write_text("name: local\n")
    (tmp_path / "b").mkdir()
    (tmp_path / "b" / "folder.yml").write_text("info:\n  type: folder\n")
    (tmp_path / "b" / "second.yml").write_text(REQUEST.replace("name: example", "name: second"))
    (tmp_path / "b" / "first.yml").write_text(
        REQUEST.replace("name: example", "name: first").replace("seq: 2", "seq: 1")
    )

    assert [request.id for request in load_collection(tmp_path)] == ["b/first", "b/second"]


def test_load_collection_requires_a_collection_file(tmp_path: Path) -> None:
    with pytest.raises(HarnessError, match="not a Bruno collection"):
        load_collection(tmp_path)


def test_the_repository_collection_loads() -> None:
    requests = load_collection(DEFAULT_COLLECTION)
    endpoints = {request.endpoint({"baseUrl": ""}) for request in requests}
    assert endpoints == {"/route", "/locate"}
    assert all(request.body for request in requests)
