import copy

from valinor_integration.checks import CHECKS, diff_projections

ROUTE = {
    "trip": {
        "status": 0,
        "units": "kilometers",
        "locations": [{"lat": 1.0, "lon": 2.0}],
        "summary": {"length": 1.5, "time": 90.0, "min_lat": 1.0},
        "legs": [
            {
                "shape": "abc",
                "summary": {"length": 1.5, "time": 90.0},
                "maneuvers": [{"type": 1, "instruction": "Go.", "length": 1.5, "extra": "x"}],
            }
        ],
    }
}

LOCATE = [
    {
        "edges": [
            {"edge_id": {"value": 2}, "edge_info": {"way_id": 7}, "percent_along": 0.5},
            {"edge_id": {"value": 1}, "edge_info": {"way_id": 7}, "percent_along": 0.0},
        ]
    }
]


def test_route_projection_ignores_excluded_fields() -> None:
    other = copy.deepcopy(ROUTE)
    other["trip"]["locations"] = []
    other["trip"]["summary"]["min_lat"] = 9.0
    other["trip"]["legs"][0]["maneuvers"][0]["extra"] = "y"
    project = CHECKS["/route"].project
    assert project(ROUTE) == project(other)


def test_route_projection_finds_differences() -> None:
    other = copy.deepcopy(ROUTE)
    other["trip"]["legs"][0]["shape"] = "abd"
    project = CHECKS["/route"].project
    diff = diff_projections("route/x", project(ROUTE), project(other), "full", "sub")
    assert "--- full/route/x" in diff
    assert '"shape": "abd"' in diff


def test_route_validation() -> None:
    validate = CHECKS["/route"].validate
    assert validate(ROUTE) == []
    assert validate({"trip": {"legs": []}}) != []
    assert validate([]) != []


def test_locate_projection_is_order_independent() -> None:
    reordered = [{"edges": list(reversed(LOCATE[0]["edges"]))}]
    project = CHECKS["/locate"].project
    assert project(LOCATE) == project(reordered)
    assert project(LOCATE)[0][0]["way_id"] == 7


def test_locate_validation_rejects_empty_results() -> None:
    validate = CHECKS["/locate"].validate
    assert validate(LOCATE) == []
    assert validate([{"edges": []}]) != []
    assert validate([]) != []


def test_equal_projections_have_no_diff() -> None:
    assert diff_projections("x", {"a": 1}, {"a": 1}, "full", "sub") == ""
