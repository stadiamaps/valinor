"""The checks of the responses, for each Valhalla endpoint.

A check has ``validate``, which finds problems in one response,
and ``project``, which keeps only the fields that the comparison uses.
To test a new endpoint, add a request to the Bruno collection and a check here.
"""

from __future__ import annotations

import difflib
import json
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from typing import Any

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


@dataclass(frozen=True)
class Check:
    validate: Callable[[Any], list[str]]
    project: Callable[[Any], Any]


def _validate_route(response: Any) -> list[str]:
    trip = response.get("trip") if isinstance(response, dict) else None
    if not isinstance(trip, dict) or not trip.get("legs"):
        return ["the response contains no trip legs"]
    return []


def _project_route(response: Any) -> Any:
    """Projects a /route response onto its status, units, shapes, summaries, and maneuvers."""
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
                    {name: maneuver.get(name) for name in MANEUVER_FIELDS}
                    for maneuver in leg["maneuvers"]
                ],
            }
            for leg in trip["legs"]
        ],
    }


def _validate_locate(response: Any) -> list[str]:
    if not isinstance(response, list) or not response:
        return ["the response is not a non-empty list of locations"]
    if sum(len(location.get("edges") or []) for location in response) == 0:
        return ["the response contains no edges"]
    return []


def _project_locate(response: Any) -> Any:
    """Projects a /locate response onto the edges found at each location."""
    return [
        sorted(
            (
                {
                    "edge_id": edge.get("edge_id"),
                    # With `verbose`, the OSM way ID is in the edge info.
                    "way_id": (edge.get("edge_info") or {}).get("way_id"),
                    "correlated_lat": edge.get("correlated_lat"),
                    "correlated_lon": edge.get("correlated_lon"),
                    "percent_along": edge.get("percent_along"),
                }
                for edge in location.get("edges") or []
            ),
            key=lambda edge: json.dumps(edge, sort_keys=True),
        )
        for location in response
    ]


#: The checks, by the path of the endpoint.
CHECKS: Mapping[str, Check] = {
    "/route": Check(validate=_validate_route, project=_project_route),
    "/locate": Check(validate=_validate_locate, project=_project_locate),
}


def diff_projections(
    name: str, expected: Any, actual: Any, expected_label: str, actual_label: str
) -> str:
    """A unified diff of two projections, or an empty string if they are equal."""
    if expected == actual:
        return ""
    return "".join(
        difflib.unified_diff(
            json.dumps(expected, indent=2, sort_keys=True).splitlines(keepends=True),
            json.dumps(actual, indent=2, sort_keys=True).splitlines(keepends=True),
            fromfile=f"{expected_label}/{name}",
            tofile=f"{actual_label}/{name}",
        )
    )
