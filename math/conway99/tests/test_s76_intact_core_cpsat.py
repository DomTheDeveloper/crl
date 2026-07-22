import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_intact_core_cpsat import (
    build_model,
    intersecting_path_tuples,
    local_holonomy_tuples,
)


def test_s76_local_tables():
    assert len(local_holonomy_tuples()) == 456
    for left_position in (0, 1):
        for right_position in (0, 1):
            assert len(intersecting_path_tuples(left_position, right_position)) == 35_280


def test_s76_intact_core_model_dimensions():
    model, context, metadata = build_model(0)
    assert model is not None
    assert len(context["intact"]) == 15
    assert metadata == {
        "profile_index": 0,
        "profile": context["profile"],
        "intact_fibers": 15,
        "edge_variables": 102,
        "intact_disjoint_edges": 48,
        "intact_intersecting_pairs": 57,
        "holonomy_variables": 144,
        "three_path_variables": 144,
        "six_path_variables": 342,
    }
