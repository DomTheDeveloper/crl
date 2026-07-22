import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_linear_quotient_cpsat import (
    build_model,
    quotient_local_tuples,
    quotient_six_path_tuples,
    quotient_table_audit,
)


def test_s76_quotient_tables_are_position_sensitive():
    report = quotient_table_audit()
    assert report["PASS"]
    assert len(quotient_local_tuples()) == 48
    tables = {
        (left, right): set(quotient_six_path_tuples(left, right))
        for left in (0, 1)
        for right in (0, 1)
    }
    assert all(len(table) == 2192 for table in tables.values())
    assert len({frozenset(table) for table in tables.values()}) == 4
    assert report["pairwise_symmetric_differences"] == {
        "00-01": 1024,
        "00-10": 1024,
        "00-11": 722,
        "01-10": 722,
        "01-11": 1024,
        "10-11": 1024,
    }


def test_s76_quotient_model_dimensions():
    model, context, metadata = build_model(0)
    assert model is not None
    assert len(context["intact"]) == 15
    assert metadata["profile_index"] == 0
    assert metadata["edge_variables"] == 102
    assert metadata["intact_disjoint_edges"] == 48
    assert metadata["intact_intersecting_pairs"] == 57
    assert metadata["holonomy_variables"] == 144
    assert metadata["three_path_variables"] == 144
    assert metadata["six_path_variables"] == 342
    assert sum(metadata["position_histogram"].values()) == 57
