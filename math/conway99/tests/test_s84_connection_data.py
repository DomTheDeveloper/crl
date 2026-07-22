import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s84_connection_data import audit


def test_s84_connection_data():
    report = audit()
    assert report["PASS"]
    assert report["support_weight"] == 56
    assert report["support_orbit_size"] == 30
    assert report["edge_parity_weight"] == 40
    assert report["F3_nullity"] == 1
    assert report["connections"] == [
        {"parameter": 0, "odd_edges": 40, "nonzero_C3_edges": 0},
        {"parameter": 1, "odd_edges": 40, "nonzero_C3_edges": 40},
        {"parameter": 2, "odd_edges": 40, "nonzero_C3_edges": 40},
    ]
