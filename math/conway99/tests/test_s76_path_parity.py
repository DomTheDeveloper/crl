import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_path_parity_audit import audit


def test_s76_exceptional_path_parity_reduction():
    report = audit()
    assert report["PASS"]
    assert report["class_compatible_supports"] == 275
    assert report["path_compatible_supports"] == 101
    assert report["exceptional_transition_orbits"] == 6
    first, second = report["exceptional_profiles"]
    assert first["profile_index"] == 39
    assert first["edge_gauge_dimension"] == 20
    assert first["path_compatible_supports"] == 51
    assert first["distinct_path_weight_profiles"] == 51
    assert second["profile_index"] == 40
    assert second["edge_gauge_dimension"] == 20
    assert second["path_compatible_supports"] == 50
    assert second["distinct_path_weight_profiles"] == 50
