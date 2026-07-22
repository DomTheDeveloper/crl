import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_curvature_support_audit import audit


def test_s76_curvature_support_reduction():
    report = audit()
    assert report["PASS"]
    assert report["canonical_core_types"] == 41
    assert report["zero_curvature_class_survivors"] == 39
    assert report["zero_curvature_profile_indices"] == list(range(39))
    assert report["exceptional_transition_orbits"] == 6
    assert [item["profile_index"] for item in report["exceptional_profiles"]] == [39, 40]
    assert [item["used_curvature_dimension"] for item in report["exceptional_profiles"]] == [12, 13]
    assert [item["supports_after_class_filter"] for item in report["exceptional_profiles"]] == [99, 176]
