import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_exceptional_symmetry_audit import audit


def test_s76_exceptional_support_symmetry_quotient():
    report = audit()
    assert report["PASS"]
    assert report["path_compatible_supports"] == 101
    assert report["support_orbits"] == 16
    assert report["F3_parameter_classes"] == [0, "nonzero"]
    assert report["canonical_quotient_lift_cases"] == 32
    first, second = report["exceptional_profiles"]
    assert first["core_mask_stabilizer_order"] == 12
    assert first["support_orbits"] == 7
    assert first["canonical_quotient_lift_cases"] == 14
    assert second["core_mask_stabilizer_order"] == 8
    assert second["support_orbits"] == 9
    assert second["canonical_quotient_lift_cases"] == 18
