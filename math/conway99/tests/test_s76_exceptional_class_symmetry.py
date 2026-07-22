import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_exceptional_class_symmetry_audit import audit


def test_s76_exceptional_class_symmetry_quotient():
    report = audit()
    assert report["PASS"]
    assert report["support_orbits"] == 16
    assert report["raw_class_assignments_on_support_representatives"] == 34
    assert report["support_class_orbits"] == 30
    assert report["F3_parameter_classes"] == [0, "nonzero"]
    assert report["canonical_full_quotient_cases"] == 60
    first, second = report["exceptional_profiles"]
    assert first["support_class_orbits"] == 19
    assert first["canonical_full_quotient_cases"] == 38
    assert second["support_class_orbits"] == 11
    assert second["canonical_full_quotient_cases"] == 22
