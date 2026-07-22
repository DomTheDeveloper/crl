import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s84_elimination_audit import audit


def test_s84_elimination_audit():
    report = audit()
    assert report["PASS"]
    assert report["branch"] == "s=84"
    assert report["status"] == "ELIMINATED"
    assert report["curvature_supports_before_conjugacy_filter"] == 256
    assert report["surviving_support_orbit_size"] == 30
    assert report["surviving_quotient_parameters"] == 3
    assert report["parameters_eliminated_by_propagation"] == [0, 2]
    assert report["parameter_eliminated_by_xor_certificate"] == 1
    assert report["xor_certificate_rows"] == 54
    assert report["current_global_implication"] == "Every putative Conway graph has s <= 76."
