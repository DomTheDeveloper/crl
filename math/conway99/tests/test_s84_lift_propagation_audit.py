import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s84_lift_propagation_audit import audit


def test_s84_lift_propagation_audit():
    report = audit()
    assert report["PASS"]
    assert [item["root_consistent"] for item in report["parameter_reports"]] == [
        False,
        True,
        False,
    ]
    assert all(item["variables"] == 1071 for item in report["parameter_reports"])
    assert all(item["constraints"] == 4305 for item in report["parameter_reports"])
    assert report["frame_probes"] == 120
    assert report["forbidden_frame_probes_rejected"] == 80
    assert report["allowed_frame_probes_survive"] == 40
    assert report["forced_common_axis"] == 3
