import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_exceptional_quotient_audit import audit


def test_s76_exceptional_quotient_reduction():
    report = audit()
    assert report["PASS"]
    assert report["path_compatible_supports"] == 101
    assert report["gauge_fixed_quotient_connections"] == 303
    assert report["exceptional_transition_orbits"] == 6
    first, second = report["exceptional_profiles"]
    assert first["profile_index"] == 39
    assert first["F3_variables"] == 84
    assert first["F3_nullity"] == 1
    assert first["gauge_fixed_quotient_connections"] == 153
    assert second["profile_index"] == 40
    assert second["F3_variables"] == 81
    assert second["F3_nullity"] == 1
    assert second["gauge_fixed_quotient_connections"] == 150
