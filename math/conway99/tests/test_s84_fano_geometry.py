import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s84_fano_geometry_audit import audit


def test_s84_fano_geometry():
    report = audit()
    assert report["PASS"]
    assert report["surviving_support_orbit_size"] == 30
    assert report["survivor_set_equals_generated_S7_orbit"]
    assert report["base_permutations_checked"] == 5040
    assert report["stabilizer_order"] == 168
    assert report["group_order"] == 8
    assert report["group_exponent"] == 2
    assert report["associativity_checks"] == 512
