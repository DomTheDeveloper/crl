import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s84_survivor_geometry_audit import audit


def test_s84_survivor_geometry():
    report = audit()
    assert report["PASS"]
    assert report["surviving_supports"] == 30
    assert report["identity_holonomies_per_support"] == 7
    assert report["double_transposition_holonomies_per_support"] == 42
    assert report["transposition_holonomies_per_support"] == 56
    assert report["four_cycle_holonomies_per_support"] == 0
