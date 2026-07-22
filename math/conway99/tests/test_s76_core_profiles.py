import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_core_profiles import audit


def test_s76_core_profiles():
    report = audit()
    assert report["PASS"]
    assert report["completed_transition_orbits"] == 701
    assert report["labelled_intact_masks"] == 64
    assert report["S7_intact_core_orbits"] == 41
    assert report["branch_intact_fiber_histogram"] == {
        "13": 163,
        "14": 190,
        "15": 164,
        "16": 111,
        "17": 59,
        "18": 14,
    }
    assert report["core_orbit_intact_fiber_histogram"] == {
        "13": 9,
        "14": 11,
        "15": 11,
        "16": 2,
        "17": 6,
        "18": 2,
    }
    assert report["minimum_closed_KG_edges"] == 0
    assert report["maximum_closed_KG_edges"] == 43
    assert (
        report["profiles_sha256"]
        == "0bb5b5453b83ca49e27027b227d1ca271475021bc75ed15d1eee19cad54f0e96"
    )
