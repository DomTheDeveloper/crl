import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_transition_orbits import audit


def test_s76_transition_orbits():
    report = audit()
    assert report["PASS"]
    assert report["deficit"] == 8
    assert report["raw_supports"] == 1_447_530
    assert report["row_swap_normal_forms"] == 164_535
    assert report["skeleton_orbits"] == 105
    assert report["raw_matching_completions"] == 11_872
    assert report["completed_transition_orbits"] == 701
    assert report["representatives_bytes"] == 111_804
    assert (
        report["representatives_sha256"]
        == "802dd82ae32a7e43549d742a176778fd1f2fd55b8001d5f102eaf30b8c9a692c"
    )
