import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s84_conjugacy_filter_audit import audit


def test_s84_conjugacy_filter():
    report = audit()
    assert report["PASS"]
    assert report["surviving_supports"] == 30
    assert report["surviving_support_weight"] == 56
    assert report["surviving_class_assignment_is_unique"]
    assert report["local_conjugacy_rules"]["allowed_ordered_local_triples"] == 456
    assert report["support_filter"] == {
        "(0, False, 105, 0, 105, 0)": 1,
        "(48, False, 14, 13, 3, 0)": 105,
        "(56, False, 1, 0, 0, 0)": 120,
        "(56, True, 8, 8, 0, 1)": 30,
    }
