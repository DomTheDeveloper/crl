import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from s76_intact_core_audit import audit


def test_s76_intact_core_audit():
    report = audit()
    assert report['PASS']
    assert report['minimum_intact_fibers'] == 13
    assert report['removed_fiber_subsets_checked'] == 203490
    assert report['induced_KG_edges'] == 33
    assert report['induced_KG_triangles'] == 9
    assert report['minimum_degree'] == 2
    assert report['cycle_rank'] == 21
    assert report['maximum_connected_components'] == 1
