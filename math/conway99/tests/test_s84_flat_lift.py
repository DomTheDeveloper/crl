import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from s84_flat_lift_obstruction import audit


def test_flat_s84_holonomy_sector_is_impossible():
    report = audit()
    assert report['PASS']
    assert report['flat_gauge_fixed_S3_connections'] == 3
    assert report['connection_classes'] == {
        'trivial': 1,
        'nontrivial_C3_inverse_pair': 2,
    }
    assert report['trivial_transport_signature']['proper_3_colorings'] == 0
    assert report['nontrivial_transport_signature']['allowed_endpoint_kernel_pairs'] == []
    assert '48 or 56 triangles' in report['consequence']
