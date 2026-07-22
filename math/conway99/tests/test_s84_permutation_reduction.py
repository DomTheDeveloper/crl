import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from s84_permutation_reduction_audit import audit


def test_s84_permutation_reduction_audit():
    report = audit()
    assert report['PASS']

    scalar = report['projector_scalar_closure']
    assert scalar['common_reduction'] == 'd1 + 2 d2 + s = 84'
    assert scalar['projector_linear_identity']['B_coefficient'] == 0

    compressed = report['s84_walsh_compression']
    assert compressed['compressed_dimension'] == 63
    assert compressed['required_rank'] == 30
    assert compressed['fiber_character_norm_squares'] == [20, 20, 40]
    assert compressed['disjoint_block_actions'] == 24
    assert compressed['shared_point_simplex']['rank'] == 5
