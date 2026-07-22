import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from skeleton_audit import audit as skeleton_audit
from s84_symmetry_audit import audit as symmetry_audit
from s84_cover_sat import C0, build


def test_skeleton_audit():
    r = skeleton_audit()
    assert r['PASS']
    assert r['F_weighted_degree'] == 2
    assert r['short_transition_parameter']['excluded_values'] == [81, 82, 83]
    assert r['s84_cover']['cross_blocks'] == 105


def test_s84_seed_triangle_orbit():
    r = symmetry_audit()
    assert r['PASS']
    assert r['seed_triangle_candidates'] == 240
    assert r['orbit_count'] == 1


def test_s84_exact_cnf_counts():
    cnf, d, products = build(True)
    assert len(C0) == 84
    assert len(d) == 1680
    assert products == 65520
    assert cnf.nv == 263760
    assert len(cnf.clauses) == 616563
