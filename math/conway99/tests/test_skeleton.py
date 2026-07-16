import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from skeleton_audit import audit as skeleton_audit
from s84_symmetry_audit import audit as symmetry_audit
from s84_cover_sat import build

def test_skeleton_audit():
    r=skeleton_audit();assert r['PASS']
    assert r['F_weighted_degree']==2
    assert r['short_transition_parameter']['excluded_values']==[81,82,83]
    assert r['s84_cover']['cross_blocks']==105

def test_s84_seed_triangle_orbit():
    r=symmetry_audit();assert r['PASS']
    assert r['seed_triangle_candidates']==240 and r['orbit_count']==1

def test_s84_exact_cnf_counts():
    _,cnf,C0,d,meta=build(True)
    assert len(C0)==84 and len(d)==1680
    assert meta['variables']==263457
    assert meta['clauses']==615954
    assert cnf.nv==263457 and len(cnf.clauses)==615954
