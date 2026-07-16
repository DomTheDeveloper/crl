import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from s84_burnside_audit import audit

def test_s84_seedstar_burnside_count():
    a=audit()
    assert a['PASS']
    assert a['signed_group_size']==640
    assert a['burnside_fixed_sum']==1095680
    assert a['orbit_count']==1712
