import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from structural_audit import audit
from hypergraph_cpsat import build
from verify_projectors import verify

def test_structural_audit():
    r=audit(); assert r['PASS']; assert r['reduced_spectrum']=={'12':1,'-2':6,'0':7,'3':40,'-4':30}
    assert r['adjacent_pair_local_types']['count']==11

def test_hypergraph_model_counts():
    _,model,c,t=build('A1')
    assert len(c)==924 and len(t)==35560
    assert len(model.Proto().variables)>36000

def test_projector_verifier_rejects_empty():
    try:
        verify({'k':14,'edges':[]})
    except AssertionError:
        return
    raise AssertionError('empty graph was accepted')
