import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from s84_cover_sat import build

def test_s84_uses_typed_constants_and_has_correct_size():
    cnf,d,products=build(False)
    assert min(d.values())==1
    assert len(d)==1680
    assert products==65520
    assert cnf.nv==263760
    assert len(cnf.clauses)==616560
