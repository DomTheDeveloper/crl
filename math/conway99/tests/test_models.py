import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from model import make_root_model, SEED_BRANCHES
from verify import verify_reduced
from verify_matrix import verify_matrix
from cpsat import solve
from sat import build_cnf
from pysat.solvers import Solver
from symmetry_audit import audit
from rup_check import check as rup_check

def test_counts_and_equations():
    p = make_root_model(4)
    assert p.v == 9 and p.m == 4
    c = make_root_model(14)
    assert c.v == 99 and c.m == 84
    assert all(len(c.incidence[i]) == 12 for i in range(14))
    assert all(sum(c.rhs_incidence(u, i) for i in range(14)) == 24 for u in range(84))

def test_seed_symmetry_orbits():
    result = audit()
    assert result["PASS"]
    assert result["orbit_count"] == len(SEED_BRANCHES) == 5
    assert result["orbit_sizes"] == [1, 10, 10, 20, 80]

def test_paley9_cpsat(tmp_path):
    out = tmp_path / "p9.json"
    solve(4, "full", 10, 1, None, str(out), False)
    assert out.exists()
    d = json.loads(out.read_text())
    edges = [tuple(e) for e in d["edges"]]
    verify_reduced(make_root_model(4), edges)
    verify_matrix(4, edges)

def test_paley9_sat(tmp_path):
    rm, cnf, edge_vars, _ = build_cnf(4, "full")
    with Solver(name="cadical195", bootstrap_with=cnf.clauses) as solver:
        assert solver.solve()
        pos = {x for x in solver.get_model() if x > 0}
    edges = [uv for uv, var in edge_vars.items() if var in pos]
    verify_reduced(rm, edges)
    verify_matrix(4, edges)

def test_small_rup_certificate(tmp_path):
    rm, cnf, edge_vars, _ = build_cnf(4, "full")
    for v in range(1, rm.m):
        cnf.append([-edge_vars[(0, v)]])
    cnf_path = tmp_path / "u.cnf"
    proof_path = tmp_path / "u.drup"
    cnf.to_file(str(cnf_path))
    with Solver(name="cadical195", bootstrap_with=cnf.clauses, with_proof=True) as solver:
        assert not solver.solve()
        proof = solver.get_proof()
        assert proof
        proof_path.write_text("\n".join(proof) + "\n")
    assert rup_check(str(cnf_path), str(proof_path))["PASS"]
