# Conway's 99-graph: exact computational campaign

This directory treats Conway's problem as the existence of an
`SRG(99,14,1,2)`. No timeout, heuristic score, partial shard, or unverified
solver message is interpreted as evidence of nonexistence.

## Exact root reduction

Fix a root vertex. Its 14 neighbors induce seven disjoint edges. Every one of
the remaining 84 vertices is uniquely labelled by a non-edge of this matching:
its two neighbors in the root neighborhood. Thus the unknown graph is a graph
`B` on the 84 non-edges of `7 K2`.

Let `X` be the 14-by-84 incidence matrix of those labels and `P` the adjacency
matrix of `7 K2`. A candidate is valid exactly when its symmetric zero-diagonal
Boolean adjacency matrix `B` satisfies

```text
X B = 2 J - X - P X,
B^2 + B + X^T X = 12 I + 2 J.
```

The scripts reconstruct and check the full 99-by-99 adjacency matrix.

## Stronger structural layers

`STRUCTURE.md` derives and audits:

- `Spec(B)=12^1,(-2)^6,0^7,3^40,(-4)^30`;
- an 84-edge transition 2-factor and 140 edge-disjoint disjoint-label triangles;
- exact rank-30 and rank-40 integral projector identities;
- 11 adjacent-pair local types and 12 allowable triangle profiles.

`SKELETON.md` derives a second weighted 2-factor, proves that the overlap
parameter cannot be 81, 82, or 83, and gives a complete 263,457-variable exact
encoding of the extremal `s=84` branch as a four-fold cover of `KG(7,2)`.
These are necessary constraints and exact subcases, not a solution.

## Independent lanes

- `src/cpsat.py`: OR-Tools CP-SAT encoding.
- `src/sat.py`: general DIMACS/PySAT encoding with proof-trace support.
- `src/hypergraph_cpsat.py`: necessary transition/triangle relaxation.
- `src/s84_cover_sat.py`: complete certificate-oriented `s=84` branch CNF.
- `src/verify.py`: direct combinatorial verifier.
- `src/verify_matrix.py`: independent integer-matrix verifier.
- `src/verify_projectors.py`: independent projector and decomposition verifier.
- `src/structural_audit.py`, `src/skeleton_audit.py`: executable audits.
- `src/symmetry_audit.py`, `src/s84_symmetry_audit.py`: exact orbit audits.
- `src/rup_check.py`: independent RUP-only proof checker for regression traces.
- `src/audit_search_tree.py`: strict binary-cube coverage checker.

## Reproduction

```bash
python -m pip install -r math/conway99/requirements.txt
pytest -q math/conway99/tests
python math/conway99/src/structural_audit.py
python math/conway99/src/skeleton_audit.py
python math/conway99/src/symmetry_audit.py
python math/conway99/src/s84_symmetry_audit.py

# Complete general CNF for one exhaustive seed orbit. Emission is not a solve.
python math/conway99/src/sat.py --k 14 --mode full --branch A1 \
  --cnf /tmp/conway99-A1.cnf --no-solve

# Complete extremal-branch CNF.
python math/conway99/src/s84_cover_sat.py --cnf /tmp/conway99-s84.cnf \
  --emit-only
```

A SAT result is accepted only after all independent witness verifiers succeed.
An UNSAT claim is accepted only when every exhaustive branch/cube has a proof
checked against the exact hashed CNF and the coverage manifest passes.
