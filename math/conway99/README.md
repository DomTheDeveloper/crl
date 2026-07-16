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

## Stronger structural layer

`STRUCTURE.md` derives and audits additional exact consequences:

- `Spec(B)=12^1,(-2)^6,0^7,3^40,(-4)^30`;
- the selected edges split into an 84-edge transition 2-factor and 420
  disjoint-label edges decomposed into 140 edge-disjoint triangles;
- every reduced neighborhood is `5 K2 + 2 isolated vertices`;
- seven perfect matchings couple the stars of the fixed matching pairs;
- exactly 11 adjacent-pair local types occur;
- two integral positive-semidefinite matrices have fixed ranks 30 and 40;
- the full triangle graph has spectrum `18^1,7^54,0^44,(-3)^132`.

These are necessary constraints, not a solution.

## Independent lanes

- `src/cpsat.py`: OR-Tools CP-SAT encoding.
- `src/sat.py`: DIMACS/PySAT encoding with proof-trace support.
- `src/hypergraph_cpsat.py`: necessary transition/triangle relaxation.
- `src/verify.py`: direct combinatorial verifier.
- `src/verify_matrix.py`: independent integer-matrix verifier.
- `src/verify_projectors.py`: independent projector and decomposition verifier.
- `src/structural_audit.py`: executable finite-count and eigenspace audit.
- `src/symmetry_audit.py`: exhaustive proof that five seed branches cover all
  121 admissible special-neighbor choices under the full seed stabilizer.
- `src/rup_check.py`: independent RUP-only proof checker for regression traces.
- `src/audit_search_tree.py`: verifies exact binary cube coverage; it refuses
  incomplete leaves and requires hashes and checked proofs.

## Reproduction

```bash
python -m pip install -r math/conway99/requirements.txt
pytest -q math/conway99/tests
python math/conway99/src/structural_audit.py
python math/conway99/src/symmetry_audit.py
python math/conway99/src/make_regressions.py --out /tmp/conway99-regressions

# Complete CNF for one exhaustive seed orbit. Emission is not a solve.
python math/conway99/src/sat.py --k 14 --mode full --branch A1 \
  --cnf /tmp/conway99-A1.cnf --no-solve

# Strong necessary relaxation. FEASIBLE is not a Conway witness; UNKNOWN is no result.
python math/conway99/src/hypergraph_cpsat.py --branch A1 \
  --seconds 300 --workers 8
```

A SAT result is accepted only after all independent witness verifiers succeed.
An UNSAT claim is accepted only when every exhaustive branch/cube has a proof
checked against the exact hashed CNF and the coverage manifest passes.
