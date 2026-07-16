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

## Independent lanes

- `src/cpsat.py`: OR-Tools CP-SAT encoding.
- `src/sat.py`: DIMACS/PySAT encoding with proof-trace support.
- `src/verify.py`: direct combinatorial verifier.
- `src/verify_matrix.py`: independent integer-matrix verifier.
- `src/symmetry_audit.py`: exhaustive proof that five seed branches cover all
  121 admissible special-neighbor choices under the full seed stabilizer.
- `src/rup_check.py`: independent RUP-only proof checker for regression traces.
- `src/audit_search_tree.py`: verifies exact binary cube coverage; it refuses
  incomplete leaves and requires hashes and checked proofs.

## Reproduction

```bash
python -m pip install -r math/conway99/requirements.txt
pytest -q math/conway99/tests
python math/conway99/src/symmetry_audit.py
python math/conway99/src/make_regressions.py --out /tmp/conway99-regressions

# Complete CNF for one exhaustive seed orbit. Emission is not a solve.
python math/conway99/src/sat.py --k 14 --mode full --branch A1 \
  --cnf /tmp/conway99-A1.cnf --no-solve

# Bounded exploratory CP-SAT run. UNKNOWN is no result.
python math/conway99/src/cpsat.py --k 14 --mode root --branch A1 \
  --seconds 300 --workers 8
```

A SAT result is accepted only after **both** witness verifiers succeed. An
UNSAT claim is accepted only when every exhaustive branch/cube has a proof
checked against the exact hashed CNF and the coverage manifest passes.
