# Conway's 99-graph: exact computational campaign

This directory treats Conway's problem as the existence of an
`SRG(99,14,1,2)`. No timeout, heuristic score, partial shard, unverified solver
message, or unchecked symmetry assumption is interpreted as a proof.

## Exact root reduction

Fix a root vertex. Its 14 neighbors induce seven disjoint edges. Every one of
the remaining 84 vertices is uniquely labelled by a non-edge of this matching.
The unknown graph is therefore a symmetric Boolean graph `B` on the 84
non-edges of `7 K2` satisfying

```text
X B = 2 J - X - P X,
B^2 + B + X^T X = 12 I + 2 J.
```

The scripts reconstruct and check the full 99-by-99 adjacency matrix.

## Verification lanes

- `src/sat.py` and `src/cpsat.py`: independent complete encodings;
- `src/verify.py` and `src/verify_matrix.py`: independent witness checkers;
- `src/verify_projectors.py`: transition/triangle and projector verifier;
- `src/symmetry_audit.py`: five exhaustive root seed orbits;
- `src/deficit_branch_sat.py`: exact fixed-transition branch model;
- `src/drup_check.cpp`: independent deletion-aware DRUP checker;
- `src/audit_search_tree.py`: exact cube-coverage audit.

See `STRUCTURE.md`, `SKELETON.md`, and `DEFICIT_SEARCH.md` for the mathematical
reductions and current certified subcases.

## Reproduction

```bash
python -m pip install -r math/conway99/requirements.txt
pytest -q math/conway99/tests
python math/conway99/src/symmetry_audit.py
python math/conway99/src/structural_audit.py
python math/conway99/src/skeleton_audit.py

g++ -O3 -std=c++17 math/conway99/src/drup_check.cpp -o /tmp/drup_check
```

For any SAT result, run every independent witness verifier. For an UNSAT claim,
retain the exact hashed CNF, a checked proof for every exhaustive leaf, and a
passing coverage manifest.

## Current status

The complete problem remains open in this campaign. Checked deficit
certificates eliminate overlap values `s=77,78,80`; elementary exact arguments
eliminate `s=79,81,82,83`. The old `s=84` specialized hash was invalidated by a
constant/variable collision and is being regenerated with typed constants.
Consult `STATUS.md` for the precise live boundary.
