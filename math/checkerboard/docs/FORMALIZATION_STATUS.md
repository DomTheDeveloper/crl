# Lean formalization status

## What the Lean project proves without `sorry`, `admit`, or project-defined axioms

The files under `proofs/lean/Checkerboard/Checkerboard/` formalize:

1. The exact cubic transformation
   `401 α³ - 1744 α² + 2240 α - 768 = -8(401 p³ - 331 p² + 19 p + 7)`
   under `α = 2(1-p)`.
2. The sum/difference square identity used in the master defect-moment argument.
3. The three parity-case contradiction inequalities proving the algebraic end of the finite `2n-4` theorem once the geometric radius bounds and master moment lower bounds are supplied.
4. The exact cubic reductions and positivity certificates used by the strengthened finite ceiling-bound computation.

## What is not yet fully formalized in Lean

The repository does **not** claim a complete Lean formalization of the whole research program. In particular, the following remain paper-level or independently checked by Python/SMT/MIP certificates:

- construction of all checkerboard capacity profiles;
- the full master defect-moment identity from finite sums;
- the capacity-unit majorization used for the ceiling theorem;
- the 35-component exact continuum transport certificate;
- measure smoothing and continuum-to-finite sampling;
- Kahn's bounded-rank edge-colouring theorem and its asymptotic application;
- the final four-direction integral asymptotic theorem;
- the still-open all-slope NTIL lower bound.

No file hides these dependencies behind a Lean `axiom`.

## Build

```bash
cd proofs/lean/Checkerboard
lake update
lake build
```

The project is pinned to Lean and Mathlib `v4.32.0`.
