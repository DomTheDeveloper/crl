# Verification report: checkerboard `D_mono(n) ≤ 2n - 4`

## Executive summary

The branch `solve/checkerboard-2n4-full` contains:

- a complete human-readable finite defect-moment proof of the exact all-line
  theorem;
- Lean source for the full dependency chain and public theorem
  `Checkerboard.checkerboard_Dmono_le`;
- a deterministic exact finite target enumerator;
- an independently generated all-line MILP corroborator whose incumbents are
  checked with exact integer determinants;
- CI guards for placeholders, custom axioms, compilation, and axiom output.

The decisive formal verification gate is still open: the current pinned Linux
and macOS GitHub Actions jobs have remained queued, so there is not yet a
successful `lake build` or current-commit axiom-audit log.  This report therefore
does not call the Lean theorem verified.

## Claim matrix

| Claim | Human proof | Independent computation | Lean source | Kernel-checked on current commit |
|---|---:|---:|---:|---:|
| integer affine lines are equivalent to Euclidean lines on lattice points | yes | direct determinant checker | predicate documented; four needed consequences formalized | pending build |
| row/column deficit totals are `3` at size `2n-3` | yes | exact enumerator | formalized | pending build |
| each diagonal deficit family has total mass `1` | yes | exact enumerator/MILP | formalized from finite fibers | pending build |
| first-moment bridge identities | yes | symbolic checks | formalized | pending build |
| second-moment bridge identity | yes | symbolic checks | formalized | pending build |
| endpoint/all-double profile moments and radii | yes | exact arithmetic | formalized | pending build |
| four parity contradictions | yes | exact arithmetic | formalized | pending build |
| `D_mono(n) ≤ 2n-4` for every `n≥6` | yes | finite corroboration only | exact theorem present | **not yet established** |

The universal proof does not depend on SAT, MIP, floating point, or a finite
range of checked values.

## Deterministic exhaustive checker

`math/checkerboard/tools/verify_target_exact.py` searches exactly for a
monochromatic no-three-in-line set of the forbidden size `2n-3`.

For each `(n,color)` it:

1. enumerates every row-count vector in `{0,1,2}^n` with total `2n-3`;
2. enumerates every compatible choice of checkerboard points in those rows;
3. rejects a partial choice when a column reaches three points;
4. rejects a partial choice when an exact integer determinant finds a
   collinear triple;
5. accepts `UNSAT` only after the complete finite search space is exhausted.

No randomization, floating-point arithmetic, solver API, or unproved symmetry
reduction is used.  The completed searches recorded during this audit were:

| `n` | color | result | row-count vectors | search nodes |
|---:|---:|---:|---:|---:|
| 6 | 0 | UNSAT | 50 | 1,745 |
| 6 | 1 | UNSAT | 50 | 1,745 |
| 7 | 0 | UNSAT | 77 | 4,802 |
| 7 | 1 | UNSAT | 77 | 2,534 |
| 8 | 0 | UNSAT | 112 | 52,967 |
| 8 | 1 | UNSAT | 112 | 52,967 |
| 9 | 0 | UNSAT | 156 | 152,725 |
| 9 | 1 | UNSAT | 156 | 104,696 |

Reproduction:

```bash
python math/checkerboard/tools/verify_target_exact.py --n-min 6 --n-max 9
```

These finite results are regression tests and independent corroboration, not the
proof for arbitrary `n`.

## Independent all-line MILP corroboration

`math/checkerboard/tools/corroborate_milp.py` constructs all checkerboard points
and all distinct affine lines containing at least three candidate points.  It
then solves the binary model

\[
\max\sum_p x_p,
\qquad
\sum_{p\in L}x_p\le2
\]

for every such line `L`.

The program accepts an optimum only when SciPy/HiGHS returns completed optimal
status `0`.  A timeout, interrupted run, or incumbent without an optimality
certificate raises an error and is reported as no result.  Every returned
optimizer is then rechecked independently by enumerating all triples and using
an exact integer determinant.

Completed optimal solves recorded during this audit were:

| `n` | color 0 optimum | color 1 optimum | theorem bound `2n-4` |
|---:|---:|---:|---:|
| 6 | 8 | 8 | 8 |
| 7 | 10 | 10 | 10 |
| 8 | 12 | 12 | 12 |
| 9 | 14 | 13 | 14 |
| 10 | 15 | 15 | 16 |

Reproduction:

```bash
python -m pip install numpy scipy
python math/checkerboard/tools/corroborate_milp.py \
  --n-min 6 --n-max 10 --time-limit 120
```

These optimizer runs are corroboration only.  No LRAT, FRAT, VeriPB, or exact
MIP dual certificate is claimed for them.

## Mathematical cross-checks

The human proof was independently reconstructed from the finite definitions.
The following exact formulas were checked symbolically:

\[
\sum_{x=0}^{n-1}(2x-(n-1))^2=\frac{n(n^2-1)}3,
\]

\[
D_{\rm end}=\frac{2(n-1)(n^2-2n+3)}3,
\qquad
D_{\rm dbl}=\frac{2n(n-1)(n-2)}3,
\]

and the three master lower bounds

\[
(n-1)(n-2)(n-3),
\quad n(n-1)(n-5),
\quad (n-1)(n^2-5n+3).
\]

At the minimal admissible cases the lower-minus-upper gaps expand as:

- odd endpoint, `n=7+t`: `t^3+13t^2+50t+48`;
- odd all-double, `n=7+t`: `t^3+13t^2+48t+34`;
- even mixed, `n=6+t`: `t^3+10t^2+26t+4`.

All coefficients are nonnegative and the constants are positive.

## Lean verification procedure

The project is pinned to Lean and Mathlib `v4.32.0`.

```bash
cd proofs/lean/Checkerboard
lake update
lake build
! grep -RnE '\bsorry\b|\badmit\b|native_decide' --include='*.lean' .
! grep -RnE '^[[:space:]]*(axiom|constant)[[:space:]]' \
    --include='*.lean' Checkerboard Checkerboard.lean
lake env lean Checkerboard/FinalTheorem.lean
```

The final file contains

```lean
#print axioms Checkerboard.checkerboard_Dmono_le
```

A completed verification requires:

1. zero build errors;
2. no placeholder match in Lean source;
3. no project-defined axiom or constant used as a mathematical assumption;
4. no `sorryAx` in the printed dependency set;
5. successful checking of the current PR head, not an earlier commit.

The CI workflow runs the build and axiom audit independently on Linux and macOS
and uploads both logs.  At the time of this report both hosted jobs are queued,
not failed and not passed.

## Honest public wording before CI completes

> A complete finite human proof and a full Lean source formalization of
> `D_mono(n) ≤ 2n-4` for `n≥6` are present in draft PR #29, with exact finite
> corroboration.  The current pinned Lean build and axiom audit are still
> pending; the theorem should not yet be called formally verified.
