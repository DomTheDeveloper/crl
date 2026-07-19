# Build status

## Local publication audit

Completed on 18 July 2026:

- `verify_small_cases.py`: pass.
  - `6 x 6`, parity 0: zero feasible nine-subsets; 155 feasible eight-subsets.
  - `6 x 6`, parity 1: zero feasible nine-subsets; 155 feasible eight-subsets.
  - thin `7 x 7`: point coverage in `{3,4}` and capacity-two cost `32 < 33`.
- `verify_quadratic_certificates.py`: pass for both parity classes and `m = 1..100` using exact rational arithmetic.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error checkerboard-2n4.tex`: pass.
- LaTeX log: no LaTeX, package, overfull-box, or underfull-box warnings.
- PDF preflight: 8 pages, openable, unencrypted, text-based.
- Visual inspection: all eight pages rendered at 200 DPI; no clipping, overlap, black boxes, or broken glyphs found.

## Lean audit

The proof-critical source previously passed focused workflow run `29664945600`, including the full pinned build, kernel checking, unfinished-marker guard, and `sorryAx` rejection.

The current publication branch changes only one explanatory comment inside the Lean proof tree; the theorem terms are unchanged.

## Pending CI

GitHub Actions for proof PR #63 and publication PR #68 must complete on their current heads before merge or public release. A queued state is not treated as a mathematical failure.
