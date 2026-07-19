# Build status

## Local publication audit

Completed on 19 July 2026:

- `verify_small_cases.py`: pass.
  - `6 x 6`, parity 0: zero feasible nine-subsets; 155 feasible eight-subsets.
  - `6 x 6`, parity 1: zero feasible nine-subsets; 155 feasible eight-subsets.
  - thin `7 x 7`: point coverage in `{3,4}` and capacity-two cost `32 < 33`.
- `verify_quadratic_certificates.py`: pass for both parity classes and `m = 1..100` using exact rational arithmetic.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error checkerboard-2n4.tex`: pass.
- LaTeX log: no LaTeX, package, overfull-box, or underfull-box warnings.
- PDF preflight: 9 pages, openable, unencrypted, text-based.
- Visual inspection: all nine pages rendered at 200 DPI; no clipping, overlap, black boxes, or broken glyphs found.
- Acknowledgments now precede the references and include a brief, subordinate AI-assisted-preparation note.

## Lean audit

A complete Lean proof package exists for `Checkerboard.checkerboard_upper_all_n`, together with an explicit `#print axioms` audit module. A prior focused checker run was reported as passing, but a fresh exact-head verification has not yet been completed and archived. The current publication branch changes only explanatory material inside the Lean proof tree; theorem terms are unchanged.

## Workflow queue cleanup

The stale checkerboard-specific workflow runs attached to PRs #63 and #68 were cancelled on 19 July 2026. The expensive Lean workflows are restored to manual-only operation. Two older general repository-wide Lean runs remain queued because they were created before that workflow had a concurrency group; they require direct run cancellation rather than another proof build.
