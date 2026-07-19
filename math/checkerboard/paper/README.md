# Publication package

This directory contains a concise manuscript and independent verification material for the theorem

\[
D_{\mathrm{mono}}(n)\le 2n-4\qquad(n\ge6).
\]

## Files

- `checkerboard-2n4.tex` - publication manuscript.
- `verify_small_cases.py` - exact standard-library verification of the `n=6` base cases and the exceptional thin `n=7` certificate.
- `verify_quadratic_certificates.py` - exact-arithmetic cross-check of point coverage, line sums, certificate costs, and strict threshold gaps.
- `REPRODUCIBILITY.md` - theorem, commit, toolchain, workflow, and axiom-audit record.
- `PRIOR_ART_AUDIT.md` - novelty search and claim boundary.
- `EMAIL_TO_PRELLBERG.md` - technical-review outreach draft.
- `ARXIV_METADATA.md` - proposed submission metadata and scope language.
- `EJC_COVER_LETTER.md` - journal cover-letter draft.

The paper workflow runs both independent checkers, compiles `checkerboard-2n4.pdf`, and uploads it as a GitHub Actions artifact.

## Build

```bash
python3 verify_small_cases.py
python3 verify_quadratic_certificates.py
latexmk -pdf checkerboard-2n4.tex
```

## Claim discipline

The manuscript proves the all-`n` upper bound. It does not claim exact values for every board size or the conjectured all-slope asymptotic equality.
