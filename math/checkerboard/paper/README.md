# Publication package

This directory contains a concise manuscript and independent finite verifier for the theorem

\[
D_{\mathrm{mono}}(n)\le 2n-4\qquad(n\ge6).
\]

## Files

- `checkerboard-2n4.tex` - publication manuscript.
- `checkerboard-2n4.pdf` - rendered manuscript.
- `verify_small_cases.py` - exact standard-library verification of the `n=6` base cases and the exceptional thin `n=7` certificate.
- `REPRODUCIBILITY.md` - theorem, commit, toolchain, workflow, and axiom-audit record.
- `EMAIL_TO_PRELLBERG.md` - technical-review outreach draft.
- `ARXIV_METADATA.md` - proposed submission metadata and scope language.

## Build

```bash
latexmk -pdf checkerboard-2n4.tex
python3 verify_small_cases.py
```

## Claim discipline

The manuscript proves the all-`n` upper bound. It does not claim exact values for every board size or the conjectured all-slope asymptotic equality.
