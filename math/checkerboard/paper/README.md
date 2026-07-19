# Publication package

This directory contains a self-contained manuscript and independent verification material for the theorem

\[
D_{\mathrm{mono}}(n)\le 2n-4\qquad(n\ge6).
\]

## Mathematical and computational files

- `checkerboard-2n4.tex` - publication manuscript with the human proof, expanded related work, 15 audited references, exact finite base case, Lean map, data/code statement, and generative-AI declaration.
- `verify_small_cases.py` - exact standard-library verification of the `n=6` base cases and exceptional thin `n=7` certificate. It records the checksum of 155 feasible eight-subsets in each `6 x 6` parity class.
- `verify_quadratic_certificates.py` - exact-arithmetic cross-check of point coverage, line sums, certificate costs, and strict threshold gaps.
- `PROOF_MAP.md` - paper-to-Lean declaration map.
- `REPRODUCIBILITY.md` - theorem, commit, toolchain, workflow, and axiom-audit record.
- `HUMAN_REVIEW_CHECKLIST.md` - line-by-line mathematical review protocol.
- `PRIOR_ART_AUDIT.md` - novelty search and claim boundary.
- `CITATION_AUDIT.md` - source and bibliography verification record.

## Internal publication preparation

- `ARXIV_METADATA.md` - proposed arXiv metadata and scope language.
- `ARXIV_SUBMISSION_CHECKLIST.md` - current internal arXiv requirements and endorsement preparation.
- `EJC_HTML_ABSTRACT.txt` - abstract suitable for the E-JC submission form.
- `EJC_SUBMISSION_CHECKLIST.md` - current internal E-JC requirements.
- `EJC_COVER_LETTER.md` - journal cover-letter draft.
- `EMAIL_TO_PRELLBERG.md` - technical-review outreach draft; keep internal until explicit author approval.
- `RELEASE_CHECKLIST.md` - gates for proof merge, archival release, outreach, and submission.

The paper workflow runs both independent checkers, syntax-checks the Python, compiles `checkerboard-2n4.pdf`, rejects LaTeX and box warnings, and uploads the PDF as a GitHub Actions artifact.

## Build

```bash
python3 verify_small_cases.py
python3 verify_quadratic_certificates.py
latexmk -pdf -interaction=nonstopmode -halt-on-error checkerboard-2n4.tex
```

The current local publication build is nine pages. The title is **Quadratic Line-Cover Certificates and the 2n-4 Bound for Checkerboard No-Three-in-Line Sets**, and the listed affiliation is San Diego State University.

## Claim discipline

The manuscript proves the finite all-`n` upper bound. It does not claim exact values for every board size, the four-direction asymptotic equality, or the true all-slope asymptotic lower bound.
