# Internal release checklist

Nothing in this checklist authorizes external contact or submission.

## Proof branch

- [ ] Clean PR #63 CI completes successfully on the exact head commit.
- [ ] Review the axiom-audit output and archive it.
- [x] Correct the explanatory comment in `N6Base.lean`: the displayed quadratic family has normalized value `47/5` at `n=6` and therefore does not exclude nine points. The theorem code is unchanged.
- [ ] Merge PR #63 only after the author approves.

## Publication branch

- [x] Main manuscript compiles locally without LaTeX or box warnings.
- [x] Rendered PDF inspected at 180 DPI.
- [x] Exact quadratic formulas checked for `m = 1..100`.
- [x] `6 x 6` enumeration checksum recorded.
- [x] Exceptional thin `7 x 7` certificate independently checked.
- [x] E-JC and arXiv internal checklists prepared.
- [x] Technical-review email remains a repository draft only.
- [ ] Publication PR CI completes and its PDF artifact is inspected.
- [ ] A second person or the author completes `HUMAN_REVIEW_CHECKLIST.md`.
- [ ] Author approves final name, affiliation, email, ORCID, and licensing.
- [ ] Create a versioned GitHub release from the exact proof and paper commits.
- [ ] Archive the release on Zenodo or another long-term repository and insert the DOI.
- [ ] Repeat the prior-art search on the release date.

## External actions requiring explicit author approval

- [ ] Send the technical-review email.
- [ ] Request arXiv endorsement.
- [ ] Submit to arXiv.
- [ ] Submit to a journal.
- [ ] Announce the result publicly.
