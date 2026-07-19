# Internal release checklist

Nothing in this checklist authorizes external contact or submission.

## Proof branch

- [ ] Clean PR #63 CI completes successfully on the exact head commit.
- [ ] Review the axiom-audit output and archive it.
- [x] Correct the explanatory comment in `N6Base.lean`: the displayed quadratic family has normalized value `47/5` at `n=6` and therefore does not exclude nine points. The theorem code is unchanged.
- [ ] Merge PR #63 only after the author approves.

## Publication branch

- [x] Main manuscript compiles locally without LaTeX or box warnings.
- [x] All nine PDF pages rendered and visually inspected at 200 DPI.
- [x] Exact quadratic formulas checked for `m = 1..100`.
- [x] `6 x 6` enumeration checksum recorded.
- [x] Exceptional thin `7 x 7` certificate independently checked.
- [x] Title and San Diego State University affiliation applied consistently.
- [x] Related-work discussion expanded and all 15 references audited.
- [x] Standard generative-AI declaration added at the end of the paper, with GPT-5.6 Thinking identified in the final sentence.
- [x] E-JC and arXiv internal checklists prepared.
- [x] Technical-review email remains a repository draft only.
- [ ] Publication PR CI completes and its PDF artifact is inspected.
- [ ] A second person or the author completes `HUMAN_REVIEW_CHECKLIST.md`.
- [ ] Author approves final email, department wording, ORCID, and licensing.
- [ ] Create a versioned GitHub release from the exact proof and paper commits.
- [ ] Archive the release on Zenodo or another long-term repository and insert the DOI.
- [ ] Repeat the prior-art and citation search on the release date.

## External actions requiring explicit author approval

- [ ] Send the technical-review email.
- [ ] Request arXiv endorsement.
- [ ] Submit to arXiv.
- [ ] Submit to a journal.
- [ ] Announce the result publicly.
