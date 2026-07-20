# External review protocol

## Immutable audit target

Reviewers must identify the exact commit audited. The current campaign target is
PR #95 on `agent/bernstein-obstacle-research`; use the latest successful Lean and
reproduction workflow commits reported in the PR before beginning.

## Required reviewer identity and conflict statement

A valid external report must include:

- reviewer name and professional affiliation or public mathematical profile;
- GitHub account used to submit the report;
- relevant expertise;
- disclosure of collaboration, competition, prior coauthorship, or other
  material conflicts with the author or closest predecessor authors;
- exact commit SHA and artifact checksums reviewed.

## Required verdict format

Return one of:

- `PASS`: the scoped theorem is valid as stated;
- `PASS AFTER CORRECTION`: list every required correction and provide the exact
  strongest corrected theorem;
- `FAIL`: provide a counterexample, invalid inference, prior-art collision, or
  missing hypothesis that defeats the claim.

A negative verdict is a successful audit result when it is specific and
reproducible.

## Mathematical report requirements

The report must:

1. quote the exact theorem and hypotheses being assessed;
2. answer every numbered item in the relevant proof map;
3. distinguish proved steps from imported results;
4. cite or derive every imported result;
5. state whether constants are uniform in mesh size;
6. state all dimension, regularity, boundary, and shape-regularity restrictions;
7. distinguish validity, novelty, and computational usefulness;
8. attach calculations or code for every claimed counterexample.

## Formal-verification report requirements

For Lean review, report:

- pinned Lean and mathlib revisions;
- audited commit SHA;
- exact build commands;
- theorem names checked;
- complete `#print axioms` output;
- confirmation of no `sorry`, `sorryAx`, unsafe declarations, or project axioms;
- a manuscript-to-Lean correspondence table;
- every manuscript claim not represented by a faithful Lean theorem.

## Computational reproduction requirements

Run the one-command workflow in `reproduction/README.md` from a clean checkout.
The reviewer must attach:

- environment and dependency versions;
- `REPRODUCTION_PASS.json`;
- raw CSV/JSON outputs;
- any failures or platform-dependent differences;
- a statement of whether the implementation was modified.

## Signature

Submit the report as a Markdown or PDF artifact and post its SHA-256 digest in
the relevant GitHub issue. A Git commit authored by the reviewer is sufficient
as a public signature; an optional detached GPG/SSH signature may also be
attached.

## Acceptance boundary

No internal report, automated agent output, repository-owner review, or second
implementation written by the same project counts as independent endorsement.
The analytical result reaches externally confirmed status only after qualified
reviewers submit public reports under this protocol.
