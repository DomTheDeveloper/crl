# External review protocol

## Immutable audit target

Reviewers must identify the exact commit audited.

The current corrected analytical review target is:

- branch: `review/bernstein-obstacle-v2-corrected`;
- commit: `f2bd41f19ff5afbcca8a23f9afdcdf084364dae4`;
- correction PR: #106.

The superseded v1 target remains available only for provenance:

- branch: `review/bernstein-obstacle-v1`;
- commit: `209460f762b24d05534075424a5a3864cc5edb9c`.

The moving research branch `agent/bernstein-obstacle-research` is not an
immutable external-review target. Any later formalization commit must receive a
new frozen SHA and a new report or explicit delta review before it can inherit
an external verdict.

## Reviewer qualification gate

A report counts as a qualified external review only when the reviewer supplies
public evidence of relevant research-level competence for the panel being
assessed. Acceptable evidence includes publications, a doctoral or postdoctoral
research profile, substantial professional finite-element/variational-analysis
work, recognized Lean/mathlib contributions, or another comparably verifiable
technical record.

Panel-specific minimum expertise:

- Panel A: approximation theory, Bernstein/Bézier methods, or obstacle/contact
  discretization and prior-art analysis;
- Panel B: Sobolev spaces, conforming finite elements, variational inequalities,
  Mosco convergence, or convex minimization;
- Panel C: free-boundary regularity, obstacle/contact mechanics, a priori FEM
  error analysis, or multiplier estimates;
- Panel D: Lean/mathlib proof auditing and enough mathematical background to
  compare formal statements with the manuscript.

A reviewer may cover more than one panel, but the report must state the evidence
supporting qualification for each panel. Repository-owner reviews, automated
agent output, and anonymous reports without a verifiable technical profile do
not satisfy this gate.

## Required reviewer identity and conflict statement

A valid external report must include:

- reviewer name and professional affiliation or public mathematical profile;
- GitHub account used to submit the report;
- relevant expertise and the qualification evidence above;
- disclosure of collaboration, competition, prior coauthorship, financial
  interest, or other material conflicts with the author or closest predecessor
  authors;
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
8. attach calculations or code for every claimed counterexample;
9. identify any step that is represented only by an abstract Lean interface
   rather than a concrete physical Sobolev/FEM construction.

## Formal-verification report requirements

For Lean review, report:

- pinned Lean and mathlib revisions;
- audited commit SHA;
- exact build commands;
- theorem names checked;
- complete `#print axioms` output;
- confirmation of no `sorry`, `sorryAx`, unsafe declarations, or project axioms;
- a manuscript-to-Lean correspondence table;
- every manuscript claim not represented by a faithful Lean theorem;
- whether any physical mesh, affine pullback, Sobolev-density, interpolation, or
  PDE coercivity hypothesis remains supplied as an assumption to an abstract
  interface.

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

A report on the corrected v2 analytical target does not automatically certify
later moving-branch changes. Conversely, a Lean build of an abstract recovery
interface does not by itself prove the physical Sobolev/FEM hypotheses used to
instantiate that interface.
