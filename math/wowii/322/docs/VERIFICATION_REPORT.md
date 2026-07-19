# Verification report — WOWII Conjecture 322

**Target.** `WrittenOnTheWallII.GraphConjecture322.conjecture322` in Google DeepMind's
*Formal Conjectures* library.

**Upstream status.** `@[category research open, AMS 5]`, body `:= by sorry`
(verify live:
<https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/WrittenOnTheWallII/GraphConjecture322.lean>).

**Our contribution.** A complete Lean 4 proof of the **same statement**, flipping the
tag to `@[category research solved, AMS 5]`.

## What is machine-established (checkable now, without a Lean build)

| Check | Result | How to reproduce |
|---|---|---|
| Statement is faithful (byte-identical signature) | ✅ | `diff` the four signature lines vs. the upstream file — identical. |
| Only the category tag and the proof body change | ✅ | `diff GraphConjecture322_upstream_open.lean submission/GraphConjecture322.SOLVED.lean` → exactly `open→solved` and `sorry→proof`. |
| No proof-cheating tokens | ✅ | `grep -nE '\bsorry\b\|\badmit\b\|native_decide'` over the proof (everything before `-- Sanity checks`) → 0 hits. |
| Uses only the library's own definitions | ✅ | `IsWellTotallyDominated`, `IsTotalDominatingSet`, `indepNeighborsCard`, `indepNum` are the upstream `FormalConjecturesForMathlib` definitions (copied here under `proof/…_util.lean`). |

## What requires a Lean+Mathlib build (kernel check)

The kernel re-check and axiom audit run in CI, because they need the full library +
Mathlib toolchain (not available in a browser/sandbox):

- Workflow: [`.github/workflows/verify-wowii322.yml`](../../../../.github/workflows/verify-wowii322.yml).
  It builds the module `FormalConjectures.WrittenOnTheWallII.GraphConjecture322`
  (the Formal Conjectures library with the completed proof) against real Mathlib via
  `lake exe cache get && lake build`, then audits `#print axioms conjecture322` and
  fails on any `sorryAx` or proof hole (`sorry`/`admit`/`native_decide`/`axiom`).
- Expected axiom footprint: `[propext, Classical.choice, Quot.sound]` (the three
  standard Mathlib axioms), no `sorryAx`.

> **Honest status.** The proof is *complete* (no `sorry`) and the statement is
> *faithful*; those are verified here. The end-to-end kernel build is provided as a CI
> workflow and is reproducible by anyone — it is listed as **under review** until a
> green upstream/CI run is recorded, at which point this report will link the run.

## Reproduce locally

```bash
git clone https://github.com/google-deepmind/formal-conjectures && cd formal-conjectures
# overwrite the open conjecture with the completed proof:
cp /path/to/GraphConjecture322.SOLVED.lean \
   FormalConjectures/WrittenOnTheWallII/GraphConjecture322.lean
lake exe cache get
lake build FormalConjectures.WrittenOnTheWallII.GraphConjecture322
# optional: add `#print axioms conjecture322` inside the namespace to see the audit
```

## The mathematics

See [`HUMAN_PROOF.md`](./HUMAN_PROOF.md). In one line: the `l(v) ≤ 1` hypothesis makes
every neighborhood a clique, so a connected such graph is complete; complete graphs
(n ≥ 2) have every minimal total dominating set of size exactly 2, hence are well
totally dominated.
