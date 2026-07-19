# Pull request

**Title:** WOWII Conjecture 322: prove `conjecture322` (`research open` → `research solved`)

**Base:** `google-deepmind/formal-conjectures : main`
**Head:** `DomTheDeveloper/formal-conjectures : wowii322-solved`

**Body:**

Resolves #<ISSUE_NUMBER>.

This fills in the previously-`sorry` theorem
`WrittenOnTheWallII.GraphConjecture322.conjecture322` with a complete proof and
updates its category from `research open` to `research solved`. The proof is short,
so it lives inline (no external `formal_proof` link needed).

**The statement is unchanged** — only the `@[category …]` tag and the proof body differ
from the current file (`sorry` → proof).

### Proof idea

The hypothesis `∀ v, indepNeighborsCard G v ≤ 1` says every open neighborhood has
independence number ≤ 1, i.e. is a clique — so `G` is `P₃`-free (a disjoint union of
cliques). Being connected, `G` is therefore **complete**. In a complete graph on ≥ 2
vertices, a set is a total dominating set iff it has ≥ 2 vertices, so every *minimal*
total dominating set has cardinality exactly 2; hence all minimal TDSs have equal size
and `G` is well totally dominated. (`n ≥ 5` is inherited from the statement; the
argument needs only `n ≥ 2`.)

### Checklist
- [x] Statement byte-identical to the upstream theorem signature
- [x] Only the category tag and proof body change (`diff` = `open→solved`, `sorry→proof`)
- [x] No `sorry` / `admit` / `native_decide` in the proof
- [x] Uses only existing library definitions (`IsWellTotallyDominated`,
      `IsTotalDominatingSet`, `indepNeighborsCard`, `indepNum`)
- [x] `lake build FormalConjectures.WrittenOnTheWallII.GraphConjecture322` succeeds
- [x] `#print axioms conjecture322` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`)

### Verification
- Project page (abstract, human proof, hashes): <https://domthedeveloper.github.io/crl/math/wowii322/>
- Reproducible CI workflow (drops the proof into this repo & builds against Mathlib):
  `.github/workflows/verify-wowii322.yml` in <https://github.com/DomTheDeveloper/crl>
