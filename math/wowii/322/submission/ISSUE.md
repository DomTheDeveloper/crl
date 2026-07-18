# Issue to open first

**Title:** WOWII Conjecture 322 (`conjecture322`) has a complete Lean 4 proof — mark solved?

**Body:**

`WrittenOnTheWallII.GraphConjecture322.conjecture322` is currently
`@[category research open, AMS 5]` with `:= by sorry`. I have a complete Lean 4 proof
of **the exact statement** (byte-identical signature), using only the library's own
definitions (`IsWellTotallyDominated`, `IsTotalDominatingSet`, `indepNeighborsCard`,
`indepNum`).

The proof is short (~64 lines), so it fits inline — no external `formal_proof` link
needed.

**Proof idea.** The hypothesis `indepNeighborsCard G v ≤ 1` for all `v` forces every
open neighborhood to be a clique, i.e. `G` is `P₃`-free; a connected `P₃`-free graph is
complete. In a complete graph on ≥ 2 vertices a set totally dominates iff it has ≥ 2
vertices, so every minimal total dominating set has cardinality exactly 2 and `G` is
well totally dominated. (The `n ≥ 5` bound is inherited; `n ≥ 2` suffices.)

**Evidence**
- The proof (no `sorry`/`admit`/`native_decide`), and a diff showing only the
  `open→solved` tag and `sorry→proof` change:
  <https://domthedeveloper.github.io/crl/math/wowii322/>
- Reproducible kernel check: a CI workflow that checks out this repo, installs the
  completed proof, and runs `lake build` + `#print axioms conjecture322` against real
  Mathlib — `.github/workflows/verify-wowii322.yml` in
  <https://github.com/DomTheDeveloper/crl>.

I've signed the CLA and have a PR ready (branch `wowii322-solved` on my fork) — happy to
open it against `main`.
