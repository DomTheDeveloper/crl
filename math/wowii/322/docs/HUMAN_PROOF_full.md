# Written on the Wall II — Conjecture 322: a complete proof

**Statement (DeepMind *Formal Conjectures*, `WrittenOnTheWallII.GraphConjecture322`).**
Let `G` be a simple **connected** graph on `n ≥ 5` vertices. For a vertex `v`, let
`l(v) = α(G[N(v)])` be the independence number of the subgraph induced by the open
neighborhood `N(v)`. If `l(v) ≤ 1` for every vertex `v`, then `G` is **well totally
dominated** (every *minimal* total dominating set has the same cardinality).

This note is the human-readable companion to the machine-checked Lean 4 proof
`GraphConjecture322_solved.lean`. The Lean statement is **byte-identical** to the
upstream `research open` theorem; only the proof body (and the `open → solved`
category tag) differ.

---

## 1. The local hypothesis forces every neighborhood to be a clique

`l(v) = α(G[N(v)]) ≤ 1` says the induced subgraph on the open neighborhood of `v`
has **no independent set of size 2**. Equivalently:

> **(★)** For every vertex `x` and every pair of *distinct* neighbors `u, v ∈ N(x)`,
> the edge `uv` is present.

Indeed, if `u, v ∈ N(x)` were non-adjacent, then `{u, v}` would be an independent set
of size `2` inside `G[N(x)]`, giving `α(G[N(x)]) ≥ 2`, contradicting `l(x) ≤ 1`.

*(In the Lean proof this is the lemma `hloc`; the independent pair `{⟨u,·⟩,⟨v,·⟩}` is
built explicitly and `hindep.card_le_indepNum` turns it into `2 ≤ indepNum`, then
`le_trans … (h x)` yields `2 ≤ 1`, a contradiction closed by `omega`.)*

Property (★) is exactly the statement that **`G` has no induced path `P₃`** — it is a
*cluster graph* (a disjoint union of cliques).

## 2. Connected + "every neighborhood a clique" ⟹ `G` is complete

Take any two distinct vertices `u ≠ w`. Since `G` is connected there is a walk from
`u` to `w`. Walk along it and apply (★) repeatedly: adjacency is transitive along a
common neighbor, so distinct endpoints of any walk are adjacent. Hence **every pair of
distinct vertices is adjacent** — `G = Kₙ`, the complete graph.

*(Lean: `hwalk` inducts on the walk — `nil` is impossible for distinct endpoints, and
`cons` uses `hloc b a c` on the shared vertex `b`; `hcomp` then closes it via
`hG.preconnected`.)*

The hypothesis `n ≥ 5` is not needed for this step (any `n ≥ 1` works); it is inherited
from the original conjecture statement.

## 3. Total domination in a complete graph

Work in `Kₙ` with `n ≥ 2` (here `n ≥ 5`). Recall `S` is a *total dominating set* (TDS)
if **every** vertex — including those in `S` — has a neighbor in `S`.

- **Every TDS has `|S| ≥ 2`.** Pick any vertex `v`. A TDS gives a neighbor `w ∈ S` of
  `v` (so `w ≠ v`), and applying the TDS property to `w` gives a neighbor `w' ∈ S` of
  `w` with `w' ≠ w`. Thus `S` contains two distinct vertices `w, w'`. *(Lean: `hTDS_ge`.)*
- **Every set with `|S| ≥ 2` is a TDS.** Given any vertex `v`, at least one of the two
  guaranteed distinct members of `S` differs from `v`, and in `Kₙ` every distinct pair
  is adjacent, so `v` has a neighbor in `S`. *(Lean: `hTDS_of_two`.)*

## 4. Every minimal TDS has cardinality exactly 2

Let `S` be a *minimal* TDS. By §3 it has `|S| ≥ 2`. If `|S| > 2`, choose a subset
`T ⊆ S` with `|T| = 2`; then `T ⊂ S` is proper, and by §3 `T` is still a TDS —
contradicting minimality. Hence `|S| = 2`. *(Lean: `hmin`, via
`Finset.exists_subset_card_eq` and `ssubset_of_ne`.)*

## 5. Conclusion

Any two minimal total dominating sets have cardinality `2`, so they have equal
cardinality. That is precisely `IsWellTotallyDominated G`. ∎

---

### Remarks

- The proof shows something sharper than the conjecture: under the hypothesis the graph
  is *forced* to be complete, and its total domination number is `2`. Well-total-
  domination is then immediate.
- The `n ≥ 5` bound in the original Graffiti.pc conjecture is generous: the argument
  works for every connected graph with `n ≥ 2` satisfying the local hypothesis.
- Nothing in the proof is graph-`n`-specific or uses `decide`/`native_decide` on the
  main theorem; it is a fully general finite-graph argument. The only `decide +native`
  calls are the two upstream `@[category test]` sanity checks about `K₄` and `⊥`.
