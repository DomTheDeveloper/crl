# Written on the Wall II — Graph Conjecture 314

## Exact theorem

Let `G` be a finite, connected, nontrivial, triangle-free graph. If the largest
induced path of `G` has at most four vertices, then every inclusion-minimal total
dominating set of `G` has the same cardinality. Equivalently, `G` is well totally
dominated.

The proof gives the sharper structural classification:

1. the bipartite graphs under the hypotheses are connected chain graphs, and
   every minimal total dominating set has cardinality `2`;
2. the nonbipartite graphs under the hypotheses are nonempty complete blow-ups
   of `C₅`, and every minimal total dominating set has cardinality `3`.

Throughout, an **induced `P₅`** means an induced path on five distinct vertices.
The hypothesis `largestInducedPathSize G ≤ 4` therefore forbids an induced `P₅`.

## 1. Odd-cycle dichotomy

Assume first that `G` is nonbipartite. Choose a shortest odd cycle `C`. A
shortest odd cycle has no chord: a chord divides it into two cycles, exactly one
of which is odd and shorter. Triangle-freeness gives `|C| ≥ 5`. If `|C| ≥ 7`,
then five consecutive vertices of the chordless cycle induce a `P₅`, contrary
to the hypothesis. Hence `C` is an induced `C₅`.

Consequently every graph under the hypotheses is in exactly one of two cases:

- `G` is bipartite;
- `G` contains an induced `C₅`.

The Lean proof formalizes the same dichotomy by coloring vertices according to
the parity of their distance from a fixed root. An edge joining equal parities
would directly produce either a triangle, an induced `C₅`, or an induced `P₅`.

## 2. The bipartite case is a chain graph

Fix a bipartition `A ∪ B`.

### Lemma 2.1: vertices on one side have a common neighbor

Let `a,b` be distinct vertices on the same side. A shortest `a`-`b` path is
induced. It cannot have length at least four, because its first five vertices
would induce a `P₅`. Its length is positive and even, so it is exactly two.
Thus `a` and `b` have a common neighbor on the opposite side.

### Lemma 2.2: neighborhoods on each side are nested

Suppose `a,b` lie on the same side and their neighborhoods are incomparable.
Choose

- `x ∈ N(a) \ N(b)`,
- `y ∈ N(b) \ N(a)`, and
- a common neighbor `c ∈ N(a) ∩ N(b)` from Lemma 2.1.

Then

`x-a-c-b-y`

is an induced `P₅`. The four displayed edges exist. Vertices `x,c,y` lie on one
side and `a,b` on the other, so bipartiteness removes all same-side chords; the
choices of `x` and `y` remove `x-b` and `a-y`. This is a contradiction.
Therefore, for any two vertices on the same side, one open neighborhood is
contained in the other. This is precisely the chain-graph property.

### Lemma 2.3: every minimal total dominating set has size two

Let `S` be an inclusion-minimal total dominating set. Total domination forces
`S` to meet both sides of the bipartition.

We show that `S` contains at most one vertex from each side. Suppose instead
that distinct `a₁,a₂ ∈ S` lie on the same side. By minimality, each `aᵢ` has a
private neighbor `bᵢ`: a vertex adjacent to `aᵢ` and to no other member of `S`.
By Lemma 2.1, `a₁,a₂` have a common neighbor `c`. Then

`b₁-a₁-c-a₂-b₂`

is an induced `P₅`. Indeed, all five required vertices are distinct; the four
path edges exist; bipartiteness removes edges among `b₁,c,b₂` and removes
`a₁a₂`; and privacy removes `b₁a₂` and `a₁b₂`. Contradiction.

Thus `S` has exactly one vertex on each side, so `|S| = 2`. Hence every graph in
the bipartite branch is well totally dominated.

## 3. The nonbipartite case is a nonempty `C₅` blow-up

Let

`C = c₀c₁c₂c₃c₄c₀`

be an induced five-cycle, with indices read modulo five.

### Lemma 3.1: the cycle dominates the graph

Suppose some vertex has distance at least two from `C`, and take a shortest path
to `C`.

If the distance is at least three, the last four vertices of the geodesic,
together with a suitable neighbor of its endpoint on `C`, form an induced
`P₅`. Geodesicity excludes backward chords, and triangle-freeness excludes the
remaining chord through the cycle edge.

If the distance is exactly two, write the path as `x-p-c₀`. Triangle-freeness
forbids `p` from seeing `c₁` or `c₄`, and `p` cannot see both `c₂` and `c₃`,
since those two cycle vertices are adjacent. Therefore at least one of

`x-p-c₀-c₁-c₂`,  `x-p-c₀-c₄-c₃`

is an induced `P₅`. This is again impossible. Hence every vertex has a neighbor
on `C`.

### Lemma 3.2: every vertex belongs to a unique cycle bag

For a vertex `x`, its neighbors on `C` form an independent set, because `G` is
triangle-free. Since the independence number of `C₅` is two, `x` has at most
two cycle neighbors. It cannot have exactly one: if its only cycle neighbor is
`c₀`, then

`x-c₀-c₁-c₂-c₃`

is an induced `P₅`. By Lemma 3.1 it has at least one, so it has exactly two,
and they are nonconsecutive.

Define

`Aᵢ = {x : N(x) ∩ V(C) = {cᵢ₋₁,cᵢ₊₁}}`.

Every vertex belongs to exactly one `Aᵢ`, and `cᵢ ∈ Aᵢ`; hence all five bags are
nonempty.

### Lemma 3.3: the bag adjacencies are exactly those of `C₅`

Each `Aᵢ` is independent: two vertices in the same bag share a cycle neighbor,
so an edge between them would create a triangle.

If `i` and `j` are nonadjacent in the quotient cycle, vertices of `Aᵢ` and
`Aⱼ` share a cycle neighbor, so the two bags are anticomplete by the same
triangle argument.

Finally, consecutive bags are completely joined. Suppose `x ∈ Aᵢ` and
`y ∈ Aᵢ₊₁` are nonadjacent. Then

`x-cᵢ₋₁-cᵢ₋₂-cᵢ₊₂-y`

is an induced `P₅`: the displayed consecutive pairs are edges, and the bag
definitions, the induced-cycle property, and the assumed missing edge exclude
all six chords. Contradiction.

Thus there is a surjection `bag : V(G) → V(C₅)` satisfying

`xy ∈ E(G)  ↔  bag(x)bag(y) ∈ E(C₅)`.

So `G` is exactly a blow-up of `C₅` into five nonempty independent bags, with
complete joins between consecutive bags.

## 4. Minimal total domination in a `C₅` blow-up

Vertices in one bag are false twins: they have identical open neighborhoods.
A minimal total dominating set cannot contain two false twins, because deleting
one leaves every vertex dominated. Therefore a minimal total dominating set
contains at most one representative from each bag.

Its occupied bag indices form an inclusion-minimal total dominating set of the
quotient `C₅`, and conversely domination of representatives is determined
entirely by the quotient.

No two vertices totally dominate `C₅`: a nonadjacent pair does not dominate
itself, while an adjacent pair misses the vertex opposite that edge. On the
other hand, every three consecutive vertices totally dominate `C₅`. Every set
of four or five cycle vertices contains three consecutive vertices and hence
cannot be inclusion-minimal. It follows that every minimal total dominating set
of `C₅` has cardinality three.

Therefore every minimal total dominating set of a nonempty `C₅` blow-up has
cardinality `3`.

## Conclusion

Every graph satisfying the hypotheses is either

- a connected chain graph, whose minimal total dominating sets all have size
  `2`, or
- a nonempty complete blow-up of `C₅`, whose minimal total dominating sets all
  have size `3`.

In either case all inclusion-minimal total dominating sets have equal
cardinality. Therefore `G` is well totally dominated. ∎

## Formalization map

The exact Lean theorem is

```lean
theorem WrittenOnTheWallII.GraphConjecture314.conjecture314_proved
    [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α,
      G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G
```

The modules are ordered as follows:

1. `Core`, `DominatingEdge`, `P5Bridge`, `GeodesicP5` — definitions and the
   exact bridge from the official induced-path invariant;
2. `BipartiteCommon`, `ChainGraph`, `BipartiteClassification` — the chain-graph
   branch and cardinality two;
3. `Cycle5`, `CycleDichotomy`, `C5Embedding`, `C5Dominates`, `C5Bags`,
   `C5BlowupClassification` — the nonbipartite classification;
4. `Cycle5Blowup`, `ConditionalFinal`, `Final` — quotient total domination and
   exact top-level assembly.

The repository workflow checks the proof against pinned Formal Conjectures
commit `b2e608fc52d765510915a244bb69b1a2741acc3c`, rejects explicit `sorry`,
`admit`, `native_decide`, custom `axiom`, and `opaque` declarations, compiles
the final module, verifies the exact upstream theorem type, runs
`#print axioms`, and fails if `sorryAx` appears.
