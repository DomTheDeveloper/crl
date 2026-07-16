# Written on the Wall II — Graph Conjecture 314

## Theorem

Let `G` be a finite connected nontrivial triangle-free graph. If `G` has no
induced path on five vertices, then all inclusion-minimal total dominating sets
of `G` have the same cardinality. Hence `G` is well totally dominated.

This proves WOWII Graph Conjecture 314, because `largestInducedPathSize G ≤ 4`
is exactly the assertion that `G` is induced-`P5`-free.

## Input theorem

We use the classical theorem of Bacsó and Tuza:

> Every connected `P5`-free graph has a dominating clique or a dominating
> induced `P3`.

In a triangle-free graph, a clique has at most two vertices. A dominating
single vertex together with any incident edge yields a dominating edge.

## Lemma 1: the bipartite case has a dominating edge

Assume `G` is bipartite. If the Bacsó–Tuza set is a clique, we already have a
dominating edge. Otherwise let `a-b-c` be a dominating induced `P3`.

If neither `ab` nor `bc` dominates, choose

- `z` not dominated by `{a,b}`; domination by the `P3` forces `z~c`, and
- `y` not dominated by `{b,c}`; domination by the `P3` forces `y~a`.

Then

`y-a-b-c-z`

is an induced `P5`: bipartiteness removes the same-side chords, and the choices
of `y,z` remove all remaining chords. Contradiction. Thus `G` has a dominating
edge `uv`.

Let the bipartition be `A∪B`, with `u∈A`, `v∈B`. Since `uv` dominates and no
same-side edges exist, `v` is adjacent to every vertex of `A`, and `u` is
adjacent to every vertex of `B`.

Let `S` be an inclusion-minimal total dominating set and write
`S_A=S∩A`, `S_B=S∩B`. Both are nonempty. Suppose `S_A` contains distinct
`a1,a2`. Minimality supplies private neighbors `b1,b2∈B` such that

`N(bi)∩S={ai}`.

Neither `bi` is `v`, and `b1≠b2`. Then

`b1-a1-v-a2-b2`

is an induced `P5`, contradiction. Therefore `|S_A|=1`; symmetrically
`|S_B|=1`. Every minimal total dominating set has size `2`.

## Lemma 2: the nonbipartite case is a nonempty blow-up of C5

Assume `G` is nonbipartite. Let `C` be a shortest odd cycle. It is chordless;
triangle-freeness gives `|C|≥5`, while induced-`P5`-freeness gives `|C|≤5`.
Thus `C=c0c1c2c3c4c0` is an induced `C5`.

### C dominates G

Suppose a vertex has distance at least two from `C`, and take a shortest path
to `C`. If the distance is at least three, the last cycle edge extends four
vertices of the geodesic to an induced `P5`. If the distance is two, write the
path as `x-p-c0`. Triangle-freeness forbids `p` from seeing `c1` or `c4`; at
most one of `c2,c3` can also see `p`. One of

`x-p-c0-c1-c2`, `x-p-c0-c4-c3`

is therefore an induced `P5`. Contradiction. Hence every vertex meets `C`.

### Cycle neighborhoods

For `x∉C`, `N_C(x)` is independent, hence has at most two vertices. It cannot
have size one, because if `N_C(x)={c0}`, then

`x-c0-c1-c2-c3`

is an induced `P5`. Therefore every vertex has exactly two nonconsecutive
neighbors on `C`.

For indices modulo five, define

`A_i={x : N_C(x)={c_{i-1},c_{i+1}}}`,

including `c_i∈A_i`. Each `A_i` is nonempty.

- `A_i` is independent, because two of its vertices share a cycle neighbor.
- Nonconsecutive classes are anticomplete, for the same triangle-free reason.
- Consecutive classes are complete: if `x∈A_i`, `y∈A_{i+1}` were nonadjacent,
  then, after cyclic relabeling,

  `x-c_{i-1}-c_{i-2}-c_{i+2}-y`

  would be an induced `P5`.

Thus `G` is exactly a blow-up of `C5` into five nonempty independent classes,
with complete joins between consecutive classes.

## Lemma 3: every minimal TDS of a nonempty C5 blow-up has size 3

Vertices in the same class `A_i` are false twins. A minimal total dominating
set contains at most one vertex from each class: if it contained two, deleting
one would leave the same class support and hence preserve total domination.

The set of occupied class indices is therefore an inclusion-minimal total
dominating set of the quotient `C5`, and conversely its representatives have
the same domination behavior.

`C5` has no total dominating set of size two. Every three consecutive vertices
form a total dominating set. Every four- or five-vertex set contains three
consecutive vertices and is therefore not minimal. Consequently every minimal
total dominating set of `C5`, and hence of its nonempty blow-ups, has size `3`.

## Conclusion

Every graph under the hypotheses is in exactly one of the following cases:

1. bipartite with a dominating edge — every minimal TDS has size `2`;
2. a nonempty blow-up of `C5` — every minimal TDS has size `3`.

In either case the graph is well totally dominated. ∎

## Computational audit

An independent exhaustive audit of connected triangle-free induced-`P5`-free
unlabeled graphs through ten vertices found 307 graphs:

| n | count |
|---:|---:|
| 2 | 1 |
| 3 | 1 |
| 4 | 3 |
| 5 | 5 |
| 6 | 11 |
| 7 | 19 |
| 8 | 41 |
| 9 | 74 |
| 10 | 152 |

Every bipartite example had minimal total dominating sets uniformly of size 2;
every nonbipartite example was a `C5` blow-up and had them uniformly of size 3.
The computation is corroboration, not a substitute for the proof above.
