# WOWII Graph Conjecture 322

## Statement

Let `G` be a finite connected simple graph with at least five vertices. Suppose that for every vertex `v`, the independence number of the graph induced by the open neighborhood `N(v)` is at most one. Then `G` is well totally dominated: all minimal total dominating sets have the same cardinality.

## Proof

First observe that every open neighborhood is a clique. Indeed, let `u` and `w` be distinct neighbors of a vertex `v`. If `u` and `w` were nonadjacent, then `{u,w}` would be an independent two-element subset of the induced graph `G[N(v)]`, contradicting `α(G[N(v)]) ≤ 1`.

We next show that `G` is complete. Let `x` and `y` be distinct vertices. Since `G` is connected, there is a walk from `x` to `y`. Repeatedly apply the preceding observation: whenever consecutive edges `a—b` and `b—c` occur with `a ≠ c`, the endpoints `a` and `c` must also be adjacent because both lie in `N(b)`. Induction on the walk therefore gives `x—y`. Thus every distinct pair of vertices is adjacent, and `G` is complete.

It remains to classify the minimal total dominating sets of a complete graph. A total dominating set must contain at least two vertices, since a vertex is not adjacent to itself. Conversely, every pair of distinct vertices totally dominates a complete graph: each member of the pair is adjacent to the other, and every outside vertex is adjacent to both. Therefore a total dominating set with more than two vertices cannot be minimal, because it contains a totally dominating pair. Hence every minimal total dominating set has cardinality exactly two.

Thus `G` is well totally dominated.

## Stronger form

The lower bound of five vertices is not used. The same proof works for every connected graph for which the theorem's hypotheses are meaningful; the local independence condition forces the graph to be complete.

## Formal verification

The accompanying Lean file proves the exact theorem statement from Google DeepMind's Formal Conjectures repository without changing its hypotheses or conclusion.
