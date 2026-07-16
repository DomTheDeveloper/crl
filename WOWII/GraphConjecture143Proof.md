# Written on the Wall II — Graph Conjecture 143

## Theorem

For every finite connected nontrivial graph `G` with positive second-smallest
degree,

`girth(G)+1 ≤ tree(G)·σ(G)`,

where `tree(G)` is the largest number of vertices in an induced tree and
`σ(G)` is the second-smallest degree.

## Case 1: G is acyclic

The repository convention gives `girth(G)=0`. Connectedness and nontriviality
give an edge, whose endpoints induce a two-vertex tree. Since `σ(G)>0`,

`girth(G)+1 = 1 ≤ tree(G)·σ(G)`.

## Case 2: G is cyclic and σ(G)≥2

Let `C` be a shortest cycle, of length `g=girth(G)`. A shortest cycle is
chordless. Delete two consecutive edges of `C`, equivalently retain the path
on `g-1` consecutive cycle vertices. Because it has fewer vertices than the
girth, its induced subgraph cannot contain a cycle; it is connected, hence an
induced tree. Therefore

`tree(G) ≥ g-1`.

Since `g≥3` and `σ(G)≥2`,

`tree(G)·σ(G) ≥ 2(g-1) ≥ g+1`.

This branch is already formalized and Lean-green in
`GraphConjecture143Next.lean`.

## Case 3: σ(G)=1

Connectedness implies every degree is positive. If the second-smallest degree
is one, there are two distinct degree-one vertices; call them `x,y`.

Choose, among all induced trees containing `x` and `y`, one with maximum
cardinality, and call its vertex set `S`. Such a tree exists: a shortest
`x-y` path is induced.

Because `G` contains a cycle, `S` is not all of `V(G)`. Connectedness gives a
vertex `z∉S` with a neighbor in `S`.

### z has at least two neighbors in S

If `z` had exactly one neighbor in `S`, adjoining `z` would attach a pendant
vertex to the induced tree `G[S]`. The induced subgraph on `S∪{z}` would still
be a tree, still contain `x,y`, and have larger cardinality, contradicting the
choice of `S`.

Thus `N(z)∩S` has at least two vertices.

Choose distinct `a,b∈N(z)∩S` for which their distance in the tree `G[S]` is
minimum. Let `P` be the unique `a-b` path in that tree. By minimality, no
internal vertex of `P` is adjacent to `z`; otherwise that internal neighbor and
one endpoint would be a closer pair of neighbors of `z`.

Consequently `P` together with `z` is an induced cycle. If `P` has `m` edges,
this cycle has `m+2` edges, so

`m+2 ≥ girth(G)`.

Every vertex of `P` has at least two neighbors in `G`: an internal vertex has
its two path neighbors, while `a,b` each has a path neighbor and the additional
neighbor `z`. Therefore neither degree-one vertex `x` nor `y` lies on `P`.
Both do lie in `S`, so

`|S| ≥ |V(P)|+2 = (m+1)+2 = m+3 ≥ girth(G)+1`.

Hence

`tree(G) ≥ girth(G)+1`.

Since `σ(G)=1`, this is exactly

`girth(G)+1 ≤ tree(G)·σ(G)`.

The three cases exhaust all possibilities. ∎

## Formalization status

The following components compile without `sorry` against the official pinned
Lean/Mathlib toolchain:

- every geodesic induces a tree;
- `dist(u,v)+1 ≤ tree(G)`;
- the acyclic branch;
- paths shorter than the girth induce trees;
- `girth(G)-1 ≤ tree(G)` in cyclic graphs;
- the complete cyclic `σ≥2` branch.

The `σ=1` branch is being decomposed into separately checked finite-selection,
degree-sequence, pendant-extension, and cycle-counting lemmas.
