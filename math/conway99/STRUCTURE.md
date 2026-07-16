# Exact structural consequences of the root reduction

This document records consequences that every `SRG(99,14,1,2)` must satisfy.
They strengthen the solver model but do **not** settle existence.
`src/structural_audit.py` mechanically checks the finite counts and the joint
eigenspace arithmetic below.

## 1. Canonical 84-vertex graph

Fix a vertex `r`. Its neighborhood is `7 K2`. Write the 14 vertices as
`0,...,13`, with matched pairs `{0,1}`, `{2,3}`, ..., `{12,13}`.

Every vertex outside `r` and its neighborhood has exactly two neighbors in the
14-set. They cannot be a matched pair, and every nonmatching pair occurs once.
Thus the 84 remaining vertices are the edges of

```text
H = K_14 - 7 K_2.
```

Let `X` be the 14-by-84 vertex-edge incidence matrix of `H`, let `P` be the
matching permutation matrix, and let `B` be the unknown adjacency matrix on the
84 labels. The exact equations are

```text
X B = 2 J - X - P X,
B^2 + B + X^T X = 12 I + 2 J.
```

No automorphism of the unknown graph is assumed in this reduction.

## 2. Exact spectrum of B

First,

```text
X X^T = 11 I + J - P.
```

Decompose `R^14` into:

- the all-ones line;
- the six-dimensional pair-constant, sum-zero space;
- the seven-dimensional pair-difference space.

Transposing the first reduced equation gives

```text
B X^T y = X^T ((sum y) 1 - (I + P) y).
```

Therefore `B` has eigenvalues `12`, `-2`, and `0` on the three images, with
multiplicities `1`, `6`, and `7`. The matrix `X` has rank 14. On `ker X`, the
all-ones component vanishes and the second reduced equation becomes

```text
B^2 + B = 12 I.
```

Hence the remaining eigenvalues are `3` and `-4`. Trace zero determines their
multiplicities. The complete spectrum is

```text
Spec(B) = 12^1, (-2)^6, 0^7, 3^40, (-4)^30.
```

## 3. Transition edges and triangle edges

Classify a selected `B`-edge according to its two labels:

- `C`: the labels intersect in one base point;
- `D`: the labels are disjoint.

For a label `u={a,b}`, the incidence equation at `a` says that `u` has exactly
one selected neighbor among the 12 labels containing `a`; the same is true at
`b`. Consequently:

- every `B`-vertex has exactly two `C`-neighbors;
- at each of the 14 base points, `C` is a perfect matching on the 12 incident
  labels;
- `C` is a 2-factor with exactly 84 edges;
- equivalently, `C` is a transition system or circuit decomposition of `H`.

Summing all 14 incidence equations gives degree 12 in `B`, so every vertex has
10 `D`-neighbors and `D` has 420 edges.

An intersecting adjacent pair has zero common `B`-neighbors. It follows that no
triangle can contain a `C`-edge. A disjoint adjacent pair has exactly one common
`B`-neighbor, so every `D`-edge lies in exactly one all-`D` triangle. Thus:

- `D` decomposes into 140 edge-disjoint triangles;
- every label lies in exactly five of those triangles;
- for every `u`, the induced graph on `N_B(u)` is exactly
  `5 K2 + 2 isolated vertices`;
- the isolated vertices are the two `C`-neighbors of `u`.

The reduced graph has 1,071 four-cycles. Indeed, each label is disjoint from 61
others, giving 2,562 disjoint pairs. Of these, 420 are `D`-edges, leaving 2,142
disjoint nonedges. Each such nonedge is an opposite pair of a unique four-cycle,
and each four-cycle has two opposite pairs.

The 231 triangles of the full graph split canonically into

```text
7 root triangles + 84 transition triangles + 140 label-only triangles.
```

## 4. Seven perfect matchings between matched stars

For each base matching pair `{i,i'}`, let `S_i` be the 12 labels containing
`i`. Apply the incidence equation for a label in `S_i` at `i'`. It gives exactly
one `B`-neighbor in `S_i'`. Symmetry gives a perfect matching between the two
12-sets.

Identify both stars with the 12 remaining base points:

```text
{i,a}  -->  {i', phi_i(a)}.
```

This defines a permutation `phi_i` of 12 points. Its fixed points are precisely
the `C`-edges between the stars; its nonfixed points are `D`-edges. These seven
permutations couple the 14 transition matchings and provide a more compact
branching language than arbitrary Boolean edges.

## 5. Eleven exact adjacent-pair local types

Fix the root `r` and one of its neighbors `i`. The induced graph on the union of
their neighborhoods has 27 vertices. Apart from `r`, `i`, and their common
neighbor, it is determined by two perfect matchings on 12 points:

- the six fixed blades inherited from `7 K2`;
- the transition matching at base point `i`.

The union of two perfect matchings is a disjoint union of even cycles. Therefore
the local isomorphism type is determined by an even partition of 12. Exactly 11
cycle types occur:

```text
12
10+2
8+4
8+2+2
6+6
6+4+2
6+2+2+2
4+4+4
4+4+2+2
4+2+2+2+2
2+2+2+2+2+2
```

Among all `11!! = 10,395` perfect matchings, their exact multiplicities are:

```text
12:                 3840
10+2:               2304
8+4:                1440
6+4+2:               960
8+2+2:               720
6+6:                 640
4+4+2+2:             180
6+2+2+2:             160
4+4+4:               120
4+2+2+2+2:            30
2+2+2+2+2+2:           1
```

This independently reproduces the known count of 11 possible combined
neighborhoods. Ordinary eigenvalue interlacing does not eliminate any of the
11 types; stronger compatibility between different base points is required.

## 6. Two exact fixed-rank projector identities

Put

```text
M = X^T X,
Y = X^T P X.
```

The joint eigenspaces of `B`, `M`, `Y`, and `J` give two integral matrices:

```text
G30 = 24 I + 2 J - 3 M - Y - 8 B,
G40 = 60 I - 2 J - 4 M + Y + 15 B.
```

They satisfy exact integer identities

```text
G30^2 = 56 G30,   rank(G30)=30,   diag(G30)=20,
G40^2 = 105 G40,  rank(G40)=40,   diag(G40)=50.
```

Both are positive semidefinite. Their traces are 1,680 and 4,200. In
particular:

- every 31-by-31 principal determinant of `G30` is zero;
- every 41-by-41 principal determinant of `G40` is zero;
- every principal minor of either matrix is nonnegative.

Because their entries are affine functions of the Boolean edges, these are
certificate-safe pruning rules for fully assigned local cores. Exact integer
or fraction-free elimination should be used. A nonzero determinant modulo a
prime certifies a nonzero integer determinant and therefore a contradiction;
a zero modular determinant alone proves nothing.

For distinct labels, write `m=|u intersection v|` and let `y` count cross-pairs
that are edges of the fixed matching. The off-diagonal entries are

```text
G30[u,v] = 2 - 3m - y - 8 B[u,v],
G40[u,v] = -2 - 4m + y + 15 B[u,v].
```

`src/verify_projectors.py` checks both scalar identities and the complete
transition/triangle decomposition independently on any proposed witness.

## 7. The 231-vertex triangle graph

Let `N` be the 99-by-231 vertex-triangle incidence matrix of a putative graph,
and let `Q` be its triangle-intersection graph. Then

```text
N N^T = 7 I + A,
N^T N = 3 I + Q.
```

Therefore

```text
Spec(Q) = 18^1, 7^54, 0^44, (-3)^132.
```

The graph `Q` is 18-regular. The neighborhood of every triangle is `3 K6`, and
adjacent vertices of `Q` have exactly five common neighbors.

For a fixed triangle `T`, let `n_j(T)` be the number of disjoint triangles with
exactly `j` cross edges to `T`. A common neighbor in `Q` is equivalent to a
cross edge, and `j` is at most three. Exact double counts give

```text
n0+n1+n2+n3 = 212,
n1+2n2+3n3 = 216,
n2+3n3 = 36.
```

Consequently, for `t(T)=n3(T)`, every triangle has profile

```text
(n0,n1,n2,n3) = (32-t, 144+3t, 36-3t, t).
```

There is one further exact restriction. The 36 external neighbors of `T` split
into three 12-sets according to which vertex of `T` they meet. Between every
pair of these sets, the cross edges form a perfect matching. Composing the
three matchings gives a permutation of 12 points, and `t(T)` is exactly its
number of fixed points. A permutation cannot have exactly 11 fixed points:
the single remaining point would also have to be fixed. Conversely, a
permutation on 12 points can have any number of fixed points from 0 through 10,
or all 12. Thus only 12 radius-one profiles are arithmetically possible:

```text
t in {0,1,2,3,4,5,6,7,8,9,10,12}.
```

For a root triangle `{r,i,i'}`, this same `t` is the number of fixed points of
the matched-star permutation `phi_i` from Section 4.

## 8. Transition-triangle hypergraph relaxation

The necessary structure can be encoded before the remaining common-neighbor
equations:

- 924 possible transition edges `C`;
- 35,560 possible triples of pairwise-disjoint labels;
- one transition at each endpoint of each label;
- exactly five selected disjoint triples through every label;
- every disjoint label-pair used by at most one selected triple;
- all exact `X B` incidence equations;
- one of the five exhaustive seed orbit representatives.

`src/hypergraph_cpsat.py` implements this relaxation. It is stronger
structurally than the incidence-only model, but a feasible solution is not a
Conway graph because the remaining common-neighbor equations are omitted.
Bounded monolithic trials returned `UNKNOWN`. The intended use is as a lazy-cut
or cube generator, followed by exact SAT and projector-minor checks.

## 9. Current implication for the search

None of the five exhaustive seed branches is eliminated by radius-one
transition/triangle constraints. All 11 adjacent-pair local types and all 12
allowable triangle profiles survive their respective purely local constraints.
Thus a proof must couple multiple local cores.

The next exact search layer should branch on transition matchings and the seven
matched-star permutations, generate triangle-hypergraph cubes, reject cubes by
`G30`/`G40` rank minors, and send only surviving leaves to a certificate-
producing SAT solver. Global nonexistence still requires checked coverage of
every leaf; existence still requires a complete witness accepted by all
independent verifiers.
