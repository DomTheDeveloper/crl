# Matching-cross skeleton and the exact `s=84` branch

This document derives a second transition system inside every putative Conway
99-graph and a specialized exact encoding of its extremal branch. None of the
bounded runs reported here settles the original problem.

## 1. A second canonical 2-factor

Use the canonical 84-vertex root reduction and put

```text
M = X^T X,
Y = X^T P X,
```

where `P` swaps the two vertices in each of the seven fixed matching pairs.
From

```text
X B = 2 J - X - P X
```

one obtains, by left multiplication with `X^T` and `X^T P`,

```text
M B = Y B = 4 J - M - Y.
```

For distinct labels `u,v`, `Y[u,v]` is the number, zero, one, or two, of fixed
matching pairs split between the two labels. Therefore the weighted graph

```text
F[u,v] = Y[u,v] B[u,v]
```

has weighted degree two at every vertex: this is the diagonal identity
`(YB)[u,u]=2`.

There is a direct combinatorial interpretation. For each fixed base pair
`{i,i'}`, the exact incidence equations give a perfect matching between the 12
labels containing `i` and the 12 labels containing `i'`. Superposing these
seven perfect matchings produces `F`; an edge with `Y=2` appears twice. Every
84-label vertex belongs to two fixed base pairs, hence has weighted degree two.

After collapsing each fixed base pair to one of seven group vertices, the 84
labels are the four signed parallel edges above every edge of `K_7`. Thus `F`
is a transition system, or circuit decomposition, of the multigraph `4 K_7`.
This is independent of the transition 2-factor `C` on the edges of
`K_14-7K_2` derived in `STRUCTURE.md`.

## 2. The overlap parameter `s`

Call a `C`-edge *short* when its two nonshared base endpoints form one of the
seven fixed matching pairs. These are exactly the simple edges common to `C`
and `F`. Let their number be `s`.

Equivalently, form a 14-by-7 zero-one matrix `Z`. Its row indexed by a base
point `a` and column indexed by a fixed pair `p` is one when the transition
matching at `a` pairs the two points of `p`. Entries in the column belonging to
the fixed pair containing `a` are unavailable and are treated as zero. Then

```text
s = sum Z.
```

Each row compares two perfect matchings on 12 points. It can have
`0,1,2,3,4`, or `6` common edges, but not five: after five common edges the two
remaining points are forced to form the sixth. Each column is the fixed-point
set of a permutation of 12 points, so it can have size `0,...,10` or `12`, but
not 11.

Measure deficits from the all-one pattern on the 84 available entries. No
positive row deficit and no positive column deficit can equal one. Therefore:

- deficit one is impossible immediately;
- deficit two must occur in one row and creates two columns of deficit one;
- deficit three must occur in one row and creates three columns of deficit one.

Hence every putative graph satisfies the exact exclusion

```text
s not in {81,82,83}.
```

This conclusion uses only the two perfect-matching systems and does not assume
any automorphism of the unknown graph.

## 3. Structure of the extremal branch `s=84`

If `s=84`, every transition at every base point pairs the six remaining fixed
base pairs. The 84-label `C`-factor is then fixed and consists of 21 disjoint
four-cycles, one on the four signed labels joining each pair of the seven base
groups. The weighted 2-factor `F` equals `C`, so every selected disjoint-label
edge has `Y=0`.

For a group pair `e`, combine:

- the fixed root;
- the four root-neighborhood vertices in the two groups;
- the four labels in the corresponding four-cycle.

These nine vertices induce `SRG(9,4,1,2)`. Every pair of its vertices already
has the full required number of common neighbors inside the nine-set. An
outside vertex therefore has at most one neighbor in it. The nine vertices
have ten external neighbors each, giving 90 edges to the 90 outside vertices,
so every outside vertex has exactly one neighbor in the nine-set.

Consequences for the 21 four-vertex label fibers are exact:

- fibers whose two group pairs intersect have no cross edges;
- between every two disjoint fibers, the 4-by-4 cross block is a perfect
  matching.

Thus the reduced graph in this branch is a four-fold cover of the Kneser graph
`KG(7,2)`, with an internal four-cycle in every fiber. The 21-cell partition is
equitable, with quotient matrix

```text
2 I + A(KG(7,2)).
```

Its quotient spectrum is

```text
12^1, 3^14, (-2)^6,
```

which is compatible with, but does not imply, the full reduced spectrum.

## 4. Exhaustive symmetry in the specialized branch

Fix the seed label `{0,2}`. There are exactly 240 possible all-`Y=0`
disjoint-label triangles through it. The complete 7,680-element setwise
stabilizer of the seed in `Aut(7K_2)` acts transitively on these 240 triangles.
Therefore one representative triangle may be fixed without loss.

`src/s84_symmetry_audit.py` enumerates the stabilizer and all candidates and
checks the single-orbit claim directly.

## 5. Exact cover CNF

`src/s84_cover_sat.py` encodes the entire `s=84` branch, not a relaxation:

- the 84 short transition edges are fixed;
- each of the 105 disjoint fiber pairs is constrained to a 4-by-4 permutation
  matrix;
- every reduced common-neighbor equation is included;
- one representative of the 240-element seed-triangle orbit is fixed;
- SAT output is written in the standard reduced-edge witness format;
- UNSAT output can retain a CaDiCaL proof trace.

With the pinned PySAT version, the deterministic symmetry-broken CNF has

```text
263,457 variables
615,954 clauses
SHA-256 913237d12c4cbc7dee7d99f8f2b0228ac004858af53a4f8c600cdd6d4fdac1b3
```

This is substantially smaller than both the 1.23-million-variable general CNF
and the earlier 483,537-variable triangle-explicit encoding of the same branch.
A timeout is still no result. An UNSAT claim requires retaining and
independently checking the proof against this exact CNF.
