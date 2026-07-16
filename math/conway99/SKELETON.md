# Matching-cross skeleton and the `s=84` branch

## 1. Second transition system

In the 84-vertex root reduction put

```text
M = X^T X,
Y = X^T P X,
```

where `P` exchanges the endpoints of the seven fixed base pairs. The exact
incidence equation implies

```text
M B = Y B = 4 J - M - Y.
```

For each fixed base pair `{i,i'}`, the selected graph gives a perfect matching
between the 12 labels containing `i` and the 12 labels containing `i'`.
Superposing these seven matchings gives a weighted degree-two transition system
`F` on the four signed parallel edges over each edge of `K7`.

Independently, the selected intersecting-label edges form a 2-factor `C` on the
84 labels.

## 2. Overlap parameter

A `C`-edge is *short* when its nonshared endpoints are a fixed base pair. These
are precisely the simple edges common to `C` and `F`. Let their number be `s`.

Equivalently, `s` is the number of ones in a 14-by-7 short-transition matrix
with 84 available entries. Positive row and column deficits cannot equal one.
The detailed deficit classification and certificates are in
`DEFICIT_SEARCH.md`.

## 3. Exact structure when `s=84`

If all 84 transitions are short, `C` is fixed and consists of 21 four-cycles,
one on each four-label fiber above an edge of `K7`. Each fiber, together with
the root and the corresponding four root-neighborhood vertices, induces
`SRG(9,4,1,2)`.

Every outside vertex has exactly one neighbor in each such nine-set. Therefore:

- intersecting fibers have no cross edges;
- every pair of disjoint fibers is joined by a 4-by-4 permutation matrix.

Thus the reduced graph is a four-fold cover of `KG(7,2)` with an internal
four-cycle in every fiber. This reduction is exact.

## 4. Symmetry

Fix the seed label `{0,2}`. The 240 possible disjoint-label triangles through
it form one orbit under the complete 7,680-element setwise seed stabilizer.
The fuller seed-star classification used for certificate generation contains
1,712 exact canonical cubes.

## 5. Critical encoder correction

The first version of `src/s84_cover_sat.py` used integer `1` as a sentinel for
fixed truth. DIMACS variable identifiers are also positive integers, so variable
number 1 was accidentally treated as a constant. The old deterministic sizes
and hashes

```text
263,457 variables
615,954 clauses
SHA-256 913237d12c4cbc7dee7d99f8f2b0228ac004858af53a4f8c600cdd6d4fdac1b3
```

are invalid for the intended model and must not be cited as evidence.

The corrected encoder uses identity-tested singleton objects `TRUE` and
`FALSE`. Its unsymmetrized exact base CNF is

```text
263,760 variables
616,560 clauses
SHA-256 09e71a0ecf915961be435f5f93784c061f4eaded737f95dff91fc7acd44aeec4
```

The corrected single-triangle symmetry-broken CNF is

```text
263,760 variables
616,563 clauses
SHA-256 e2de6ea248f5f18846bcab0d4e92e120c9ddad951437e87f351182e6b218ddfa
```

No `s=84` UNSAT claim is accepted until every one of the 1,712 corrected
symmetry cubes has an independently checked proof against the corrected base.
Solver agreement without proof checking remains only computational evidence.
