# Matching-overlap deficit campaign

## Definition

Fix the canonical root and its seven matched pairs. The 84 second-layer labels
carry two exact transition systems:

1. `C`, the selected edges joining labels with one shared base point;
2. `F`, the seven perfect matchings between the two stars belonging to each
   fixed base pair.

Let `s` be the number of simple edges common to `C` and `F`, and put

```text
deficit = 84 - s.
```

Equivalently, form the 14-by-7 short-transition matrix `Z`. The unavailable
entry in row `a` and the column containing `a` is zero. Every other entry is one
when the transition matching at `a` retains the corresponding fixed base-pair
edge. Then `s=sum Z`.

A positive row deficit cannot equal one: two perfect matchings cannot differ in
exactly one edge. A positive column deficit cannot equal one: a permutation of
12 points cannot have exactly 11 fixed points. Thus the defect graph, whose
left vertices are defective rows and whose right vertices are defective
columns, has minimum positive degree at least two on both sides.

## Exact near-extremal consequences

The minimum-degree condition gives immediately:

- deficits 1, 2 and 3 are impossible, hence `s != 83,82,81`;
- deficit 4 is exactly `K_{2,2}`;
- deficit 5 is impossible, hence `s != 79`;
- deficit 6 has three bipartite support shapes;
- deficit 7 has the unique support shape `K_{3,3}` minus a two-edge matching;
- deficit 8 has 105 skeleton orbits and 701 completed transition orbits;
- deficit 9 has 216 skeleton orbits and 3,611 completed transition orbits.

All orbit quotients use only the full wreath-product action
`Aut(7 K2) = C2 wr S7`; no automorphism of the unknown graph is assumed.

## Certified eliminations

The exact branch model fixes a completed transition system and then includes:

- every `X B` incidence equation;
- every reduced common-neighbor equation;
- exact saturation around each intact Paley-9 fiber;
- every remaining disjoint-label edge that is not already forced impossible.

The following subcases have complete independently checked DRUP packages:

| overlap `s` | deficit | raw transition states | symmetry orbits | status |
|---:|---:|---:|---:|---|
| 80 | 4 | 3,780 skeletons | 4 completed branches | certified UNSAT |
| 79 | 5 | 0 | 0 | mathematically impossible |
| 78 | 6 | 300,160 | 29 | certified UNSAT |
| 77 | 7 | 1,989,120 | 36 | certified UNSAT |
| 81–83 | 1–3 | 0 | 0 | mathematically impossible |

Every nontrivial UNSAT branch was solved with Glucose and checked by the
separately compiled deletion-aware RUP checker in `src/drup_check.cpp`.
The manifest records the exact CNF and proof hashes for each leaf. The compact
proof traces themselves are retained as external artifacts because their total
size is unsuitable for ordinary Git history.

## Corrected `s=84` campaign

An earlier specialized encoder represented fixed truth by integer `1`. Since
DIMACS variable identifiers are also positive integers, SAT variable number 1
was accidentally interpreted as a constant. All old hashes and proof claims
from that encoder are invalid and superseded.

The corrected encoder uses identity-tested singleton objects for `TRUE` and
`FALSE`. Its unsymmetrized base CNF has

```text
263,760 variables
616,560 clauses
SHA-256 09e71a0ecf915961be435f5f93784c061f4eaded737f95dff91fc7acd44aeec4
```

The 1,712 exact seed-star symmetry cubes are being regenerated and checked
against this corrected base. Until all 1,712 proofs pass, `s=84` remains
**unsettled**, regardless of solver-level UNSAT results.

## Present frontier

The full Conway problem is not solved. At this checkpoint:

```text
s in {84} or s <= 76.
```

The 701 `s=76` completed transition orbits are undergoing exact SAT search.
No timeout or unchecked solver answer is counted as a proof.
