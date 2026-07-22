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

| overlap `s` | deficit | raw transition states | symmetry orbits | status |
|---:|---:|---:|---:|---|
| 84 | 0 | specialized cover | exact finite quotient | eliminated by replayable finite/XOR certificate |
| 80 | 4 | 3,780 skeletons | 4 completed branches | certified UNSAT |
| 79 | 5 | 0 | 0 | mathematically impossible |
| 78 | 6 | 300,160 | 29 | certified UNSAT |
| 77 | 7 | 1,989,120 | 36 | certified UNSAT |
| 81–83 | 1–3 | 0 | 0 | mathematically impossible |

The `s=77`, `s=78`, and `s=80` branches use independently checked DRUP
packages. The `s=84` elimination uses a different exact certificate chain:
finite orbit enumeration, finite-field quotient classification, sound
finite-domain propagation and a stored 54-row XOR contradiction over `F2`.

## Complete corrected `s=84` elimination

The first specialized cover encoder represented fixed truth by integer `1`,
colliding with DIMACS variable 1. All hashes and proof claims from that version
remain invalid and are not used.

The replacement proof starts from the corrected exact four-fold-cover equations
and establishes:

```text
256 parity-curvature supports
  -> one 30-element S7 orbit
  -> Fano/F2^3 geometry
  -> three S3 quotient parameters
  -> parameters 0 and 2 propagate to contradiction
  -> parameter 1 forces one C4 axis
  -> 546 equations in 210 F2 variables
  -> 54 selected equations XOR to 0 = 1
```

The replayable certificate and checkers are:

```text
certificates/S84_TRANSLATION_XOR.json
src/s84_lift_propagation_audit.py
src/s84_translation_parity_audit.py
src/verify_s84_translation_xor.py
src/s84_elimination_audit.py
```

Therefore `s=84` is eliminated independently of the old 1,712-cube campaign.

## Deterministic `s=76` quotient

`src/s76_transition_orbits.py` regenerates the complete deficit-eight quotient
from first principles:

```text
1,447,530 raw supports
164,535 normal forms under the seven row swaps
105 skeleton orbits under simultaneous S7 relabelling
11,872 raw perfect-matching completions
701 completed transition orbits under exact support stabilizers
```

The canonical compact representative payload has SHA-256

```text
802dd82ae32a7e43549d742a176778fd1f2fd55b8001d5f102eaf30b8c9a692c
```

The 701 transition orbits induce only 64 labelled intact-fiber masks and 41
masks up to `S7`. Every branch has 13 through 18 intact four-vertex fibers.
`src/s76_intact_core_cpsat.py` retains every `S4` permutation block incident
with an intact fiber and imposes all exact three-holonomy and six-path equations
whose two endpoint fibers are intact.

## Present frontier

The full Conway problem is not solved. The current exact implication is

```text
s <= 76.
```

The next objective is to eliminate or sharply reduce the 41 intact-core types,
then emit proof-producing SAT leaves only for the surviving completed transition
orbits. No timeout, `UNKNOWN`, or unchecked solver answer is counted as a proof.
