# Verified status — 2026-07-16

## Verdict

**The Conway 99-graph problem is not settled.**

No valid 99-vertex graph has been found, and no globally exhaustive checked
UNSAT certificate covering every transition system has been produced.

## Kernel-independent exact work completed

- exact reduction from 99 vertices to an 84-vertex labelled Boolean graph;
- independent SAT and CP-SAT encodings;
- combinatorial, integer-matrix and projector witness verifiers;
- exact seed-stabilizer quotient into five root branches;
- transition/triangle decomposition and two integral fixed-rank projector
  identities;
- matching-overlap deficit classification;
- independently checked UNSAT certificates for `s=80`, `s=78`, and `s=77`;
- mathematical exclusions `s not in {79,81,82,83}`;
- SAT and CP-SAT reconstruction of `SRG(9,4,1,2)` regressions;
- strict cube-tree and proof-manifest auditing.

Consequently every putative Conway graph must currently satisfy

```text
s = 84 or s <= 76.
```

## Critical correction

The first `s=84` cover encoder used integer `1` for fixed truth, colliding with
DIMACS variable 1. Its old CNF hashes and proof claims are invalid. The corrected
encoder uses typed singleton constants. The corrected 1,712-cube proof audit is
still running, so `s=84` is **not yet certified UNSAT**.

## Active search

- `s=76`: 105 skeleton orbits and 701 completed transition orbits;
- `s=75`: 216 skeleton orbits and 3,611 completed transition orbits;
- corrected `s=84`: exhaustive 1,712-cube independent proof checking.

## Not completed

- no 99-vertex witness;
- no elimination of every case with `s <= 76`;
- no complete corrected certificate for `s=84` yet;
- no Lean proof of existence or nonexistence.
