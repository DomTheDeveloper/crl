# Verified status — 2026-07-22

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
- exact elimination of the complete corrected `s=84` branch;
- deterministic regeneration of all 105 deficit-eight skeleton orbits and all
  701 completed `s=76` transition orbits;
- SAT and CP-SAT reconstruction of `SRG(9,4,1,2)` regressions;
- strict cube-tree, finite-field, XOR-certificate and proof-manifest auditing.

Consequently every putative Conway graph must now satisfy

```text
s <= 76.
```

## Exact `s=84` elimination

The invalid pre-correction CNF/proof claims remain discarded. The replacement
argument does not rely on them.

The corrected four-fold-cover branch is reduced exactly as follows:

1. 256 topologically possible parity-curvature supports;
2. one surviving 30-element `S7` orbit after exact conjugacy filtering;
3. a forced Fano-plane / `F2^3` geometry with stabilizer `GL(3,2)` of order 168;
4. exactly three gauge-fixed `S3` quotient connections;
5. quotient parameters 0 and 2 rejected by exact finite-domain propagation;
6. parameter 1 forced onto one common `C4` axis;
7. 546 affine equations in 210 translation bits over `F2`;
8. a stored 54-row XOR certificate whose selected rows sum to `0 = 1`.

The stored certificate is

```text
certificates/S84_TRANSLATION_XOR.json
```

and is independently reconstructed and replayed by

```text
src/verify_s84_translation_xor.py
src/s84_elimination_audit.py
```

## Active `s=76` campaign

The complete deficit-eight quotient is now regenerated inside the repository:

```text
1,447,530 raw supports
164,535 row-swap normal forms
105 skeleton orbits
11,872 raw matching completions
701 completed transition orbits
```

The representative file has canonical SHA-256

```text
802dd82ae32a7e43549d742a176778fd1f2fd55b8001d5f102eaf30b8c9a692c
```

The 701 branches have only 64 labelled intact-fiber masks and 41 masks up to
`S7`. Every branch retains between 13 and 18 intact four-vertex fibers. The
next exact layer keeps all `S4` cross-block permutations incident with intact
fibers and imposes every three-holonomy and six-path equation whose endpoint
fibers are intact.

## Not completed

- no 99-vertex witness;
- no elimination of every case with `s <= 76`;
- no complete checked UNSAT package for all 701 `s=76` transition orbits;
- no Lean proof of existence or nonexistence.
