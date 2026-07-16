# Rigorous campaign design

## 1. Exact mathematical statement

Find a simple graph on 99 vertices such that adjacent pairs have exactly one
common neighbor and nonadjacent pairs have exactly two. These conditions imply
regularity. Double-counting edges between a neighborhood and its complement
then gives

```text
k(k-2) = 2(98-k),
```

so `k=14`. The target is therefore exactly `SRG(99,14,1,2)`.

## 2. Root normal form

Fix a root `r`.

1. `N(r)` is 1-regular, hence `7 K2`.
2. Every vertex outside `r ∪ N(r)` has exactly two neighbors in `N(r)`.
3. These two neighbors cannot be a matched pair.
4. Every nonmatching pair in `N(r)` occurs exactly once, because it already has
   `r` as one of its two common neighbors.

There are `C(14,2)-7=84` such labels. This canonicalizes all vertices without
assuming the unknown graph has any nontrivial automorphism.

For labels `u,v` and reduced adjacency `B`:

```text
sum_{q containing i} B[u,q]
  = 2 - 1[i in label(u)] - 1[mate(i) in label(u)],

common_B(u,v) + B[u,v]
  = 2 - |label(u) ∩ label(v)|.
```

The first family is linear and implies every reduced vertex has degree 12.
The second family is quadratic and completes the exact SRG conditions.

## 3. Safe symmetry breaking

Safe, exhaustive symmetries:

- choose one root;
- canonically label its `7 K2` neighborhood;
- choose seed label `(0,2)`;
- quotient the forced pair of distinguished seed-neighbors by the complete
  setwise stabilizer of `(0,2)`.

`src/symmetry_audit.py` enumerates all 7,680 stabilizer permutations and all
121 admissible ordered pairs. It proves that exactly five orbits remain.

Unsafe as a global assumption:

- requiring a nontrivial automorphism;
- requiring a Paley-9 subgraph or excluding one without proof;
- imposing a cyclic, Cayley, block, or transitive construction ansatz.

Such assumptions may define experimental subsearches but cannot close the
original problem.

## 4. Structural pruning

The adjacency spectrum of a putative graph is

```text
14^1, 3^54, (-4)^44.
```

Two exact positive-semidefinite Gram matrices are

```text
G_-4 = 27 I - 9 A + J,   rank 44,
G_3  = 44 I + 11 A - 2 J, rank 54.
```

For a fully assigned local core, exact rational or modular rank and principal
minor tests can reject patterns incompatible with these global ranks. These
are valid pruning lemmas; floating eigenvalues alone are not certificates.

Additional exact counts available for cross-checking include 231 triangles,
2,079 quadrilaterals, and 22,176 pentagons. Cycle-count inequalities can be
added only after their derivations are independently audited.

## 5. Solver portfolio

### SAT

- exact sequential-cardinality CNF;
- one complete base CNF plus five seed-orbit cubes;
- CaDiCaL/Kissat/CryptoMiniSat portfolio for search;
- cube-and-conquer with deterministic split variables;
- proof output in LRAT/FRAT where possible, DRAT otherwise.

### CP-SAT

- independent high-level Boolean/cardinality model;
- root relaxations for propagation experiments;
- full model for witness search and cross-checking;
- never interpret `UNKNOWN` as infeasible.

### Structural enumeration

- enumerate seed-neighborhood completions canonically;
- apply exact pair equations immediately;
- apply exact Gram-rank filters to completed local cores;
- feed surviving cores as SAT cubes.

Heuristic local search or MaxSAT may propose candidate edge sets, but only the
exact verifiers can certify a construction.

## 6. What constitutes a valid affirmative result

Required artifacts:

1. complete reduced edge list `B`;
2. SHA-256 manifest;
3. successful `verify.py` run;
4. successful `verify_matrix.py` run;
5. preferably a third checker in a different language or proof assistant.

The full reconstructed graph must have 99 vertices, degree 14, one common
neighbor on every edge, and two on every nonedge.

## 7. What constitutes a valid negative result

Required artifacts:

1. deterministic generator and exact source version;
2. hash of the full base CNF;
3. proof that the five seed branches cover all solutions;
4. a binary cube tree whose children exactly partition every internal cube;
5. an UNSAT proof for every leaf;
6. independent proof checking against each exact leaf CNF;
7. a coverage audit with zero missing, duplicate-as-coverage, SAT, UNKNOWN,
   timeout, corrupt, or unchecked leaves;
8. aggregate hashes and reproduction commands.

Only that package would establish global nonexistence. A solver log saying
`UNSAT` without a checked proof, or thousands of closed shards with one
unresolved shard, is not a proof.

## 8. Current frontier

The present code establishes the exact model, independently validates the
encodings on the 9-vertex member of the same SRG family, and removes one
redundant seed branch. The complete 99-vertex search remains open.
