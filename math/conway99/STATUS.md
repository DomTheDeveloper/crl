# Verified status — 2026-07-16

## Verdict

**The Conway 99-graph problem is not settled by this campaign.**

No valid 99-vertex graph has been found, and no globally exhaustive checked
UNSAT certificate has been produced. Solver timeouts and `UNKNOWN` results are
recorded only as performance data.

## Completed and independently checked

- exact reduction from 99 vertices to an 84-vertex labelled Boolean graph;
- exact SAT and CP-SAT encodings of the reduced equations;
- two independent witness verifiers;
- exact full-stabilizer audit reducing the seed split from six overlapping
  cases to five disjoint orbit classes of sizes `1,10,10,20,80`;
- SAT and CP-SAT reconstruction of the known `SRG(9,4,1,2)` regression graph;
- independent combinatorial and matrix verification of both regression
  witnesses;
- a small CaDiCaL UNSAT trace independently accepted by the RUP checker;
- a strict manifest checker for exhaustive cube-and-conquer coverage.

## Not completed

- no 99-vertex SAT witness;
- no complete set of 99-vertex branch proofs;
- no independently checked DRAT/LRAT/FRAT certificate for any complete
  99-vertex branch;
- no Lean proof of existence or nonexistence.

Prior local archives were represented in the file library only by checksum
files during this run. Their reported deeper reductions were therefore not
trusted or imported; they must be regenerated from source before use.
