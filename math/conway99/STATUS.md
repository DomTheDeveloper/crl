# Verified status — 2026-07-16

## Verdict

**The Conway 99-graph problem is not settled by this campaign.**

No valid 99-vertex graph has been found, and no globally exhaustive checked
UNSAT certificate has been produced. Solver timeouts and `UNKNOWN` results are
recorded only as performance data.

## Completed and independently checked

- exact reduction from 99 vertices to an 84-vertex labelled Boolean graph;
- exact SAT and CP-SAT encodings of the reduced equations;
- three independent witness-verification paths: common-neighbor, integer-matrix,
  and projector/decomposition checks;
- exact spectrum `12^1,(-2)^6,0^7,3^40,(-4)^30` for the reduced graph;
- exact decomposition into an 84-edge transition 2-factor and 140 edge-disjoint
  disjoint-label triangles;
- seven perfect matchings between the stars of the seven fixed matching pairs;
- exact classification and multiplicities of the 11 adjacent-pair local types;
- exact rank-30 and rank-40 integral projector identities for structural pruning;
- exact spectrum and 12 allowable radius-one profiles for the 231-vertex
  triangle graph, with the apparent `t=11` profile ruled out exactly;
- a necessary 36,484-variable transition/triangle CP-SAT relaxation;
- exact full-stabilizer audit reducing the seed split from six overlapping
  cases to five disjoint orbit classes of sizes `1,10,10,20,80`;
- SAT and CP-SAT reconstruction of the known `SRG(9,4,1,2)` regression graph;
- a small CaDiCaL UNSAT trace independently accepted by the RUP checker;
- a strict manifest checker for exhaustive cube-and-conquer coverage.

## Search results that are explicitly not proofs

- all five seed classes have radius-one transition/triangle completions;
- all 11 adjacent-pair local types survive ordinary spectral interlacing;
- all 12 allowable triangle profiles survive their purely local constraints;
- bounded transition/triangle CP-SAT runs returned `UNKNOWN`;
- a 600-second exact SAT attempt on the globally fixed `t=12` transition branch
  returned timeout/no result;
- bounded complete-CNF runs returned timeout/no result.

These results show that a successful proof must couple multiple local cores;
they do not favor either existence or nonexistence.

## Not completed

- no 99-vertex SAT witness;
- no complete set of 99-vertex branch proofs;
- no independently checked DRAT/LRAT/FRAT certificate for any complete
  99-vertex branch;
- no Lean proof of existence or nonexistence.

Prior local archives were represented in the file library only by checksum
files during this run. Their reported deeper reductions were therefore not
trusted or imported; they must be regenerated from source before use.
