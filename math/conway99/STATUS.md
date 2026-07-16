# Verified status — 2026-07-16

## Verdict

**The Conway 99-graph problem is not settled by this campaign.**

No valid 99-vertex graph has been found, and no globally exhaustive checked
UNSAT certificate has been produced. Solver timeouts and `UNKNOWN` results are
recorded only as performance data.

## Completed and independently checked

- exact reduction from 99 vertices to an 84-vertex labelled Boolean graph;
- exact SAT and CP-SAT encodings of the reduced equations;
- three independent witness-verification paths;
- exact reduced spectrum and rank-30/rank-40 integral projector identities;
- exact decomposition into an 84-edge transition 2-factor and 140 edge-disjoint
  disjoint-label triangles;
- a second weighted transition 2-factor on the edges of `4 K7`;
- exact exclusion of short-transition overlap values `81,82,83`;
- exact classification of 11 adjacent-pair local types and 12 allowable
  triangle profiles;
- exact four-fold-cover reduction of the extremal `s=84` branch;
- a 7,680-element audit showing its 240 seed triangles form one orbit;
- a complete deterministic `s=84` CNF with 263,457 variables and 615,954
  clauses, SHA-256
  `913237d12c4cbc7dee7d99f8f2b0228ac004858af53a4f8c600cdd6d4fdac1b3`;
- a necessary 36,484-variable transition/triangle CP-SAT relaxation;
- five exhaustive general seed orbits of sizes `1,10,10,20,80`;
- SAT and CP-SAT reconstruction of the known `SRG(9,4,1,2)` regression graph;
- a small CaDiCaL UNSAT trace independently accepted by the RUP checker;
- a strict manifest checker for exhaustive cube-and-conquer coverage.

## Search results that are explicitly not proofs

- all five seed classes have radius-one transition/triangle completions;
- all 11 adjacent-pair local types survive ordinary spectral interlacing;
- all 12 allowable triangle profiles survive their purely local constraints;
- bounded transition/triangle CP-SAT runs returned `UNKNOWN`;
- bounded general and specialized complete-CNF runs returned timeout/no result.

These results show that a successful proof must couple multiple local cores;
they do not favor either existence or nonexistence.

## Not completed

- no 99-vertex SAT witness;
- no checked UNSAT proof even for the complete `s=84` subcase;
- no complete set of general branch proofs;
- no independently checked global DRAT/LRAT/FRAT certificate;
- no Lean proof of existence or nonexistence.

Prior local archives represented only by checksum files were not trusted or
imported; they must be regenerated from source before use.
