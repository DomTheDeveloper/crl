# Exact top-mask-34 closure for `D_mono(22)`

This directory records a completed canonical all-double boundary family in the target-34 search.

## Exact solver closure

For top boundary mask `34`, all 39 admissible fixed-left formulas returned UNSAT. Four independent shards completed normally and emitted closed UNSAT summaries. No scope returned SAT, a witness, UNKNOWN, or an incomplete leaf.

The independent family audit checks the shard assignment union, final status of every scope, absence of witnesses, and complete parent closure. It reports `PASS: true`.

These 39 fixed-left scopes own exactly 58,099 canonical boundary orbits for top mask 34.

## Trust boundary

This establishes a complete solver closure and independently enumerated coverage partition for top mask 34. It is not yet a finished machine-checkable proof bundle: each solver-derived UNSAT scope still needs a checked DRUP/DRAT/LRAT certificate before the family can be used in the final theorem without trusting the SAT solver.

This family alone does not determine `D_mono(22)`. The global status remains

```
33 <= D_mono(22) <= 34
```

until all canonical all-double and singleton regimes are certificate-closed, or a valid 34-point witness is found.
