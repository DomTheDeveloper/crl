# Exact top-mask-68 closure for `D_mono(22)`

This directory records a completed canonical all-double boundary family in the target-34 search.

## Exact solver closure

For top boundary mask `68`, there are 34 admissible canonical left masks. Thirty-three fixed-left formulas were solved directly as UNSAT. The remaining left mask `288` resisted monolithic solving, so it was partitioned over all 38 admissible bottom masks; every fixed `(top,left,bottom)` formula was solved as UNSAT.

The hybrid audit checks:

- every expected fixed-left or fixed-bottom scope is present;
- every recorded terminal result is UNSAT;
- no result contains a witness or SAT status;
- the scopes own all 38,192 canonical boundary orbits exactly once;
- no scope is missing or duplicated.

The audit result is `PASS: true` with 71 exact UNSAT records.

## Trust boundary

This establishes a complete solver closure and an independently enumerated coverage partition for top mask 68. It is not yet a finished machine-checkable proof bundle: each solver-derived UNSAT scope still needs a checked DRUP/DRAT/LRAT certificate before the family can be used in the final theorem without trusting the SAT solver.

This family alone does not determine `D_mono(22)`. The global status remains

```
33 <= D_mono(22) <= 34
```

until all canonical all-double and singleton regimes are certificate-closed, or a valid 34-point witness is found.
