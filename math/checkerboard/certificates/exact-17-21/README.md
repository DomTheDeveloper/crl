# Exact certificates for the 17×17 and 21×21 checkerboards

This directory certifies the exact values

\[
D_{\rm mono}(17,0)=D_{\rm mono}(17,1)=26,
\qquad
D_{\rm mono}(21,0)=D_{\rm mono}(21,1)=32.
\]

Hence `D_mono(17) = 26` and `D_mono(21) = 32` when either checkerboard colour may be chosen.

## What is independently checked

`certify.py` contains the mathematical data, generators, and checkers.

* Every lower-bound construction is checked twice with exact integers: once by all triple determinants, and once by a canonical complete-line occupancy calculation.
* The two 17×17 upper bounds are exact rational four-direction dual certificates with objectives `1788/67 < 27` and `880/33 < 27`.
* The two 21×21 duals reduce a hypothetical 33-point set to exact Boolean models with 136 variables/548 line constraints (fat colour) and 132 variables/508 line constraints (thin colour).
* The 21×21 Boolean upper bounds have complete exact rational branch-and-bound certificates. Every leaf is checked using integer arithmetic only, and the binary branch tree is checked to cover every Boolean assignment.
* Four OPB instances are emitted for external pseudo-Boolean solvers.
* OR-Tools CP-SAT and SciPy/HiGHS independently verify every fixed witness and prove all four upper-bound targets infeasible.

The deterministic `verify` command uses only the Python standard library. It does **not** trust SciPy, HiGHS, CP-SAT, floating-point output, or a stored constraint matrix.

## Reproduce

With Python 3.11 or newer:

```bash
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt

python3 certify.py generate
python3 certify.py solve --seconds 120
python3 certify.py verify
```

A successful run ends with:

```text
ALL_DETERMINISTIC_CHECKS_PASS
```

To check already-generated artifacts on a machine with no solver packages:

```bash
python3 certify.py verify
```

## Timeout policy

A timeout, `UNKNOWN`, interrupted run, or solver limit status is `NO_RESULT`. It is never converted into an infeasibility claim. `solve` accepts only CP-SAT `INFEASIBLE` and HiGHS status `2` as upper-bound solver results.

## Proof-artifact status

The committed `.bbcert.json.gz` files are compact complete exact proof artifacts with a deterministic checker, but they are not claimed to be standard LRAT, FRAT, or VeriPB syntax. Proof-logging SAT attempts were made separately; runs that timed out produced no accepted result and are not used in the theorem. The OPB files are provided so a standard VeriPB-capable solver/checker pipeline can be added without changing the mathematical encoding.

## Generated files

* `artifacts/results.json` — exact values, witnesses, and rational profiles.
* `artifacts/instances/*.opb` — four exact pseudo-Boolean infeasibility instances.
* `artifacts/n21-p*-target33.bbcert.json.gz` — complete exact 21×21 upper-bound proofs.
* `artifacts/solver_results.json` — accepted outcomes from CP-SAT and HiGHS.
* `artifacts/SHA256SUMS` — deterministic integrity manifest.

The GitHub workflow regenerates all artifacts from `certify.py`, runs both solvers, runs the standard-library checker, and commits only byte-for-byte reproducible outputs.
