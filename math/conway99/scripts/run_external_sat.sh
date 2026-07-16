#!/usr/bin/env bash
set -euo pipefail
# Usage: run_external_sat.sh BRANCH OUTDIR
# Requires certificate-producing CaDiCaL on PATH.
branch=${1:?branch A1/A2/B2/B3/B4}
out=${2:?output directory}
mkdir -p "$out"
python "$(dirname "$0")/../src/sat.py" --k 14 --mode full --branch "$branch" \
  --cnf "$out/$branch.cnf" --no-solve
sha256sum "$out/$branch.cnf" > "$out/$branch.cnf.sha256"
# CaDiCaL CLI syntax varies by release; the common form is:
cadical "$out/$branch.cnf" "$out/$branch.drat" | tee "$out/$branch.solver.log"
# Independently build and run drat-trim or convert to LRAT and check with an
# independently built LRAT checker before treating UNSAT as established.
