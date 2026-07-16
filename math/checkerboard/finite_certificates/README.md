# Exact finite certificates for the 17×17 and 21×21 checkerboards

This directory contains deterministic, independently checkable certificate
packages for the monochromatic checkerboard no-three-in-line problem.

For `p ∈ {0,1}`, let `D_mono(n,p)` be the largest subset of

```text
{(x,y) : 0 ≤ x,y < n and (x+y) mod 2 = p}
```

that contains no three points on any Euclidean line. Let
`D_mono(n) = max(D_mono(n,0), D_mono(n,1))`.

## Exact values

| board | parity 0 | parity 1 | combined |
|---|---:|---:|---:|
| `17×17` | `26` | `26` | `26` |
| `21×21` | `32` | `32` | `32` |

The lower bounds are explicit coordinate lists. The upper bounds exclude 27
points on each 17×17 color class and 33 points on each 21×21 color class.

A timeout, interrupted run, resource limit, `UNKNOWN`, or malformed solver log
is **not** counted as a result anywhere in this package.

## Lower-bound certificates

The four files under `constructions/` are the complete point sets. Each is
checked in three structurally different ways:

1. `check_model.py` tests every selected triple with the exact integer
   determinant;
2. `check_coordinates_independent.py` builds the normalized integer equation of
   every line determined by a selected pair and rejects any line occurring on
   three selected points;
3. `generate_fixed_construction_cnf.py` fixes every board variable and sends the
   resulting all-slope CNF to pinned CaDiCaL and Kissat builds.

The committed SHA-256 digests are recorded in `manifest.json`.

## Upper-bound certificates

### 17×17

The exact four-direction dual profiles have objectives

```text
parity 0: 1788/67 = 26.686567...
parity 1:  880/33 = 80/3 = 26.666666...
```

Every all-line no-three-in-line set satisfies the row, column, and slope `±1`
capacity constraints, so these exact dual covers already imply
`D_mono(17,p) ≤ 26` for both parities. The workflow additionally generates the
full all-slope target-27 CNFs and seeks direct UNSAT certificates.

### 21×21

The exact dual objectives are

```text
parity 0: 2476/75 = 33 + 1/75
parity 1: 1584/48 = 33
```

For a hypothetical 33-point set, summing the integer cover slacks gives:

```text
parity 0: total slack ≤ 1
parity 1: total slack ≤ 0
```

Therefore:

- parity 0 uses only the 116 zero-slack and 20 one-slack points, with at most one
  one-slack point selected;
- parity 1 uses only the 132 zero-slack points.

`generate_reduced_n21.py` regenerates these candidate sets from the compact
rational profiles and then adds every all-slope collinear-triple clause. The
resulting reduced target-33 CNFs are proved UNSAT.

## Deterministic instance identities

| instance | variables | clauses | SHA-256 |
|---|---:|---:|---|
| `n17-p0-k27` full | 3709 | 24765 | `7b3a37138b8ae8374da08e2685c3fd4fc5a7b4a1f8aa331ed4805ae83273e221` |
| `n17-p1-k27` full | 3681 | 24402 | `ff571ad45466c593d242ed453ba575b84f36b54a5145704d65bf87555f9adccf` |
| `n21-p0-k33` reduced | 4096 | 20946 | `6e086de861ac3dfb4e099422fc2fccab8e926322d05d2020e21e05ac2dea847c` |
| `n21-p1-k33` reduced | 3960 | 19944 | `10bd70ac54894a10df3e814aa453a9c80f149f465a102a147de9edf082a0a38e` |

`verify_instance_semantics.py` imports none of the generator modules. It
independently rebuilds the point set, enumerates collinear triples by exact
integer determinants, reconstructs the cardinality counter, rederives the 21×21
slack reduction, and compares the generated CNF clause-by-clause.

## Solvers and proof artifacts

The upper-bound workflow uses pinned builds of:

- CaDiCaL at commit `7b99c07f0bcab5824a5a3ce62c7066554017f641`;
- Kissat at commit `8af8e56f174b778aef3aa45af9f739b2a5f492c2`;
- `drat-trim`/`lrat-check` at commit
  `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`.

CaDiCaL emits DRAT. `drat-trim` verifies it and emits LRAT; `lrat-check` then
checks the LRAT artifact. Both compressed proofs, hashes, solver logs, generated
CNFs, metadata, and checker logs are uploaded as GitHub Actions artifacts.
Kissat independently solves the same deterministic CNF. The separate
`crosscheck_upper_solvers.py` reconstructs the mathematical model for OR-Tools
CP-SAT and SciPy/HiGHS; those runs are corroboration, not substitutes for the
proof artifact.

## Reproduction

From this directory:

```bash
python3 verify_manifest.py
python3 test_encoding.py
python3 verify_profiles.py
python3 check_coordinates_independent.py constructions/*.json
```

Generate and independently validate all four upper-bound instances:

```bash
mkdir -p /tmp/checkerboard-certs

python3 generate_cnf.py --n 17 --parity 0 --at-least 27 \
  --cnf /tmp/checkerboard-certs/n17-p0-k27.cnf \
  --metadata /tmp/checkerboard-certs/n17-p0-k27.json
python3 generate_cnf.py --n 17 --parity 1 --at-least 27 \
  --cnf /tmp/checkerboard-certs/n17-p1-k27.cnf \
  --metadata /tmp/checkerboard-certs/n17-p1-k27.json
python3 generate_reduced_n21.py --parity 0 \
  --cnf /tmp/checkerboard-certs/n21-p0-k33.cnf \
  --metadata /tmp/checkerboard-certs/n21-p0-k33.json
python3 generate_reduced_n21.py --parity 1 \
  --cnf /tmp/checkerboard-certs/n21-p1-k33.cnf \
  --metadata /tmp/checkerboard-certs/n21-p1-k33.json

for cnf in /tmp/checkerboard-certs/*.cnf; do
  metadata="${cnf%.cnf}.json"
  python3 verify_instance_semantics.py --cnf "$cnf" --metadata "$metadata"
done

python3 verify_manifest.py --metadata /tmp/checkerboard-certs/*.json
```

Independent optimization cross-checks, after installing the pinned Python
packages used by CI:

```bash
for npt in '17 0 27' '17 1 27' '21 0 33' '21 1 33'; do
  set -- $npt
  python3 crosscheck_upper_solvers.py --solver cpsat --n "$1" --parity "$2" --target "$3" --seconds 1800
  python3 crosscheck_upper_solvers.py --solver highs --n "$1" --parity "$2" --target "$3" --seconds 1800
done
```

The complete pinned proof-producing commands are in
`.github/workflows/certify-checkerboard-upper-bounds.yml`.

## Audit boundary

The coordinate files, compact rational profiles, deterministic generators,
semantic checkers, and hashes are committed. Large DRAT/LRAT files are generated
from those committed inputs and retained as workflow artifacts rather than
silently represented as source-level proofs. The draft PR should remain draft
until every required solver and proof-checking job has completed successfully.
