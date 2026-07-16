# Exact finite certificates for the 17×17 and 21×21 checkerboards

This directory contains a complete, deterministic certificate package for the
monochromatic checkerboard no-three-in-line problem.

For `p ∈ {0,1}`, let `D_mono(n,p)` be the largest subset of

```text
{(x,y) : 0 ≤ x,y < n and (x+y) mod 2 = p}
```

that contains no three points on any Euclidean line, and let
`D_mono(n) = max(D_mono(n,0), D_mono(n,1))`.

## Exact values

| board | parity 0 | parity 1 | combined |
|---|---:|---:|---:|
| `17×17` | `26` | `26` | `26` |
| `21×21` | `32` | `32` | `32` |

The full mathematical argument is in `PROOF.md`.

## Primary proof path

The source-level proof does not depend on a SAT timeout or an unavailable large
proof artifact.

1. `dual_profiles.json` stores exact rational four-direction line covers.
2. `verify_profiles.py` and `verify_profiles_independent.py` expand and check the
   covers using two implementations and integer arithmetic.
3. The 17×17 objectives are strictly below 27, proving both upper bounds
   immediately.
4. For 21×21, the dual covers reduce a hypothetical 33-point set to saturated
   positive-weight lines and small symmetry cases.
5. `verify_exhaustive_upper_bounds.py` regenerates every all-slope candidate
   line and closes every remaining case by exhaustive exact-cardinality search.

The exhaustive search fingerprints are:

```text
parity 0: 13,560 nodes
parity 1: 13,239 nodes
total:    26,799 nodes
```

It uses only Python's standard library, exact integers, finite propagation, and
complete branching. It has no timeout acceptance path and raises an error if a
completion is found.

## Lower-bound certificates

The four files under `constructions/` are explicit point sets. Each is checked
in three structurally different ways:

1. `check_model.py` tests every selected triple with the exact integer
   determinant;
2. `check_coordinates_independent.py` normalizes every integer line determined
   by a selected pair and rejects any line occurring on three selected points;
3. `generate_fixed_construction_cnf.py` fixes every board variable and sends the
   resulting all-slope CNF to pinned CaDiCaL and Kissat builds.

The committed SHA-256 digests are recorded in `manifest.json`.

## Exact dual data

The four profile objectives are

```text
17 parity 0: 1788/67 < 27
17 parity 1:  880/33 = 80/3 < 27
21 parity 0: 2476/75 = 33 + 1/75
21 parity 1: 1584/48 = 33
```

For 21 parity one, a hypothetical 33-set must use the 132 zero-slack candidates,
saturate all 56 positive-weight lines, and choose exactly one point from each of
the zero-weight sum- and difference-diagonal classes. The 64 special-point
pairs reduce to ten `D4` orbits.

For 21 parity zero, the 136 candidates have 116 zero-slack and 20 one-slack
points. The exact identity `slack + weighted line deficit = 1` leaves four
symmetry cases: three one-slack point orbits, plus the zero-slack case with one
of the four weight-one axis lines deficient by one.

The exhaustive verifier combines these reductions with all 548 parity-zero or
508 parity-one maximal Euclidean candidate lines.

## Deterministic CNF cross-checks

The package also retains independently generated SAT instances:

| instance | variables | clauses | SHA-256 |
|---|---:|---:|---|
| `n17-p0-k27` full | 3709 | 24765 | `7b3a37138b8ae8374da08e2685c3fd4fc5a7b4a1f8aa331ed4805ae83273e221` |
| `n17-p1-k27` full | 3681 | 24402 | `ff571ad45466c593d242ed453ba575b84f36b54a5145704d65bf87555f9adccf` |
| `n21-p0-k33` reduced | 4096 | 20946 | `6e086de861ac3dfb4e099422fc2fccab8e926322d05d2020e21e05ac2dea847c` |
| `n21-p1-k33` reduced | 3960 | 19944 | `10bd70ac54894a10df3e814aa453a9c80f149f465a102a147de9edf082a0a38e` |

`verify_instance_semantics.py` imports none of the generators. It independently
rebuilds the point set, enumerates collinear triples by exact determinants,
reconstructs the cardinality counter, rederives the 21×21 slack reduction, and
compares each generated CNF clause by clause.

## Solver corroboration

The slower proof-producing workflow uses pinned builds of:

- CaDiCaL at commit `7b99c07f0bcab5824a5a3ce62c7066554017f641`;
- Kissat at commit `8af8e56f174b778aef3aa45af9f739b2a5f492c2`;
- `drat-trim` and `lrat-check` at commit
  `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`.

CaDiCaL emits DRAT, `drat-trim` verifies it and emits LRAT, and `lrat-check`
checks LRAT. Kissat, OR-Tools CP-SAT, and SciPy/HiGHS independently reconstruct
or solve the same finite models. These runs are corroboration; the small
standard-library exhaustive verifier is now the primary upper-bound proof.

A timeout, resource limit, `UNKNOWN`, missing status line, or malformed proof is
always treated as no result.

## Reproduction

From this directory:

```bash
python3 verify_manifest.py
python3 test_encoding.py
python3 verify_profiles.py
python3 verify_profiles_independent.py
python3 verify_exhaustive_upper_bounds.py
python3 check_coordinates_independent.py constructions/*.json
```

The exhaustive proof ends with

```text
VERIFIED D_mono(21,0) <= 32 nodes=13560
VERIFIED D_mono(21,1) <= 32 nodes=13239
ALL N=21 EXHAUSTIVE UPPER BOUNDS VERIFIED nodes=26799
```

Generate and independently validate all four CNFs:

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

## Audit boundary

The exact constructions, rational profiles, reductions, all-slope geometry,
symmetry decomposition, exhaustive upper-bound algorithm, deterministic node
fingerprints, CNF generators, semantic checkers, and hashes are committed.
Large DRAT/LRAT files remain optional reproducibility artifacts rather than the
only evidence for the theorem.
