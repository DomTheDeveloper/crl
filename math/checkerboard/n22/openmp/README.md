# OpenMP search and exact local repair for `D_mono(22)`

This directory contains two C++20/OpenMP programs for the monochromatic checkerboard no-three-in-line problem on the `22 x 22` grid.

**Current mathematical status:** this package verifies a 33-point construction and performs exact finite neighborhood exclusions, but it contains neither a valid 34-point witness nor a complete global UNSAT certificate. Therefore it does not resolve whether `D_mono(22)` is 33 or 34.

## Programs

### `dmono22_openmp`

A fixed-cardinality witness search. It:

- constructs all checkerboard-compatible cells;
- generates every maximal all-slope geometric line containing at least three available cells;
- runs independent OpenMP replicas with deterministic per-trial seeds;
- uses incremental collinear-triple deltas, tabu/min-conflicts moves, weighted breakout penalties, random walks, restarts, and simulated-annealing acceptance;
- optionally enforces exactly two points on each outer boundary or four explicit oriented boundary masks;
- accepts a witness only after an exact integer-determinant check of every selected triple;
- prints `NO_WITNESS`, never `UNSAT`, when bounded heuristic work ends without a witness.

### `dmono22_augment_openmp`

An exhaustive local destroy-and-repair solver. In augmentation mode it removes exactly `d` points from a valid seed and tries every legal `d+1` point reinsertion. In `--repair` mode it removes exactly `d` points from a near-valid fixed-cardinality state, requires the removals to hit every existing conflict, and tries every legal `d` point reinsertion.

It uses exact line-capacity propagation and a sound greedy clique-color upper bound. A completed negative run prints `UNSAT_NEIGHBORHOOD`; that means only the explicitly described neighborhood is exhausted, not the global `n=22` problem.

### `verify_witness.py`

An implementation-independent Python checker using direct integer determinants over every selected triple. It can verify either a true witness or an expected number of conflicts in a near configuration.

## Build and smoke test

```bash
make clean
make -j
make test
```

The default build uses `g++ -O3 -march=native -std=c++20 -fopenmp`.

## Search for a 34-point witness

```bash
OMP_PROC_BIND=spread OMP_PLACES=cores \
./dmono22_openmp \
  --n 22 --parity 0 --target 34 \
  --threads 64 --trials 200000 --steps 500000 \
  --seed 0xD1A0002234 \
  --witness n22_34.txt
```

A successful run returns 0, writes the coordinates, and prints `SAT`. A completed bounded run with no witness returns 2 and writes its best near state to `n22_34.txt.best`; that result is not evidence of nonexistence.

To restrict replicas to the necessary two-points-per-outer-boundary regime:

```bash
./dmono22_openmp --target 34 --double-boundary --threads 64 \
  --trials 200000 --steps 500000 --seed 0xD1A0002234 \
  --witness n22_34_double_boundary.txt
```

Explicit oriented masks are accepted with `--top-mask`, `--left-mask`, `--rb-mask`, and `--rr-mask`.

## Independent verification

```bash
python3 verify_witness.py examples/n22_33.txt \
  --n 22 --parity 0 --size 33

python3 verify_witness.py examples/n22_near34_one_conflict.txt \
  --n 22 --parity 0 --size 34 \
  --expect-collinear-triples 1 --show-conflicts
```

## Exact local neighborhood searches

Exhaust radius 7 around a valid 33-point seed:

```bash
OMP_NUM_THREADS=64 ./dmono22_augment_openmp \
  --seed examples/n22_33.txt --destroy 7 --threads 64
```

Exhaust repair radius 8 around the one-conflict 34-point state:

```bash
OMP_NUM_THREADS=64 ./dmono22_augment_openmp \
  --seed examples/n22_near34_one_conflict.txt \
  --repair --destroy 8 --threads 64
```

The negative exit code is 2 by design. Count a run as an exact local exclusion only when it terminates normally, prints `UNSAT_NEIGHBORHOOD`, and reports `completed_removal_subsets` equal to the announced total.

See [`RESULTS.md`](RESULTS.md) for the completed `n=22` runs recorded during development.

## Reproducibility and trust boundary

For fixed command-line options, trial seeds and per-trial behavior are deterministic; OpenMP scheduling can affect which simultaneous witness is reported first but not whether a completed exact neighborhood enumeration covers its declared removal subsets.

The search code is not a global proof checker. A proof that `D_mono(22)=33` still requires complete coverage of every globally possible 34-point configuration plus independently checked LRAT/FRAT/VeriPB-style artifacts, or another rigorous global argument. A proof that `D_mono(22)=34` requires only one coordinate file accepted by the independent determinant checker.
