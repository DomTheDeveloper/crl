# Recorded `n=22` OpenMP results

These are reproducible computational observations from this package. They do **not** determine the exact value of `D_mono(22)`.

## Exact geometry

For parity `0`, the generated instance has:

- 242 parity-compatible cells;
- 2,455 distinct maximal geometric lines containing at least three compatible cells.

The opposite parity is isomorphic by reflection.

## Verified lower-bound configurations

`examples/n22_33.txt` is a 33-point no-three-in-line set. The independent Python checker tests all `C(33,3) = 5,456` triples with integer determinants.

Two additional independently generated 33-point seeds are included as `n22_33_seed_b.txt` and `n22_33_seed_c.txt`. Their pairwise overlaps are 6, 10, and 4 points, so the local exact searches below probe distinct basins rather than copies of one configuration.

## Best 34-point near configuration

`examples/n22_near34_one_conflict.txt` has exactly one collinear triple:

```text
(6,8), (14,16), (18,20)
```

It is not a witness.

## Completed exact local exclusions

For each of the three verified 33-point seeds, augmentation destroy radius 7 was exhausted. Each run enumerated all 4,272,048 seven-point removal subsets and proved that no legal eight-point reinsertion exists. Aggregate completed removal neighborhoods: 12,816,144.

For the one-conflict 34-point near configuration, exact repair radii 1 through 8 were exhausted. At radius 8 the program completed all 18,156,204 removal subsets; 10,267,479 hit the existing bad triple and therefore required reinsertion search. No exact eight-for-eight repair was found. Across radii 1 through 8, 13,750,987 conflict-hitting removal subsets were checked.

These statements are finite and exact **only for the stated neighborhoods**. They are not a global UNSAT proof.

## Incomplete runs excluded from evidence

- Augmentation radius 8 around the 33-point seeds did not complete.
- Repair radius 9 around the one-conflict 34-point state did not complete.
- Heuristic target-34 runs found no witness, but heuristic exhaustion is never treated as UNSAT.

The exact status therefore remains:

```text
33 <= D_mono(22) <= 34.
```
