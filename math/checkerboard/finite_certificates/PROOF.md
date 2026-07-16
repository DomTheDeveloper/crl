# Complete proof of the 17×17 and 21×21 monochromatic values

For `p ∈ {0,1}`, write

```text
B(n,p) = {(x,y) : 0 ≤ x,y < n and (x+y) mod 2 = p}.
```

Let `D_mono(n,p)` be the maximum size of a subset of `B(n,p)` containing no
three collinear points on any Euclidean line, and let

```text
D_mono(n) = max(D_mono(n,0), D_mono(n,1)).
```

This document proves

```text
D_mono(17,0) = D_mono(17,1) = 26,
D_mono(21,0) = D_mono(21,1) = 32.
```

The proof is finite, exact, and reproducible with Python's standard library.
No timeout, numerical tolerance, or unverified solver answer is used.

## 1. Exact line-cover lemma

Use four families of board lines:

- rows `x = a`;
- columns `y = b`;
- sum diagonals `x+y = c`;
- difference diagonals `x-y = d`.

Assign a nonnegative integer numerator weight `w(L)` to each such line and a
positive common denominator `q`. For a board point `z`, define its coverage
numerator and slack by

```text
c(z) = sum of w(L) over the four lines L through z,
s(z) = c(z) - q.
```

The files `dual_profiles.json`, `verify_profiles.py`, and
`verify_profiles_independent.py` verify, using exact integer arithmetic, that
`s(z) ≥ 0` at every eligible point for each of the four profiles below.

If `X` is no-three-in-line and `m(L) = |X ∩ L|`, then `m(L) ≤ 2`. Therefore

```text
q|X| + sum_{z in X} s(z)
  = sum_L w(L)m(L)
  ≤ 2 sum_L w(L).
```

The right side is the stored objective numerator. This identity also records
exactly when equality occurs: every positive-weight line must contain two
selected points.

## 2. The 17×17 upper bounds

The exact objectives are

```text
parity 0: 1788/67 < 27,
parity 1:  880/33 = 80/3 < 27.
```

The line-cover lemma gives `|X| < 27`, hence, integrally,

```text
D_mono(17,0) ≤ 26,
D_mono(17,1) ≤ 26.
```

The files `constructions/n17_p0_26.json` and
`constructions/n17_p1_26.json` give valid 26-point sets, so both inequalities
are equalities.

## 3. The 21×21 parity-one reduction

For parity one, the denominator is `q = 48` and the objective numerator is

```text
1584 = 33·48.
```

Suppose a 33-point set `X` existed. The line-cover lemma forces equality
throughout. Consequently:

1. every selected point has slack zero;
2. every positive-weight row, column, sum diagonal, and difference diagonal
   contains exactly two selected points.

There are exactly 132 zero-slack candidates. Among them, eight lie on a
zero-weight sum diagonal and eight lie on a zero-weight difference diagonal.
There are sixteen positive-weight sum diagonals, each saturated at two points,
so exactly 32 selected points lie on positive-weight sum diagonals. Thus exactly
one selected point lies on a zero-weight sum diagonal. The same argument gives
exactly one selected point on a zero-weight difference diagonal.

The square's dihedral group `D4` has ten orbits on the resulting 64 ordered
choices of those two special points. The exhaustive verifier generates these
orbits itself and checks one representative of each.

For each representative it imposes:

- exactly two selected points on each of the 56 positive-weight lines;
- at most two selected points on every one of the 508 maximal Euclidean lines
  containing at least three candidates;
- the fixed unique zero-sum and zero-difference points.

All ten cases are contradictory. The complete search uses 13,239 nodes.
Therefore

```text
D_mono(21,1) ≤ 32.
```

## 4. The 21×21 parity-zero reduction

For parity zero, `q = 75` and

```text
2476 = 33·75 + 1.
```

Assume again that a 33-point set `X` exists. Let

```text
sigma = sum_{z in X} s(z),
delta = sum over positive-weight lines L of w(L)(2-m(L)).
```

The exact counting identity gives

```text
sigma + delta = 1.
```

Both quantities are nonnegative integers. In particular, every selected point
has slack zero or one. There are 116 zero-slack candidates and 20 one-slack
candidates.

### Case A: `sigma = 1`

Exactly one one-slack point is selected, `delta = 0`, and every positive-weight
line is saturated at two selected points. The 20 possible one-slack points form
three `D4` orbits, represented by

```text
(0,8), (0,10), (3,9).
```

The exhaustive searches for these representatives close after 3,438, 3,549,
and 2,027 nodes, respectively.

### Case B: `sigma = 0`

No one-slack point is selected and `delta = 1`. Since every positive line
weight is a positive integer, exactly one weight-one line has deficit one and
all other positive-weight lines have deficit zero. The only weight-one lines
are

```text
R6, R14, C6, C14.
```

They form one `D4` orbit. Taking `R6` as representative, the verifier imposes
one selected point on `R6`, two on every other positive-weight line, and at most
two on every maximal Euclidean candidate line. This case closes after 4,546
nodes.

The parity-zero search therefore contains 13,560 nodes in total, and proves

```text
D_mono(21,0) ≤ 32.
```

## 5. Why the exhaustive checker is a proof

`verify_exhaustive_upper_bounds.py` uses only exact integers and finite sets.
A state consists of two bit masks recording points fixed true and false.

For an exact-cardinality constraint `sum_{i in C} x_i = k`, it performs only the
following logically forced steps:

- if already-selected points exceed `k`, close the branch;
- if selected plus undecided points is below `k`, close the branch;
- if exactly `k` are already selected, set every other point in `C` false;
- if every undecided point is required to reach `k`, set all of them true.

For an all-slope line constraint `sum_{i in L} x_i ≤ 2`, it closes a branch with
three selected points and sets all remaining line points false once two are
selected.

If propagation does not decide the state, the checker chooses an exact
constraint with `u` undecided points of which exactly `r` must be selected. It
then visits every one of the `binomial(u,r)` choices. These children partition
all possible completions of the parent state. A state is memoized only after
all of its children have been proved contradictory, and memoization is never
shared between different constraint systems.

The verifier would stop with an error if it found a satisfying completion. It
also checks the candidate census, line census, symmetry orbits, and deterministic
node fingerprints before reporting success. Its final fingerprint is

```text
parity 0: 13,560 nodes,
parity 1: 13,239 nodes,
total:    26,799 nodes.
```

## 6. The 21×21 lower bounds

The files `constructions/n21_p0_32.json` and
`constructions/n21_p1_32.json` give explicit 32-point configurations. They are
checked independently by exhaustive integer determinants, normalized integer
line equations, and fully fixed SAT instances.

Combining the upper and lower bounds gives

```text
D_mono(21,0) = D_mono(21,1) = 32.
```

Together with the 17×17 result:

```text
D_mono(17) = 26,
D_mono(21) = 32.
```

## 7. Reproduction

From this directory, run

```bash
python3 verify_manifest.py
python3 verify_profiles.py
python3 verify_profiles_independent.py
python3 verify_exhaustive_upper_bounds.py
python3 check_coordinates_independent.py constructions/*.json
```

A successful run of the exhaustive proof ends with

```text
VERIFIED D_mono(21,0) <= 32 nodes=13560
VERIFIED D_mono(21,1) <= 32 nodes=13239
ALL N=21 EXHAUSTIVE UPPER BOUNDS VERIFIED nodes=26799
```
