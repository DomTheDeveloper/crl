# Why the unrestricted target-34 CNF is equivalent to the original n=22 decision problem

The file emitted by `emit_global_cnf.py` has **no fixed boundary mask and no symmetry-breaking
assumption**. Its primary variables are the 242 points of the even checkerboard color on the
22 by 22 board.

## Primary constraints

1. `CardEnc.equals(..., 34)` requires exactly 34 selected points.
2. For every Euclidean line containing at least three points of this parity class, every
   three-element subset receives the clause `(-a OR -b OR -c)`. Consequently every Euclidean
   line contains at most two selected points. Conversely, these clauses are satisfied by every
   no-three-in-line set.

Thus the primary part is exactly the existence question for a 34-point monochromatic NTIL set.
A larger NTIL set would contain a 34-point NTIL subset, so ruling out exact cardinality 34 rules
out all larger cardinalities as well.

## The weighted-slack identity is implied, not assumed

For each of the 61 weighted rows, columns, and diagonals, let `occ(L)` be its selected-point
occupancy. The all-line clauses imply `occ(L) <= 2`. Let `w_L` be the integer line weight and
let `c_p` be the total weight of the weighted lines through point `p`. The checked data satisfy

```
2 * sum_L w_L = OBJ = 6470,
min_p c_p >= DEN = 187,
BUD = OBJ - 34 * DEN = 112.
```

For every exact-34 assignment,

```
sum_p (c_p - DEN) x_p + sum_L w_L (2 - occ(L))
  = sum_p c_p x_p - 34*DEN + 2*sum_L w_L - sum_L w_L occ(L)
  = OBJ - 34*DEN
  = BUD.
```

The middle cancellation is the double-counting identity
`sum_p c_p x_p = sum_L w_L occ(L)`.

`n22_exact_core.py` introduces Boolean names for `occ(L)=0` and `occ(L)<=1`, then uses an
exact reduced BDD to encode this equality. Because `occ(L)` is already in `{0,1,2}`, the line
contribution is exactly `2w_L`, `w_L`, or `0`. The special clauses for weights larger than the
remaining budget are direct logical consequences of the same equality.

Therefore every 34-point monochromatic NTIL set extends to a satisfying assignment of the
emitted CNF, and every satisfying assignment projects to such a set. A checked DRAT refutation
of this CNF proves that no 34-point set exists.

## Other checkerboard color

For an even board, the affine reflection `(x,y) -> (21-x,y)` is a bijection between the two
checkerboard colors and preserves collinearity. Hence the two parity classes have equal optima.
Together with the independently determinant-checked 33-point witness, a verified global UNSAT
certificate establishes `D_mono(22) = 33`.
