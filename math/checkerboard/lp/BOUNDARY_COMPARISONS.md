# Exact bounded comparisons between finite four-direction symmetry classes

Let

- `F_m = L4(2m+1,0)` be the odd fat parity-class optimum;
- `T_m = L4(2m+1,1)` be the odd thin parity-class optimum;
- `E_m = L4(2m,0)` be the even optimum.

Only rows, columns, and the two principal diagonal families are constrained,
with capacity two on every line.

## Theorem

For every `m`,

```text
E_m <= F_m <= E_m + 2,
E_m <= T_m <= E_m + 2.
```

Consequently,

```text
|T_m - F_m| <= 2,
|E_m - F_m| <= 2.
```

Thus the constants in `FourDirectionFractionalPackage` may both be chosen to
be exactly `2`.

## Proof of `E_m <= F_m`

Embed the `2m x 2m` grid into the first `2m` rows and columns of the
`(2m+1) x (2m+1)` grid without changing coordinates.  Parity zero remains
parity zero.  Extend a feasible weighting by zero outside the image.

Every row and column in the image is an old row or column.  The negative
slopes retain the key `x+y`; the positive-diagonal key changes from
`x+2m-y` to `x+(2m+1)-y`, merely translating the diagonal index by one.
Hence every new line load is either an old line load or zero, and feasibility
and objective value are preserved.

## Proof of `F_m <= E_m + 2`

Start with a feasible weighting on the odd fat class.  Remove its last column
`x=2m`.  The removed weight is the load of one column and is therefore at most
two.  The remaining coordinates already lie in the `2m x 2m` grid and retain
parity zero.  As above, restriction and the one-step translation of the
positive-diagonal key preserve every four-direction capacity.  Therefore the
remaining objective is at most `E_m`, proving `F_m <= E_m+2`.

## Proof of `E_m <= T_m`

Map `(x,y)` to `(x+1,y)` in the odd grid and extend by zero.  This flips parity
from zero to one.  Rows and columns are translated or unchanged; the
negative-diagonal key is translated by one and the positive-diagonal key by
two.  Thus feasibility and objective value are preserved.

## Proof of `T_m <= E_m + 2`

Delete the first odd-grid column `x=0`, losing at most its capacity two, and
map every remaining point `(x,y)` to `(x-1,y)`.  The parity flips from one to
zero.  The row/column and diagonal keys are translated by constants, so the
restricted weighting is feasible for the even problem.  Hence
`T_m <= E_m+2`.

## Absolute comparisons

Both `F_m` and `T_m` lie in `[E_m,E_m+2]`, so `|T_m-F_m| <= 2`.  The first
sandwich also gives `|E_m-F_m| <= 2`.

## Formalization map

The Lean implementation should expose four reusable operations on finite
weightings:

1. zero extension under the coordinate-preserving embedding;
2. zero extension under the one-column shift;
3. restriction after deleting the last column;
4. restriction after deleting the first column and shifting back.

For each operation, finite-sum reindexing proves objective preservation (or
objective decomposition into retained mass plus one column load), while a
case split on `FourLine` proves feasibility.  Combining the four optimum
inequalities with `linarith` fills `thinComparison` and `evenComparison` in
`FourDirectionFractionalPackage` with constant `2`.
