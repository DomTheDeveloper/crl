# Exact proof of the checkerboard bound `D_mono(n) ≤ 2n - 4`

## Status

This document gives the complete finite mathematical argument for the exact
all-line theorem.  It does not use the four-direction LP limit, asymptotic
rounding, floating-point optimization, or a finite list of checked values.

The companion Lean development is intended to formalize this argument exactly.
Until the pinned `lake build` and `#print axioms` jobs finish successfully, the
mathematical proof below should not be described as a completed formal proof.

## 1. Exact statement

Let

\[
G_n=\{0,1,\ldots,n-1\}^2,
\qquad
C_\varepsilon=\{(x,y)\in G_n:x+y\equiv\varepsilon\pmod2\}.
\]

A finite set is **no-three-in-line** when no Euclidean line contains three of
its points.  Define

\[
D_{\rm mono}(n,\varepsilon)=
\max\{|S|:S\subseteq C_\varepsilon,\ S\text{ is no-three-in-line}\}
\]

and

\[
D_{\rm mono}(n)=\max_{\varepsilon\in\{0,1\}}
D_{\rm mono}(n,\varepsilon).
\]

We prove

\[
\boxed{D_{\rm mono}(n)\le 2n-4\qquad(n\ge6).}
\]

The Lean predicate uses integer affine lines

\[
Ax+By=C,\qquad A,B,C\in\mathbb Z,\quad(A,B)\ne(0,0).
\]

This is equivalent on `G_n` to the usual Euclidean definition.  One direction
is immediate.  Conversely, a Euclidean line through two distinct lattice
points `(x₁,y₁)` and `(x₂,y₂)` has the integer equation

\[
(y_2-y_1)x+(x_1-x_2)y
=(y_2-y_1)x_1+(x_1-x_2)y_1.
\]

Thus every three collinear lattice points lie on a nonconstant integer affine
line.

## 2. Reduction to the forbidden size `2n-3`

It is enough to rule out a monochromatic no-three-in-line set of size `2n-3`.
Indeed, if a larger set existed, any `2n-3` of its points would still be
monochromatic and no-three-in-line.

Fix `n ≥ 6`, a color `ε`, and suppose for contradiction that

\[
S\subseteq C_\varepsilon,
\qquad |S|=2n-3.
\]

Every row, column, slope-`+1` diagonal, and slope-`-1` diagonal is a Euclidean
line, so each contains at most two selected points.

## 3. Row and column deficits

For `x,y∈{0,…,n-1}`, let `a_x` be the number of selected points in column `x`
and `b_y` the number in row `y`.  Put

\[
c_x=2-a_x,
\qquad
r_y=2-b_y.
\]

These are nonnegative integers, and double counting gives

\[
\sum_x c_x=2n-|S|=3,
\qquad
\sum_y r_y=2n-|S|=3. \tag{1}
\]

Use doubled centered coordinates

\[
X_x=2x-(n-1),
\qquad
Y_y=2y-(n-1).
\]

They satisfy

\[
\sum_{x=0}^{n-1}X_x=0,
\qquad
\sum_{x=0}^{n-1}X_x^2
=\frac{n(n^2-1)}3=:S_2. \tag{2}
\]

Define the row and column defect moments

\[
C_1=\sum_x c_xX_x,
\quad C_2=\sum_x c_xX_x^2,
\qquad
R_1=\sum_y r_yY_y,
\quad R_2=\sum_y r_yY_y^2.
\]

## 4. The two diagonal families

For a board point `(x,y)`, define

\[
U=x+y-(n-1),
\qquad
V=x-y.
\]

Then

\[
X=U+V,
\qquad
Y=U-V,
\qquad
X^2+Y^2=2(U^2+V^2). \tag{3}
\]

Because `x+y≡ε (mod 2)`, only one parity of each diagonal coordinate can
contain selected points.  Give each active diagonal its genuine line capacity:
capacity `2`, except that an active corner diagonal containing only one board
point has capacity `1`.

For either diagonal family the total active capacity is exactly

\[
2n-2. \tag{4}
\]

There are two possible capacity profiles:

* **endpoint profile:** `n` active diagonals, with capacities
  `1,2,…,2,1`;
* **all-double profile:** `n-1` active diagonals, all with capacity `2`.

Let `μ_u` and `ν_v` be unused capacities on the active `U=u` and `V=v`
diagonals.  By (4),

\[
\sum_u\mu_u=(2n-2)-|S|=1,
\qquad
\sum_v\nu_v=(2n-2)-|S|=1. \tag{5}
\]

The deficits are nonnegative integers.  Therefore each family has exactly one
unit of missing capacity.  Define

\[
M_j^U=\sum_u\mu_u u^j,
\qquad
M_j^V=\sum_v\nu_v v^j.
\]

Equation (5) implies

\[
M_2^U=(M_1^U)^2,
\qquad
M_2^V=(M_1^V)^2. \tag{6}
\]

Both capacity profiles are symmetric about zero, so their first moments vanish.
Comparing the selected-point first moments in columns, rows, and diagonals gives

\[
C_1=M_1^U+M_1^V,
\qquad
R_1=M_1^U-M_1^V. \tag{7}
\]

## 5. Exact second-moment identity

Let `D_U` and `D_V` be the second moments of the two full diagonal capacity
profiles.  The selected column-square total is `2S₂-C₂`, and the selected
row-square total is `2S₂-R₂`.  The selected diagonal-square totals are
`D_U-M₂^U` and `D_V-M₂^V`.  Summing (3) over `S` therefore gives

\[
(2S_2-C_2)+(2S_2-R_2)
=2\bigl((D_U-M_2^U)+(D_V-M_2^V)\bigr).
\]

Equivalently,

\[
C_2+R_2=A+2(M_2^U+M_2^V), \tag{8}
\]

where

\[
A=4S_2-2(D_U+D_V). \tag{9}
\]

The two exact profile moments are

\[
D_{\rm end}
=\frac{2(n-1)(n^2-2n+3)}3, \tag{10}
\]

and

\[
D_{\rm dbl}
=\frac{2n(n-1)(n-2)}3. \tag{11}
\]

For completeness, (10) follows by taking twice the centered square sum (2) and
then removing one copy of each endpoint square `(n-1)²`.  Formula (11) is twice
the square sum of the arithmetic progression

\[
-(n-2),-(n-4),\ldots,n-4,n-2.
\]

## 6. The master lower bound

Weighted Cauchy-Schwarz and (1) give

\[
C_1^2\le3C_2,
\qquad
R_1^2\le3R_2.
\]

Using (7),

\[
C_2+R_2
\ge\frac{(M_1^U+M_1^V)^2+(M_1^U-M_1^V)^2}{3}
=\frac{2}{3}\bigl((M_1^U)^2+(M_1^V)^2\bigr).
\]

By (6), if

\[
M=M_2^U+M_2^V,
\]

then

\[
C_2+R_2\ge\frac23M. \tag{12}
\]

Combining (8) and (12),

\[
A+2M\ge\frac23M,
\]

hence

\[
\boxed{M\ge-\frac34A.} \tag{13}
\]

This is the entire defect-moment lower bound needed for the theorem.

## 7. Parity profiles and the contradiction

### 7.1 Odd `n`, endpoint color

When `n` is odd, one color uses the endpoint profile in both diagonal
families.  Substituting `D_U=D_V=D_end` in (9), then using (2) and (10), turns
(13) into

\[
M\ge(n-1)(n-2)(n-3). \tag{14}
\]

The unique missing unit in either family can occur only at an offset with
absolute value at most `n-1`, so

\[
M\le2(n-1)^2. \tag{15}
\]

For `n=7+t`, `t≥0`, the difference between the lower and upper bounds is

\[
(n-1)(n-2)(n-3)-2(n-1)^2
=t^3+13t^2+50t+48>0.
\]

Every odd `n≥6` has `n≥7`, so (14) and (15) contradict each other.

### 7.2 Odd `n`, all-double color

The other color uses the all-double profile in both families.  Equations
(2), (9), (11), and (13) give

\[
M\ge n(n-1)(n-5). \tag{16}
\]

Every active offset has absolute value at most `n-2`, so

\[
M\le2(n-2)^2. \tag{17}
\]

For `n=7+t`,

\[
n(n-1)(n-5)-2(n-2)^2
=t^3+13t^2+48t+34>0,
\]

again a contradiction.

### 7.3 Even `n`

When `n` is even, the two diagonal families have opposite active parities.
Thus one has the endpoint profile and the other the all-double profile,
regardless of the chosen checkerboard color.  Equations (2), (9)–(11), and
(13) give

\[
M\ge(n-1)(n^2-5n+3). \tag{18}
\]

The two radii are `n-1` and `n-2`, so

\[
M\le(n-1)^2+(n-2)^2. \tag{19}
\]

For `n=6+t`,

\[
(n-1)(n^2-5n+3)-\bigl((n-1)^2+(n-2)^2\bigr)
=t^3+10t^2+26t+4>0.
\]

This contradicts (18) and (19).

## 8. Conclusion

All parity and color cases are impossible at size `2n-3`.  By the subset
reduction in Section 2, every monochromatic no-three-in-line subset of the
`n×n` checkerboard has at most `2n-4` points for every `n≥6`.  Therefore

\[
\boxed{D_{\rm mono}(n)\le2n-4\qquad(n\ge6).}
\]

Only the four principal line directions were used after the initial all-line
hypothesis.  This is logically valid because every all-line no-three-in-line
set satisfies those four capacity constraints.  The proof does **not** claim
that a four-direction packing is itself no-three-in-line.
