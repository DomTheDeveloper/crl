# Defect moments and four-direction asymptotics for checkerboard no-three-in-line sets

## Status

This document records a research proof package based on Thomas Prellberg's 2026 checkerboard-restricted no-three-in-line problem. It distinguishes four different statements:

1. a finite upper bound for actual checkerboard no-three-in-line sets;
2. a sharper finite bound for integral four-direction packings;
3. the limiting value of the finite four-direction linear programs;
4. the stronger all-slope checkerboard NTIL limit, which remains open.

The results have extensive exact computational corroboration and a partial sorry-free Lean formalization. They have not yet undergone external peer review.

## 1. Setup

Let

\[
G_n=\{0,1,\ldots,n-1\}^2,
\qquad
C_\varepsilon=\{(x,y)\in G_n:x+y\equiv\varepsilon\pmod2\}.
\]

A set is no-three-in-line (NTIL) when it contains no three collinear points. Write

\[
D_{\rm mono}(n,\varepsilon)
\]

for the maximum size of an NTIL subset of `C_ε`, and maximize over the two colors to obtain `Dmono(n)`.

Every NTIL set contains at most two points on every row, column, and diagonal of slopes `+1` and `-1`. The finite moment arguments therefore apply to the larger class of integral four-direction capacity-two packings.

## 2. Defect moments

Put

\[
h=\frac{n-1}{2},\qquad X=x-h,\quad Y=y-h,
\]

and use centered diagonal coordinates

\[
U=X+Y,\qquad V=X-Y.
\]

Suppose a four-direction packing has

\[
N=2n-2-q
\]

points. The quantity `q` is its diagonal capacity deficit. Let `μ_t` and `ν_t` be the unused capacity on the `U=t` and `V=t` diagonals. Define

\[
M_j^U=\sum_t\mu_t t^j,
\qquad
M_j^V=\sum_t\nu_t t^j.
\]

Let `c_i` and `r_i` be the unused column and row capacities, and define their centered second moments `C₂` and `R₂`.

The central identity is

\[
C_2+R_2
=K_{n,\varepsilon}+\frac{M_2^U+M_2^V}{2}.
\tag{1}
\]

The parity-dependent constant is

\[
K_{n,\varepsilon}=
\begin{cases}
-\dfrac{(n-1)(n-2)(n-3)}3,&n\text{ odd, fat class},\\[6pt]
-\dfrac{n(n-1)(n-5)}3,&n\text{ odd, thin class},\\[6pt]
-\dfrac{(n-1)(n^2-5n+3)}3,&n\text{ even}.
\end{cases}
\tag{2}
\]

The first moments satisfy

\[
\sum_i c_i(i-h)=\frac{M_1^U+M_1^V}{2},
\qquad
\sum_i r_i(i-h)=\frac{M_1^U-M_1^V}{2}.
\]

Weighted Cauchy-Schwarz then yields

\[
K_{n,\varepsilon}+\frac{M_2^U+M_2^V}{2}
\ge
\frac{(M_1^U)^2+(M_1^V)^2}{2(q+2)}.
\tag{3}
\]

## 3. The finite `2n-4` theorem

To rule out a set of size `2n-3`, take `q=1`. Each diagonal deficit family consists of one missing unit, at centered offsets `a` and `b`. Thus

\[
M_1^U=a,\quad M_2^U=a^2,
\qquad
M_1^V=b,\quad M_2^V=b^2.
\]

Substituting in (3) gives

\[
a^2+b^2\ge -3K_{n,\varepsilon}.
\tag{4}
\]

Geometry gives the opposite upper bounds:

- odd fat: `a²+b² ≤ 2(n-1)²`;
- odd thin: `a²+b² ≤ 2(n-2)²`;
- even: `a²+b² ≤ (n-1)²+(n-2)²`.

For the required ranges, each upper bound is strictly smaller than the corresponding right side of (4). Therefore

\[
\boxed{D_{\rm mono}(n)\le 2n-4\qquad(n\ge6).}
\]

The Lean project formalizes the three final polynomial contradictions. The capacity profiles and full finite-sum derivation of (1) are still paper-level.

## 4. A stronger finite moment bound

At general deficit `q`, the largest possible diagonal second moment is achieved by placing missing capacity at the largest absolute offsets. A universal ordered-offset majorant is

\[
M_2\le
qn^2-\frac n2q(q+1)
+\frac{q(q+1)(2q+1)}{24}.
\tag{5}
\]

Combining (5) with the master identity and exact cubic reductions for `c=2^(2/3)` gives the research-draft bound

\[
\boxed{
D_{\rm mono}(n)
\le
\min\left(2n-4,\left\lceil2^{2/3}n\right\rceil\right).
}
\]

Lean verifies the algebraic reductions and positivity estimates after the combinatorial majorization (5) is supplied.

## 5. The four-direction LP constant

Prellberg's continuum dual certificate has value

\[
\alpha=1.576823396873808\ldots,
\]

where

\[
401\alpha^3-1744\alpha^2+2240\alpha-768=0.
\]

Equivalently, if `p` is the middle real root of

\[
401p^3-331p^2+19p+7=0,
\]

then

\[
\alpha=2(1-p).
\]

The upper transfer samples the continuum dual functions directly into the odd-fat and shifted odd-thin finite dual programs. The finite constraints match the continuum arguments exactly; the objectives converge by Riemann summation. Even grids embed in the appropriate odd-fat grid.

For the lower direction, an exact continuum primal transport certificate of mass `α` is split into:

- an outer block with 35 affine components and weights in `Q(p)`;
- a seven-component middle block with rational weights.

Exact checkers verify support, positivity, total mass, and all paired projection identities. Smoothing, trimming and Riemann sampling then produce finite primal solutions of value `(α-o(1))n`.

Consequently, the research package claims

\[
\boxed{
\lim\frac{L_m^{\rm fat}}{2m+1}
=
\lim\frac{L_m^{\rm thin}}{2m+1}
=
\lim\frac{L_m^{\rm even}}{2m}
=\alpha.
}
\]

This is the checkerboard-specific four-direction LP conjecture, not the classical all-slope NTIL problem.

## 6. Integral four-direction rounding

The package further argues that the integral four-direction optimum has the same limit. A diffuse finite fractional solution is blown up into a bounded-rank hypergraph:

- line-capacity clones enforce at most two selected points per principal line;
- identity vertices prevent selecting the same board point twice;
- bounded rank is fixed because there are only four direction families;
- diffuseness makes pair-codegrees `o(Δ)`.

Kahn's bounded-rank small-codegree edge-coloring theorem decomposes the blow-up into `(1+o(1))Δ` matchings. One color class retains asymptotically the average mass, yielding an integral four-direction packing with `(α-o(1))n` points.

This argument is paper-level and depends on an external theorem not formalized here.

## 7. What remains open

The actual checkerboard NTIL lower bound requires controlling every Euclidean line, not just four fixed directions:

\[
\boxed{
\liminf_{n\to\infty}\frac{D_{\rm mono}(n)}n\ge\alpha
}
\]

is still open.

The obstacle is multiscale. The number of primitive slope directions grows with `n`; independent rounding produces conflicts on every dyadic slope scale. A final proof appears to require correlated multiscale rounding, absorption/switching, or a direct algebraic construction.

## 8. Verification statement

The repository should be cited honestly as containing:

- paper proofs and exact computational certificates;
- a partial sorry-free Lean formalization of the algebraic core;
- no complete Lean proof of the continuum or hypergraph arguments;
- no solution of the full all-slope checkerboard NTIL limit.
