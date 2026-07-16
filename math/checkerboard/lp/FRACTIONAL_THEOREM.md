# Checkerboard four-direction fractional LP asymptotics

## Scope

This document concerns only the fractional packing LP using rows, columns, and the two diagonal families of slopes `+1` and `-1`. It does not assert the integral all-slope no-three-in-line conjecture.

For a parity class of an `n x n` checkerboard, put a nonnegative weight on each point and require total weight at most two on every row, column, slope-`+1` diagonal, and slope-`-1` diagonal. Let `L4(n, eps)` be the optimum. For odd side length `2m+1`, write `F_m` for the fat parity class and `T_m` for the thin parity class. For even side length `2m`, write `E_m`; the two parity classes are equivalent by reflection.

Let `p` be the unique root in

```text
2115883 / 10000000 < p < 2115884 / 10000000
```

of

```text
401 p^3 - 331 p^2 + 19 p + 7 = 0,
```

and define

```text
alpha = 2 (1 - p).
```

Equivalently,

```text
401 alpha^3 - 1744 alpha^2 + 2240 alpha - 768 = 0,
```

with `alpha = 1.576823396873808...`.

## Fractional theorem

The intended kernel-checked theorem is

```text
lim_{m -> infinity} F_m / (2m+1) = alpha,
lim_{m -> infinity} T_m / (2m+1) = alpha,
lim_{m -> infinity} E_m / (2m)   = alpha.
```

The proof has four logically separate layers.

## 1. Continuum primal and dual

Let

```text
T = {(x,y) in R^2 : 0 <= y, y <= x, x+y <= 1}.
```

For a finite nonnegative Borel measure `mu` on `T`, define paired pushforwards

```text
P_A mu = x_# mu + (1-y)_# mu,
P_B mu = (x+y)_# mu + (x-y)_# mu.
```

The continuum primal maximizes `mu(T)` subject to

```text
P_A mu <= 4 lambda,
P_B mu <= 4 lambda,
```

where `lambda` is Lebesgue measure on `[0,1]`.

The continuum dual minimizes

```text
4 * integral_0^1 (A(t)+B(t)) dt
```

over nonnegative functions `A,B` satisfying

```text
A(x) + A(1-y) + B(x+y) + B(x-y) >= 1
```

for all `(x,y)` in `T`.

Weak duality follows by integrating the obstacle inequality against a primal-feasible measure and applying the two pushforward domination inequalities.

## 2. Exact dual certificate

Prellberg's ancillary certificate gives exact piecewise polynomial functions `A` and `B`. Its verification data consists of:

- the exact breakpoints and algebraic constants in `Q(p)`;
- a triangulation of the continuum triangle into 40 exact triangles;
- the degree-two Bernstein coefficients of the obstacle polynomial on each triangle;
- exact sign checks proving every required coefficient nonnegative;
- exact integral identities giving objective `alpha`.

The Lean formalization must not trust the Python verifier. The generated Lean certificate is required to check every algebraic identity and sign in the kernel.

## 3. Exact primal certificate

Define

```text
c = (187 p^3 - 211 p^2 + 61 p - 5)
    / (2 * (71 p^2 - 66 p + 11)),
d = 1 + p - c,
e = (2 c + 3 p - 1) / 4,
f = (-2 c + 5 p + 1) / 4,
g = (1 - 3 p + 2 c) / 2,
L = c-p,
M = d-c.
```

The exact identities include

```text
L = 1-d,
M = 4(f-p),
p-e = f-p,
4L + 2M = alpha.
```

The primal certificate is `mu_Q + mu_L`.

### Outer block

Put

```text
r = p/L,
q = (f-p)/L,
h = (g-p)/L,
E = [0, q, 1-r, h-1, r, (h-q)/2, (h+q)/2, 1].
```

The outer certificate is a probability measure formed from 35 positively weighted affine couplings of intervals whose endpoints lie in `E`. Its exact table is `q_weights_exact.csv`. Kernel verification must establish:

1. the 35 weights are positive and sum to one;
2. both coordinate marginals are exactly uniform on `[0,1]`;
3. the sum and difference pushforward densities add to the indicator of `[-r,-q] union [q,h]`;
4. every component maps into `T` under `(a,b) |-> (p+La,Lb)`.

After multiplying by `4L`, this block has mass `4L` and saturates the appropriate portions of both paired projection constraints.

### Middle block

The middle certificate is a seven-component rational mixture of affine one-parameter couplings. Its component weights are

```text
19/90, 7/90, 1/5, 1/45, 7/45, 1/6, 1/6.
```

The interval data is finite and rational. Kernel verification must establish its uniform marginals, its exact active diagonal marginal, the bound on the inactive diagonal marginal, support in `T`, and total mass `2M`.

Thus the full primal certificate has mass

```text
4L + 2M = alpha.
```

Together with the exact dual certificate and weak duality, the continuum primal and dual optima are both exactly `alpha`.

## 4. Continuum-to-finite transfer

The lower transfer is not a numerical extrapolation. It uses a four-direction cardinal box spline.

Let `phi` be the convolution of the uniform probability measures on the centered segments in directions

```text
(1,0), (0,1), (1,1), (1,-1).
```

The integer translates of `phi` form a partition of unity almost everywhere. Summing `phi` over an integer fibre of any of the four primitive linear forms produces a nonnegative compactly supported one-dimensional kernel of integral one.

For an interior-truncated continuum feasible measure `mu`, define reduced odd-fat finite weights by

```text
z_m(u,v) = 2m * integral phi(mz-(u,v)) dmu(z)
```

on the strict interior of the reduced triangular index set. Fubini/Tonelli and the fibre-kernel identities give every finite row/column/diagonal capacity exactly. The endpoint constraints are zero because boundary indices are omitted.

The partition of unity, zero boundary mass of the explicit segment certificate, and dominated convergence give

```text
(1/(2m)) * sum_{u,v} z_m(u,v) -> mu(T).
```

Hence

```text
liminf F_m/(2m+1) >= alpha.
```

For the upper transfer, sample the exact continuum dual at the finite grid. Each finite obstacle inequality is literally the continuum obstacle inequality at the corresponding scaled point. The objective is a Riemann sum for the exact piecewise-polynomial dual, giving

```text
limsup F_m/(2m+1) <= alpha.
```

Therefore the odd-fat limit is `alpha`.

The odd-thin and even limits are transferred either by their shifted meshes directly or by exact bounded boundary comparisons. Since the boundary difference is `O(1)`, division by the side length makes it vanish.

## Formal completion criterion

This theorem is complete only when all of the following are true:

- the exact primal and dual finite certificate data are checked by Lean rather than asserted;
- weak duality is proved for the concrete measure/function definitions;
- the box-spline fibre identities, finite feasibility, and dominated-convergence objective limit are formalized;
- the upper Riemann-sum transfer is formalized;
- all three normalized limits compile;
- `#print axioms` shows no `sorryAx` and no project-specific axiom.
