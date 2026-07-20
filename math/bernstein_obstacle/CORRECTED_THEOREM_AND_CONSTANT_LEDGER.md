# Corrected sharp theorem and constant-dependence ledger

## Theorem statement

Let `Omega` be a bounded polyhedral Lipschitz domain, let `r >= 1` be fixed,
and let `{T_h}` be a conforming uniformly shape-regular simplicial mesh family.
Let `u` solve the homogeneous-obstacle variational inequality for a symmetric
continuous coercive bilinear form `a` and load `F`. Let `u_h^B` be the minimizer
over the conforming Bernstein coefficient cone.

Assume the interior free boundary

```text
Gamma = boundary({u > 0}) intersect Omega
```

is compact and regular and the following hypotheses hold uniformly along the
mesh family.

### A. Continuous problem

1. `u in C^{1,1}` near `Gamma`, with `u = grad u = 0` on `Gamma`.
2. On the positive side of a fixed tubular neighborhood,

   ```text
   c0 dist(x,Gamma)^2 <= u(x) <= C0 dist(x,Gamma)^2.
   ```

3. A one-sided `H^{r+1}` extension exists on that neighborhood with norm at
   most `M_ext`, independently of the mesh.
4. Outside the interface patch,

   ```text
   sum_{T notin omega_h} |u|_{H^{r+1}(T)}^2 <= M_reg^2.
   ```

5. The multiplier has a nonnegative density `lambda in L^infinity`, supported
   on the contact set, with norm at most `M_lambda`.

### B. Corrected local grading

For a fixed `kappa > 1`, define

```text
R_h = {T : dist(T,Gamma) <= kappa h_T}.
```

Let `omega_h` be a fixed-ring enlargement of `R_h`. Assume

```text
c_m h_Gamma <= h_T <= C_m h_Gamma   for T in omega_h,
|omega_h| <= C_Gamma h_Gamma.
```

Outside `omega_h`, let

```text
h = max h_T.
```

The mesh family is isotropic and uniformly shape regular. Anisotropic elements
are not covered by this theorem.

### C. Physical boundary

Either the free-boundary patch is separated from the physical boundary by a
contact collar, or positive boundary elements satisfy a uniform inward linear
lower bound. Boundary-face coefficients are exactly zero; the lower bound is
used only for off-face lattice points.

### D. Exact obstacle representation

The problem is shifted to a zero-gap formulation and the discrete obstacle is
represented exactly. Inexact obstacles require an additional consistency term.

## Conclusion

There exists a constant `C`, independent of `h` and `h_Gamma`, such that

```text
||u - u_h^B||_{H^1(Omega)}
  <= C (h^r + h_Gamma^(3/2)).
```

## Explicit localization threshold

Let `C_coeff` be the uniform constant in

```text
|b_{T,alpha}(I_T^r u) - u(x_{T,alpha})|
  <= C_coeff h_T^2.
```

A sufficient local-distance threshold is any `kappa` for which

```text
C_coeff <= c0 (kappa - 1)^2.
```

Thus one may choose

```text
kappa >= 1 + sqrt(C_coeff / c0).
```

The conservative subtraction by one element diameter also covers formulations
where distance is measured from an element representative rather than as the
minimum distance of the complete element.

## Allowed dependence of the final constant

The final constant may depend on:

- ambient dimension `d` and fixed polynomial degree `r`;
- domain and fixed tubular-neighborhood geometry;
- the continuity and coercivity constants of `a`;
- mesh shape-regularity and fixed-ring constants;
- `c0`, `C0`, `M_ext`, `M_reg`, and `M_lambda`;
- `c_m`, `C_m`, `C_Gamma`, and the chosen `kappa`;
- reference-element Bernstein norm-equivalence and collocation-inverse
  constants;
- the physical-boundary lower-growth constant when that alternative is used.

It must not depend on:

- the global mesh index;
- `h` or `h_Gamma`;
- the number of interface elements;
- the phase position of `Gamma` relative to an individual element.

## Proof dependency chain

1. Fixed-degree collocation stability and affine cancellation give the
   coefficient-to-value error `C_coeff h_T^2`.
2. The chosen `kappa` and quadratic lower growth force nonnegative coefficients
   outside `R_h`.
3. Quadratic upper growth and local quasi-uniformity give coefficient amplitude
   `O(h_Gamma^2)` on `omega_h`.
4. Shared global clipping preserves conformity, boundary traces, and pointwise
   feasibility.
5. Per-element squared `H^1` repair energy is `O(h_Gamma^(d+2))`.
6. The codimension-one patch contains `O(h_Gamma^{-(d-1)})` elements, giving
   total squared repair energy `O(h_Gamma^3)`.
7. Uniform broken regularity supplies the bulk `O(h^r)` interpolation term.
8. Bounded multiplier density contributes `O(h_Gamma^3)` to the energy/Falk
   estimate.
9. Coercivity and square-root transfer give the stated minimizer rate.

## Exclusions

The theorem does not cover singular or degenerate free-boundary points,
boundary-touching free boundaries without a separate analysis, anisotropic
meshes, arbitrary inexact obstacles, measure-valued multipliers, nonsymmetric
operators, or optimal adaptive complexity.
