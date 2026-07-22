# Fitted-contact high-order restoration and adaptive strategy

## Local fitted-factorization theorem

Let `T` be a `d`-simplex and let the active interface be the face

```text
F={lambda_j=0},
```

where `lambda_j` is the associated barycentric coordinate. Fix `p>=2`.
Assume that on `T`

```text
u-m = lambda_j^2 a,
```

with `a>=a_0>0`. Let `A_{p-2}` be a degree-`p-2` Bernstein polynomial
approximation of `a` whose coefficients are nonnegative. Then

```text
R_T u = m + lambda_j^2 A_{p-2}
```

is a degree-`p` polynomial whose degree-`p` Bernstein coefficients all satisfy
the lower bound `m`.

If

```text
A_{p-2} = sum_{|beta|=p-2} c_beta B_beta^{p-2},
c_beta>=0,
```

then

```text
lambda_j^2 B_beta^{p-2}
 = ((beta_j+1)(beta_j+2)/(p(p-1)))
     B_{beta+2e_j}^p.
```

Thus the only nonzero degree-`p` gap coefficients are

```text
c_beta (beta_j+1)(beta_j+2)/(p(p-1)) >= 0.
```

The constant-amplitude specialization `a=constant` is certified in Lean by the
simplicial second-moment theorem.

## Optimal local `H^1` rate

Suppose `rho` is the physical affine normal coordinate on `T`, with

```text
rho = s_T lambda_j,
|rho| <= C h_T,
|grad rho| <= C,
```

and

```text
u-m = rho^2 a.
```

Let `A_h` be a degree-`p-2` approximation satisfying

```text
||a-A_h||_{L^2(T)} <= C h_T^{p-1}|a|_{H^{p-1}(T)},
||grad(a-A_h)||_{L^2(T)} <= C h_T^{p-2}|a|_{H^{p-1}(T)}.
```

Then

```text
u-R_Tu = rho^2(a-A_h),
```

and

```text
grad[rho^2(a-A_h)]
 = rho^2 grad(a-A_h)
   +2rho(a-A_h)grad rho.
```

Consequently

```text
||u-R_Tu||_{H^1(T)}
 <= C[h_T^2 h_T^{p-2}+h_T h_T^{p-1}]
      |a|_{H^{p-1}(T)}
 <= C h_T^p |a|_{H^{p-1}(T)}.
```

This is the mechanism by which a fitted mesh restores the full degree-`p`
energy rate despite quadratic contact. The two lost powers in approximating the
amplitude are exactly restored by the `rho^2` factor.

## Global fitted theorem

Let a shape-regular simplicial mesh fit the active interface, and assume:

1. the active set is a union of elements and its boundary is a union of mesh
   faces;
2. in a fitted tubular strip, `u-m=rho_h^2 a`, where `rho_h` is a continuous
   piecewise-affine level-set coordinate and `a>=a_0>0`;
3. the amplitude has a globally conforming degree-`p-2` approximation with
   nonnegative Bernstein coefficients and the estimates above;
4. away from the contact strip, `u` has a uniform lower-bound clearance, so the
   ordinary degree-`p` interpolant is coefficient-feasible for small `h`;
5. the two constructions agree on their common mesh skeleton, or are assembled
   through globally shared Bernstein degrees of freedom;
6. the prescribed boundary trace is represented exactly and kept fixed.

Then there is a globally conforming `R_hu in K_h^B` such that

```text
||u-R_hu||_{H^1(Omega)} <= C h^p.
```

The same statement applies to an upper contact set after replacing `u-m` by
`M-u`. Bilateral constraints are handled when the fitted lower and upper
contact strips are disjoint or have compatible local factorizations.

## Why ordinary refinement is insufficient

For an unfitted quadratic contact point or interface, repeated uniform
refinement can preserve the same interior phase. The local negative coefficient
then remains `-gamma_p h_T^2` on every level. Refinement decreases the error but
does not restore order `p`.

A successful adaptive algorithm must therefore have a geometric action, not
only a size action:

```text
REFINE_OR_FIT(T):
  if coefficient defect is too large for degree-p accuracy:
      insert/snap the detected contact geometry into the mesh skeleton;
  otherwise:
      perform ordinary residual-driven refinement.
```

## Contact-aware estimator

Let

```text
delta_T = max_alpha max((m-b_{T,alpha})_+,(b_{T,alpha}-M)_+).
```

Use

```text
eta_T^2
 = eta_res,T^2
 + C_B h_T^{d-2} delta_T^2
 + C_G eta_geom,T^2.
```

The scaling of the coefficient term follows from fixed-degree basis stability:
a coefficient correction of size `delta_T` contributes energy of order
`h_T^{d-2}delta_T^2`.

A rate-diagnostic marking condition is

```text
delta_T > C_target h_T^p.
```

Such an element cannot support degree-`p` recovery through a uniformly bounded
coefficient repair. If it intersects the detected contact interface, it should
be marked for fitting rather than blind bisection.

## Abstract contraction theorem

Once the following standard AFEM ingredients are established for the combined
estimator,

1. reliability;
2. estimator reduction on refined/fitted cells;
3. quasi-orthogonality of the constrained solutions;
4. discrete reliability;
5. Dörfler marking;
6. shape-regular closure and bounded fitting overhead;

there are constants `0<q<1` and `C>=1` such that the quasi-error

```text
Delta_l = ||u-u_l||_{H^1}^2 + mu eta_l^2
```

satisfies

```text
Delta_{l+1} <= q Delta_l,
Delta_l <= q^l Delta_0.
```

If the fitted approximation class has nonlinear approximation exponent `s`,
the usual overlay and complexity argument then yields

```text
||u-u_l||_{H^1}+eta_l
 <= C (#T_l-#T_0)^{-s}.
```

## Remaining hard analysis

The local coefficient theorem and the factorized rate mechanism are now clear.
A complete AFEM paper still has to prove, for a specified fitting algorithm:

1. stable detection and approximation of a curved free boundary;
2. preservation of conformity and shape regularity after snapping/insertion;
3. reliability and efficiency of the geometry/coefficient estimator;
4. quasi-orthogonality for changing inner cones;
5. bounded mesh-closure and geometry-fitting complexity;
6. instance optimality or rate optimality.

Those are algorithmic/geometric theorems, not gaps in the local Bernstein
coefficient algebra.
