# Literature and mesh-alignment audit

## What Kirby--Shapero already observed

Kirby--Shapero explicitly note that a pointwise positive quadratic can have a
negative Bernstein coefficient.  Their equation (38) is

```text
p(x) = B_0^2(x) - 0.9 B_1^2(x) + B_2^2(x)
     = 3.8 x^2 - 3.8 x + 1,
```

whose minimum is `0.05` at `x=1/2`.  They therefore state that the
coefficient-bounded finite-element cone cannot reproduce every positive quadratic
and that standard Bramble--Hilbert polynomial reproduction cannot be invoked.
They also observe that subdividing `[0,1]` into the two half intervals removes this
particular obstruction.

The new result in `SMOOTH_QUADRATIC_CONTACT_SATURATION.md` is not the elementary
fact that positive polynomials can have negative Bernstein coefficients.  The new
step is the asymptotic mesh-family conclusion:

```text
for a bound-touching quadratic and a phase-locked shape-regular refinement family,
the negative coefficient persists with size gamma_p h^2,
and the best coefficient-feasible H^1 error is Theta(h^2).
```

This resolves the rate question negatively for `p>2`.

## Why strict positivity and contact behave differently

For the paper's equation (38), the minimum is strictly positive.  Under mesh
refinement, the local variation becomes small relative to the fixed positive margin,
so all local coefficients eventually become positive.

For

```text
u(x)=x^2,
```

the minimum is exactly the active bound.  On every element where the zero remains
at a nonvertex phase, the degree-`p` coefficient defect is a fixed phase constant
times `h^2`.  Refinement shrinks the defect but does not change its sign.  Therefore
strict-margin arguments do not apply.

## Why the published optimal-rate experiment does not test the obstruction

The manufactured solution used for the convergence experiment is

```text
u(x,y) = exp(2xy) sin^2(pi x) sin^2(2 pi y).
```

Its zero sets include the domain boundary and the interior line

```text
y = 1/2.
```

The experiments use `N x N` meshes with

```text
N = 2^i.
```

Hence `y=1/2` is a mesh line at every refinement level.  The principal interior
contact set is exactly aligned with the mesh skeleton.  The experiment therefore
supports optimal convergence on an aligned family; it does not rule out saturation
on phase-misaligned mesh families.

This also explains why the numerical result and the new negative theorem are
compatible.

## Three distinct regimes

### 1. Strict interior margin

If

```text
m+delta <= u <= M-delta,
```

then standard interpolation is coefficient-feasible for all sufficiently small `h`,
so the usual `O(h^p)` rate is expected.

### 2. Bound contact aligned with the mesh

If the contact set lies in the mesh skeleton, piecewise polynomial branches can be
represented separately.  The coefficient obstruction may disappear entirely.

### 3. Bound contact at a persistent interior phase

For quadratic contact, the coefficient defect is `Theta(h^2)`.  For `p>2`, the
coefficient cone can therefore saturate at second order even for an analytic target
that the unconstrained space reproduces exactly.

## Audit of the existing `h^(3/2)` formal theorem

The certified theorem

```text
bernsteinBezier_quadraticContact_fullSpace_threeHalvesSaturation
```

uses a half-quadratic hinge and assumes a cut-patch local energy lower bound.  The
profile has a jump in its second derivative, so an unfitted polynomial space already
has an `h^(3/2)` `H^1` approximation barrier.  This is a free-boundary regularity and
phase theorem.

It must not be presented as proving that smooth coefficient-constrained recovery
saturates at `h^(3/2)`.  The analytic target `x^2` yields the distinct pure
coefficient-cone saturation scale `h^2`.

## Corrected literature-level conclusion

The open question has a two-part answer:

1. Qualitative density and Mosco convergence can still hold because the bounded
   piecewise-linear cone embeds in every degree-`p` Bernstein cone.
2. Uniform fixed-degree `O(h^p)` approximation for all smooth bound-touching
   functions is false for `p>2`; a phase-misaligned quadratic contact gives sharp
   second-order saturation.

Optimal high-order convergence requires an additional hypothesis such as strict
clearance, contact order at least `p`, mesh/interface alignment, or an adaptive
refinement rule that eliminates persistent bad phases.
