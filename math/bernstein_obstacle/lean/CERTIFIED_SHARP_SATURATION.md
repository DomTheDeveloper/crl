# Certified Bernstein–Bézier quadratic-contact saturation theorem

## Final formal endpoint

The Lean declaration

```text
BernsteinObstacle.bernsteinBezier_quadraticContact_fullSpace_threeHalvesSaturation
```

proves an explicit two-sided estimate on the asymptotic range `0 < h <= 1`:

```text
0 < c_lower,
c_lower * (h * sqrt h) <= ||actual - approx||,
||actual - approx|| <= C_upper * (h * sqrt h).
```

Here

```text
c_lower = sqrt(mappedQuadraticHingeLocalConstant J0 amplitude eta M * N) / 2
C_upper = 3 * sqrt(max P (max A B) / alpha).
```

The lower coefficient is proved strictly positive from positive Jacobian,
quadratic-contact amplitude, phase-separation, tangential-mass, and retained
interface-count constants.

## Formal dependency chain

1. Exact best approximation of the half-quadratic hinge by every scalar
   quadratic polynomial.
2. Restriction of coordinate-free quadratic polynomials to affine transverse
   lines.
3. Transverse-prism integration and mapped Jacobian transfer.
4. Codimension-one cut-patch summation.
5. Interface-cover lower cardinality.
6. Higher-order free-boundary remainder absorption.
7. Direct normed-space physical lower bound.
8. Quadratic-contact upper energy estimate.
9. Formal absorption of both `h^2` bulk terms into `h * sqrt h` for
   `0 <= h <= 1`.

## Verification contract

The dedicated workflow:

```text
.github/workflows/bernstein-sharp-sandwich-audit.yml
```

must, on the exact reviewed head:

- build the complete `BernsteinObstacle` library;
- build the non-root normed physical endpoint;
- build the final sharp-sandwich endpoint;
- compile `SharpQuadraticSaturationAudit.lean`;
- print the axioms of both new declarations;
- fail if `sorryAx` appears.

## Exact scientific scope

This is a complete conditional sharp-saturation theorem.  It does not hide the
application boundary.  A concrete obstacle PDE and mesh family must verify the
explicit hypotheses supplied to the theorem, including:

- retained transverse prisms on the selected cut elements;
- uniform positive phase, tangential-mass, and Jacobian constants;
- the interface-cover estimate;
- the local quadratic-contact decomposition;
- the higher-order remainder estimate;
- the upper energy inequality.

Once those hypotheses are established for an application, the two-sided
`h^(3/2)` conclusion follows without any additional unproved formal step.
