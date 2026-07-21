# Bernstein–Bézier final-five-percent closure

Date: 2026-07-20

Branch: `formal/bernstein-final-five-percent-v2`

Base: canonical grand-theorem head `ba1c762ce1c06633fd5f31c0fb6269048ec82929`

## Gap closed

The previous terminal theorem required an explicit threshold-form recovery
package. A physical finite-element proof normally does not construct those
thresholds as primary data. Instead, for each fixed smooth target it proves:

1. strong FEM recovery error tends to zero as the mesh is refined;
2. the recovery is eventually feasible.

The new `AsymptoticGrandTheorem.lean` eliminates that artificial interface.
`AsymptoticSobolevFEMRecoveryData` now feeds directly into:

- moving-obstacle Mosco convergence;
- strong convergence of constrained minimizers;
- the full consistency-limited codimension-growth grand theorem;
- the sharp quadratic-contact theorem with contact term
  `hGamma * sqrt hGamma`.

## Stronger clearance closure

The new `ClearanceRecovery.lean` removes eventual feasibility as an independent
assumption. It formalizes the standard physical argument:

- each fixed smooth recovery stage has a strictly positive obstacle clearance;
- the FEM recovery converges strongly to the smooth stage;
- once the recovery error is below the clearance, discrete feasibility follows;
- convergence to zero makes that inequality hold eventually.

Thus a `ClearanceSobolevFEMRecoveryData` package canonically produces
`AsymptoticSobolevFEMRecoveryData`, and therefore the entire moving-obstacle and
sharp-rate grand theorem stack.

## New terminal declarations

- `eventually_norm_lt_clearance`;
- `ClearanceSobolevFEMRecoveryData.toAsymptoticData`;
- `ClearanceSobolevFEMRecoveryData.moscoConverges`;
- `ClearanceSobolevFEMRecoveryData.minimizers_strongConvergence`;
- `AsymptoticSobolevFEMRecoveryData.movingObstacle_moscoConverges`;
- `AsymptoticSobolevFEMRecoveryData.movingObstacle_minimizers_strongConvergence`;
- `AsymptoticSobolevFEMRecoveryData.bernsteinBezierObstacleGrandTheorem`;
- `AsymptoticSobolevFEMRecoveryData.bernsteinBezierObstacleGrandTheorem_quadraticContact`;
- the corresponding four `ClearanceSobolevFEMRecoveryData` moving/grand endpoints.

Every declaration is imported by the root library, checked and axiom-printed by
`GrandCanonicalAudit.lean`, required by the workflow transcript, and covered by
the no-`sorryAx` gate.

## Mathematical significance

This changes the recovery spine from

```text
hand-supplied threshold schedule
  -> diagonal recovery
  -> Mosco/minimizer/grand theorem
```

to

```text
strict smooth clearance + ordinary FEM convergence
  -> eventual feasibility
  -> extracted threshold schedule
  -> moving Mosco convergence
  -> strong minimizer convergence
  -> sharp codimension-growth grand theorem.
```

The threshold and eventual-feasibility steps are now theorems rather than
external bookkeeping assumptions.

## Remaining physical trust boundary

This branch does not pretend to manufacture a complete Sobolev/FEM library.
A fully concrete PDE instantiation still must provide:

1. the actual ambient `H₀¹(Ω)` or `W₀^{1,p}(Ω)` space;
2. strict nonnegative or bilateral smooth density yielding the positive
   clearance used above;
3. a conforming shape-regular simplicial mesh family and assembled recovery;
4. the scaled local/global interpolation convergence estimate;
5. the PDE-specific multiplier, free-boundary geometry, and energy inequality.

The logical route from those standard analytical inputs to the final theorem is
now closed in Lean. Exact-head compilation and axiom inspection remain the next
certification gate.
