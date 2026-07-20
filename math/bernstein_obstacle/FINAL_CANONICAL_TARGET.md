# Final canonical Bernstein–Bézier obstacle target

This file freezes the single canonical review target after consolidating all
verified and internally audited Bernstein branches.

## Included theorem layers

- complete-element Bernstein positivity and interval certificates;
- arbitrary-simplex bases and all-degree lattice unisolvence;
- oriented shared-face conformity and homogeneous boundary traces;
- clipping as a feasible Euclidean projection with KKT, complementarity,
  Pythagorean, and nonexpansive properties;
- assembled obstacle energies, minimizer transfer, weak closure, and Mosco
  infrastructure;
- constructive scheduled recovery and automatic threshold extraction from
  eventual FEM feasibility/convergence;
- translated moving-obstacle Mosco convergence;
- Hilbert-space and monotone-operator inner-cone convergence layers;
- corrected local-distance coefficient localization and physical-boundary
  linear-growth domination;
- codimension-growth repair laws, consistency saturation, and optimal grading;
- terminal moving-obstacle grand theorems;
- exact phase-locked integral identity and matching three-halves clipping lower
  model.

## Canonical terminal declarations

- `bernsteinBezierObstacleGrandTheorem`;
- `bernsteinBezierObstacleGrandTheorem_quadraticContact`;
- `BilateralBarrierEnvelopeData.grandBarrier_mosco_and_hilbertConvergence`;
- `AsymptoticSobolevFEMRecoveryData.moscoConverges`;
- `AsymptoticSobolevFEMRecoveryData.minimizers_strongConvergence`;
- `intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity`;
- `phaseLockedQuadraticSlopeEnergy_lowerBound`;
- `threeHalvesContactLaw`;
- `balancedContactOrder_equalizes`.

## Verification rule

The canonical target is accepted internally only after the pinned workflow:

1. builds the complete `BernsteinObstacle` library;
2. runs every terminal audit, including `GrandCanonicalAudit.lean`;
3. rejects `sorryAx`;
4. finds every canonical terminal theorem in the axiom transcript;
5. completes the deterministic numerical reproduction workflow.

## Trust boundary

The formal package proves the abstract and algebraic theorem chain. The
concrete physical Sobolev recovery estimates, moving mesh geometry,
free-boundary regularity hypotheses, independent novelty review, and genuine
third-party clean-room reproduction remain separate external obligations.
