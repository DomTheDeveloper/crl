# Scope addendum for the Grand Positive-Basis Constraint Theorem

This addendum is normative for `GRAND_THEOREM_V3_UNIFIED.md`.

1. Radon-measure pairings use quasi-continuous Sobolev representatives. For the continuous Bernstein recovery difference, this agrees with the ordinary Radon integral.
2. The identity `grad g = 0` is used only at interior contact points. The active-set closure may reach the physical boundary, but no boundary multiplier is included.
3. The local contact indicator is `q_h(x)=max_{T: x in closure(T)} h_T omega_T(h_T)`, the maximum over elements incident to `x`; the shorthand printed in the main V3 document is superseded by this definition.
4. The sampling/conformity theorem assumes affine shape-regular simplices and a fixed degree shared across each face.
5. Nonpolynomial shifted trial sets are finite-dimensional affine sets, but the theorem assumes exact variational integration. Quadrature requires a separate perturbation estimate.
6. For nonsymmetric coercive operators, the discrete object is a variational-inequality solution, not an energy minimizer.
7. The Minkowski law is conditional on coefficient localization, repair amplitude, inverse stability, and tubular-volume hypotheses.
8. The current Lean layer formalizes integer vanishing orders and integer codimensions. Real exponents in the manuscript remain analytical.
9. The `3/2` lower bound is sharp only for the stated phase-locked unfitted coefficientwise-clipping class.
10. Bilateral rates require a positive obstacle width in `W^{1,infinity}` and a homogeneous normalized trace or exact normalized boundary lift.
11. The complete function-space unilateral/bilateral rates, PDE-specific measure representation, and reference-simplex Sobolev modulus estimate remain analytical review targets.
