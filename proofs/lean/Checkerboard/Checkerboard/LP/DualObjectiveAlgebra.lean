import Checkerboard.LP.DualProfilePositivity

/-!
# Exact algebra of the continuum dual objective

The piecewise polynomial integrals reduce to two elements of `ℚ(p)`.  This file
checks those reductions directly against the defining cubic.  The analytic
module only needs to prove that the actual integrals equal the displayed finite
antiderivative formulas.
-/

namespace Checkerboard

noncomputable section

/-- Antiderivative of `a + b t + c t²`. -/
def quadraticPrimitive (a b c t : ℝ) : ℝ :=
  a * t + b * t ^ 2 / 2 + c * t ^ 3 / 3

/-- Exact finite antiderivative formula for the row/column profile. -/
def certifiedDualAIntegralFormula : ℝ :=
  (quadraticPrimitive certifiedDualN1 (-2 * certifiedDualR) (-certifiedDualK) primalC -
    quadraticPrimitive certifiedDualN1 (-2 * certifiedDualR) (-certifiedDualK)
      checkerboardP) +
  (quadraticPrimitive certifiedDualNu certifiedDualEll 0 primalD -
    quadraticPrimitive certifiedDualNu certifiedDualEll 0 primalC) +
  (quadraticPrimitive certifiedDualN2 (2 * certifiedDualK) (-certifiedDualK) 1 -
    quadraticPrimitive certifiedDualN2 (2 * certifiedDualK) (-certifiedDualK) primalD)

/-- Exact finite antiderivative formula for the diagonal profile. -/
def certifiedDualBIntegralFormula : ℝ :=
  (quadraticPrimitive certifiedDualS certifiedDualR (certifiedDualK / 2) primalE -
    quadraticPrimitive certifiedDualS certifiedDualR (certifiedDualK / 2) 0) +
  (quadraticPrimitive certifiedDualQ (-certifiedDualEll) 0 primalF -
    quadraticPrimitive certifiedDualQ (-certifiedDualEll) 0 primalE) +
  (quadraticPrimitive certifiedDualS certifiedDualR (certifiedDualK / 2) primalG -
    quadraticPrimitive certifiedDualS certifiedDualR (certifiedDualK / 2) primalF)

/-- Reduced value of the row/column integral. -/
def certifiedDualAIntegralRep : CubicRep :=
  ⟨(21723 / 35188 : ℚ), (-32933 / 17594 : ℚ), (54919 / 35188 : ℚ)⟩

/-- Reduced value of the diagonal integral. -/
def certifiedDualBIntegralRep : CubicRep :=
  ⟨(-4129 / 35188 : ℚ), (12068 / 8797 : ℚ), (-54919 / 35188 : ℚ)⟩

/-- Exact reduction of the row/column antiderivative expression. -/
theorem certifiedDualAIntegralFormula_reduced :
    certifiedDualAIntegralFormula = certifiedDualAIntegralRep.eval := by
  have hp := checkerboardP_root
  simp [pPoly] at hp
  simp [certifiedDualAIntegralFormula, quadraticPrimitive,
    certifiedDualAIntegralRep, certifiedDualK, certifiedDualR,
    certifiedDualEll, certifiedDualN1, certifiedDualNu, certifiedDualN2,
    certifiedDualKRep, certifiedDualRRep, certifiedDualEllRep,
    certifiedDualN1Rep, certifiedDualNuRep, certifiedDualN2Rep,
    primalC_reduced, primalD_reduced, CubicRep.eval]
  linear_combination
    (-((613345183912 * checkerboardP ^ 5 -
        1049711179214 * checkerboardP ^ 4 +
        636927045547 * checkerboardP ^ 3 -
        139246955519 * checkerboardP ^ 2 +
        77714449 * checkerboardP + 2301122929) / 69510093696)) * hp

/-- Exact reduction of the diagonal antiderivative expression. -/
theorem certifiedDualBIntegralFormula_reduced :
    certifiedDualBIntegralFormula = certifiedDualBIntegralRep.eval := by
  have hp := checkerboardP_root
  simp [pPoly] at hp
  simp [certifiedDualBIntegralFormula, quadraticPrimitive,
    certifiedDualBIntegralRep, certifiedDualK, certifiedDualR,
    certifiedDualS, certifiedDualEll, certifiedDualQ,
    certifiedDualKRep, certifiedDualRRep, certifiedDualSRep,
    certifiedDualEllRep, certifiedDualQRep,
    primalE_reduced, primalF_reduced, primalG_reduced, CubicRep.eval]
  linear_combination
    ((1533362959780 * checkerboardP ^ 5 -
        1926808112963 * checkerboardP ^ 4 +
        769334563258 * checkerboardP ^ 3 -
        33254103524 * checkerboardP ^ 2 -
        12485834270 * checkerboardP - 1897053209) / 556080749568) * hp

/-- The two exact integral representatives sum to `(1-p)/2`. -/
theorem certifiedDualIntegralFormula_sum :
    certifiedDualAIntegralFormula + certifiedDualBIntegralFormula =
      (1 - checkerboardP) / 2 := by
  rw [certifiedDualAIntegralFormula_reduced,
    certifiedDualBIntegralFormula_reduced]
  norm_num [certifiedDualAIntegralRep, certifiedDualBIntegralRep, CubicRep.eval]
  ring

/-- Therefore the exact real dual objective is the checkerboard constant. -/
theorem certifiedDualIntegralFormula_objective :
    4 * (certifiedDualAIntegralFormula + certifiedDualBIntegralFormula) =
      checkerboardAlpha := by
  rw [certifiedDualIntegralFormula_sum]
  simp [checkerboardAlpha]
  ring

end

end Checkerboard
