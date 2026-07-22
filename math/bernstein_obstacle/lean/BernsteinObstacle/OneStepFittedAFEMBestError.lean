import BernsteinObstacle.OneStepFittedAFEM
import BernsteinObstacle.GlobalSmoothSaturation
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Exact best-error collapse after one-step contact fitting

The one-step fitted algorithm already gives exact nonnegative coefficients on
both children.  This file adds the upper coefficient bound, packages the two
child vectors into the actual coefficient box, and proves that the genuine
metric best-approximation error is zero.
-/

/-- The normalized quadratic monomial coefficient does not exceed the lattice
fraction `k/p`. -/
theorem quadraticMonomialCoeff_le_indexFraction
    (p k : ℕ) (hp : 2 ≤ p) (hk : k ∈ Finset.range (p + 1)) :
    quadraticMonomialCoeff p k ≤ (k : ℝ) / (p : ℝ) := by
  have hkp : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkR : (k : ℝ) ≤ (p : ℝ) := by exact_mod_cast hkp
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : ((p : ℝ) - 1) ≠ 0 := by
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  unfold quadraticMonomialCoeff quadraticMomentDenominator
  rw [natCast_mul_pred p, natCast_mul_pred k]
  field_simp [hp0, hp1]
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hkR)]

/-- Every degree-`p` Bernstein coefficient of `t²` lies below one. -/
theorem quadraticMonomialCoeff_le_one
    (p k : ℕ) (hp : 2 ≤ p) (hk : k ∈ Finset.range (p + 1)) :
    quadraticMonomialCoeff p k ≤ 1 := by
  have hfrac := quadraticMonomialCoeff_le_indexFraction p k hp hk
  have hkp : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hp0 : 0 < (p : ℝ) := by positivity
  have hfrac1 : (k : ℝ) / (p : ℝ) ≤ 1 := by
    apply (div_le_one hp0).2
    exact_mod_cast hkp
  exact hfrac.trans hfrac1

/-- Every degree-`p` Bernstein coefficient of `(1-t)²` lies below one. -/
theorem oneMinusQuadraticCoeff_le_one
    (p k : ℕ) (hp : 2 ≤ p) (hk : k ∈ Finset.range (p + 1)) :
    oneMinusQuadraticCoeff p k ≤ 1 := by
  have hq := quadraticMonomialCoeff_le_indexFraction p k hp hk
  have hfrac0 : 0 ≤ (k : ℝ) / (p : ℝ) := by positivity
  unfold oneMinusQuadraticCoeff
  nlinarith

/-- If the original cell width is at most two, the square of either fitted
child's width is at most one. -/
theorem fittedHalfWidth_sq_le_one
    (h : ℝ) (hh0 : 0 ≤ h) (hh2 : h ≤ 2) :
    (h / 2) ^ 2 ≤ 1 := by
  have hhalf0 : 0 ≤ h / 2 := by positivity
  have hhalf1 : h / 2 ≤ 1 := by linarith
  have hprod : 0 ≤ (h / 2) * (1 - h / 2) :=
    mul_nonneg hhalf0 (sub_nonneg.mpr hhalf1)
  nlinarith

/-- Full box certificate for a fitted right-child coefficient. -/
theorem rightFittedQuadraticCoeff_mem_Icc
    (p k : ℕ) (h : ℝ) (hp : 2 ≤ p)
    (hk : k ∈ Finset.range (p + 1))
    (hh0 : 0 ≤ h) (hh2 : h ≤ 2) :
    rightFittedQuadraticCoeff p k h ∈ Set.Icc 0 1 := by
  have hbase0 := quadraticMonomialCoeff_nonneg p k hp
  have hbase1 := quadraticMonomialCoeff_le_one p k hp hk
  have hscale0 : 0 ≤ (h / 2) ^ 2 := sq_nonneg _
  have hscale1 := fittedHalfWidth_sq_le_one h hh0 hh2
  constructor
  · exact rightFittedQuadraticCoeff_nonneg p k h hp
  · unfold rightFittedQuadraticCoeff
    calc
      (h / 2) ^ 2 * quadraticMonomialCoeff p k ≤
          1 * quadraticMonomialCoeff p k :=
        mul_le_mul_of_nonneg_right hscale1 hbase0
      _ = quadraticMonomialCoeff p k := one_mul _
      _ ≤ 1 := hbase1

/-- Full box certificate for a fitted left-child coefficient. -/
theorem leftFittedQuadraticCoeff_mem_Icc
    (p k : ℕ) (h : ℝ) (hp : 2 ≤ p)
    (hk : k ∈ Finset.range (p + 1))
    (hh0 : 0 ≤ h) (hh2 : h ≤ 2) :
    leftFittedQuadraticCoeff p k h ∈ Set.Icc 0 1 := by
  have hbase0 := oneMinusQuadraticCoeff_nonneg p k hp hk
  have hbase1 := oneMinusQuadraticCoeff_le_one p k hp hk
  have hscale1 := fittedHalfWidth_sq_le_one h hh0 hh2
  constructor
  · exact leftFittedQuadraticCoeff_nonneg p k h hp hk
  · unfold leftFittedQuadraticCoeff
    calc
      (h / 2) ^ 2 * oneMinusQuadraticCoeff p k ≤
          1 * oneMinusQuadraticCoeff p k :=
        mul_le_mul_of_nonneg_right hscale1 hbase0
      _ = oneMinusQuadraticCoeff p k := one_mul _
      _ ≤ 1 := hbase1

/-- Coefficient space of the two children produced by the fitting step. -/
abbrev FittedQuadraticCoefficientPair (p : ℕ) :=
  (Fin (p + 1) → ℝ) × (Fin (p + 1) → ℝ)

/-- Exact coefficient vector of `x²` on the two fitted children. -/
def fittedQuadraticCoefficientPair (p : ℕ) (h : ℝ) :
    FittedQuadraticCoefficientPair p :=
  (fun k => leftFittedQuadraticCoeff p k h,
   fun k => rightFittedQuadraticCoeff p k h)

/-- Actual coefficient box on the fitted two-child patch. -/
def fittedQuadraticCoefficientBox (p : ℕ) :
    Set (FittedQuadraticCoefficientPair p) :=
  {c | (∀ k, c.1 k ∈ Set.Icc 0 1) ∧ (∀ k, c.2 k ∈ Set.Icc 0 1)}

/-- The exact quadratic coefficient vector belongs to the fitted box. -/
theorem fittedQuadraticCoefficientPair_mem_box
    (p : ℕ) (h : ℝ) (hp : 2 ≤ p) (hh0 : 0 ≤ h) (hh2 : h ≤ 2) :
    fittedQuadraticCoefficientPair p h ∈ fittedQuadraticCoefficientBox p := by
  constructor
  · intro k
    exact leftFittedQuadraticCoeff_mem_Icc p k h hp
      (Finset.mem_range.mpr k.isLt) hh0 hh2
  · intro k
    exact rightFittedQuadraticCoeff_mem_Icc p k h hp
      (Finset.mem_range.mpr k.isLt) hh0 hh2

/-- After one contact-fitting step, the genuine metric best-approximation error
of the exact fitted coefficient vector from the coefficient box is zero. -/
theorem oneStepFittedAFEM_bestApproximationError_eq_zero
    (p : ℕ) (h : ℝ) (hp : 2 ≤ p) (hh0 : 0 ≤ h) (hh2 : h ≤ 2) :
    bestApproximationError (fittedQuadraticCoefficientPair p h)
      (fittedQuadraticCoefficientBox p) = 0 := by
  unfold bestApproximationError
  exact Metric.infDist_zero_of_mem
    (fittedQuadraticCoefficientPair_mem_box p h hp hh0 hh2)

/-- Final benchmark theorem: the single geometric split is shape regular,
coefficient-feasible in the full `[0,1]` box, exactly reproduces both child
polynomials, and collapses the genuine best error to zero. -/
theorem oneStepFittedAFEM_complete
    (p : ℕ) (h : ℝ) (hp : 2 ≤ p)
    (hh0 : 0 ≤ h) (hh2 : h ≤ 2) (hhne : h ≠ 0) :
    bestApproximationError (fittedQuadraticCoefficientPair p h)
        (fittedQuadraticCoefficientBox p) = 0 ∧
    (∀ t, curve p (fun k => leftFittedQuadraticCoeff p k h) t =
      (-h / 2 + (h / 2) * t) ^ 2) ∧
    (∀ t, curve p (fun k => rightFittedQuadraticCoeff p k h) t =
      ((h / 2) * t) ^ 2) ∧
    h / (h / 2) = 2 := by
  constructor
  · exact oneStepFittedAFEM_bestApproximationError_eq_zero p h hp hh0 hh2
  constructor
  · exact leftFittedQuadratic_exact p hp h
  constructor
  · exact rightFittedQuadratic_exact p hp h
  · exact fittedCentral_neighbor_ratio h hhne

end

end BernsteinObstacle
