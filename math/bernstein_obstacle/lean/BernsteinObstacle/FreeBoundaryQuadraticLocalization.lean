import BernsteinObstacle.CoefficientLocalization
import BernsteinObstacle.Core
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Quadratic-growth free-boundary localization

These lemmas combine the coefficient-to-value `O(h^2)` estimate with quadratic
nondegeneracy of the positive phase.  They prove that a negative coefficient can
only occur in a strip of width `κ h`, and that the clipping correction has the
same quadratic amplitude as the risky coefficient.
-/

/-- Quadratic growth dominates a quadratic coefficient error outside a
`κ h` interface strip. -/
theorem coefficient_nonneg_of_quadratic_growth
    (b v errorConstant growthConstant kappa h dist : ℝ)
    (herrorConstant : 0 ≤ errorConstant)
    (hgrowthConstant : 0 ≤ growthConstant)
    (hkappa : 0 ≤ kappa) (hh : 0 ≤ h) (hdist : 0 ≤ dist)
    (hcoefficientError : |b - v| ≤ errorConstant * h ^ 2)
    (hquadraticGrowth : growthConstant * dist ^ 2 ≤ v)
    (houtside : kappa * h ≤ dist)
    (hdominates : errorConstant ≤ growthConstant * kappa ^ 2) :
    0 ≤ b := by
  have hscale : 0 ≤ h ^ 2 := sq_nonneg h
  have hkappaH : 0 ≤ kappa * h := mul_nonneg hkappa hh
  have hdistSq : (kappa * h) ^ 2 ≤ dist ^ 2 := by
    have hproduct : 0 ≤ (dist - kappa * h) * (dist + kappa * h) :=
      mul_nonneg (sub_nonneg.mpr houtside) (add_nonneg hdist hkappaH)
    nlinarith
  have hconstantScale :
      errorConstant * h ^ 2 ≤ (growthConstant * kappa ^ 2) * h ^ 2 :=
    mul_le_mul_of_nonneg_right hdominates hscale
  have hgrowthScale :
      (growthConstant * kappa ^ 2) * h ^ 2 ≤
        growthConstant * dist ^ 2 := by
    calc
      (growthConstant * kappa ^ 2) * h ^ 2 =
          growthConstant * (kappa * h) ^ 2 := by ring
      _ ≤ growthConstant * dist ^ 2 :=
        mul_le_mul_of_nonneg_left hdistSq hgrowthConstant
  have herrorLeValue : errorConstant * h ^ 2 ≤ v :=
    hconstantScale.trans (hgrowthScale.trans hquadraticGrowth)
  exact coefficient_nonneg_of_abs_sub_le
    b v (errorConstant * h ^ 2) hcoefficientError herrorLeValue

/-- Contrapositive localization: under quadratic nondegeneracy, every negative
coefficient belongs to the `κ h` strip. -/
theorem distance_lt_stripWidth_of_coefficient_neg
    (b v errorConstant growthConstant kappa h dist : ℝ)
    (herrorConstant : 0 ≤ errorConstant)
    (hgrowthConstant : 0 ≤ growthConstant)
    (hkappa : 0 ≤ kappa) (hh : 0 ≤ h) (hdist : 0 ≤ dist)
    (hcoefficientError : |b - v| ≤ errorConstant * h ^ 2)
    (hquadraticGrowth : growthConstant * dist ^ 2 ≤ v)
    (hdominates : errorConstant ≤ growthConstant * kappa ^ 2)
    (hb : b < 0) :
    dist < kappa * h := by
  by_contra hnot
  have houtside : kappa * h ≤ dist := le_of_not_gt hnot
  have hbnonneg := coefficient_nonneg_of_quadratic_growth
    b v errorConstant growthConstant kappa h dist
    herrorConstant hgrowthConstant hkappa hh hdist
    hcoefficientError hquadraticGrowth houtside hdominates
  linarith

/-- Clipping changes a scalar coefficient by at most its absolute value. -/
theorem abs_clip_sub_le_abs (b : ℝ) :
    |clip b - b| ≤ |b| := by
  by_cases hb : 0 ≤ b
  · simp [clip, max_eq_left hb]
  · have hb' : b < 0 := lt_of_not_ge hb
    simp [clip, max_eq_right (le_of_lt hb'), abs_of_neg hb']

/-- A risky coefficient of quadratic amplitude produces a clipping correction
of quadratic amplitude. -/
theorem abs_clip_sub_le_quadratic_scale
    (b M h : ℝ) (_hM : 0 ≤ M) (_hh : 0 ≤ h)
    (hb : |b| ≤ M * h ^ 2) :
    |clip b - b| ≤ M * h ^ 2 :=
  (abs_clip_sub_le_abs b).trans hb

/-- Combining two-sided lattice values and coefficient consistency gives the
quadratic clipping-amplitude bound used on interface elements. -/
theorem abs_clip_sub_le_of_value_and_error
    (b v valueConstant errorConstant h : ℝ)
    (hvalueConstant : 0 ≤ valueConstant)
    (herrorConstant : 0 ≤ errorConstant)
    (hh : 0 ≤ h)
    (herror : |b - v| ≤ errorConstant * h ^ 2)
    (hvalue : |v| ≤ valueConstant * h ^ 2) :
    |clip b - b| ≤ (valueConstant + errorConstant) * h ^ 2 := by
  apply (abs_clip_sub_le_abs b).trans
  exact abs_coefficient_le_quadratic_scale
    b v valueConstant errorConstant h
    hvalueConstant herrorConstant hh herror hvalue

end BernsteinObstacle
