import BernsteinObstacle.CoefficientLocalization
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Local-distance localization for the corrected sharp theorem

The corrected free-boundary theorem measures distance to the interface against
the diameter of the same element. These lemmas certify the real-inequality core
of that correction.
-/

/-- Quadratic gap growth and a local distance-to-size condition force a
coefficient to be nonnegative once the growth constant dominates the
coefficient-error constant. -/
theorem coefficient_nonneg_of_quadratic_growth_and_local_distance
    (b v errorConstant growthConstant κ h dist : ℝ)
    (hh : 0 ≤ h)
    (hκ : 1 ≤ κ)
    (herrorConstant : 0 ≤ errorConstant)
    (hgrowthConstant : 0 ≤ growthConstant)
    (hdist : κ * h ≤ dist)
    (hvalue : growthConstant * (dist - h) ^ 2 ≤ v)
    (herror : |b - v| ≤ errorConstant * h ^ 2)
    (hdominates : errorConstant ≤ growthConstant * (κ - 1) ^ 2) :
    0 ≤ b := by
  have hk : 0 ≤ κ - 1 := sub_nonneg.mpr hκ
  have hkh : 0 ≤ (κ - 1) * h := mul_nonneg hk hh
  have hdistMinus : (κ - 1) * h ≤ dist - h := by
    nlinarith
  have hdistMinusNonneg : 0 ≤ dist - h := hkh.trans hdistMinus
  have hproduct :
      0 ≤ ((dist - h) - (κ - 1) * h) *
        ((dist - h) + (κ - 1) * h) :=
    mul_nonneg (sub_nonneg.mpr hdistMinus)
      (add_nonneg hdistMinusNonneg hkh)
  have hsquare : ((κ - 1) * h) ^ 2 ≤ (dist - h) ^ 2 := by
    nlinarith
  have hthreshold :
      errorConstant * h ^ 2 ≤ growthConstant * (dist - h) ^ 2 := by
    calc
      errorConstant * h ^ 2 ≤
          (growthConstant * (κ - 1) ^ 2) * h ^ 2 :=
        mul_le_mul_of_nonneg_right hdominates (sq_nonneg h)
      _ = growthConstant * ((κ - 1) * h) ^ 2 := by ring
      _ ≤ growthConstant * (dist - h) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare hgrowthConstant
  exact coefficient_nonneg_of_abs_sub_le
    b v (errorConstant * h ^ 2) herror (hthreshold.trans hvalue)

/-- A negative coefficient can occur only in the corrected local risky set
`dist(T, Gamma) < kappa h_T`. -/
theorem local_distance_lt_of_coefficient_neg
    (b v errorConstant growthConstant κ h dist : ℝ)
    (hh : 0 ≤ h)
    (hκ : 1 ≤ κ)
    (herrorConstant : 0 ≤ errorConstant)
    (hgrowthConstant : 0 ≤ growthConstant)
    (hvalue : growthConstant * (dist - h) ^ 2 ≤ v)
    (herror : |b - v| ≤ errorConstant * h ^ 2)
    (hdominates : errorConstant ≤ growthConstant * (κ - 1) ^ 2)
    (hb : b < 0) :
    dist < κ * h := by
  by_contra hnot
  have hdist : κ * h ≤ dist := le_of_not_gt hnot
  have hnonneg := coefficient_nonneg_of_quadratic_growth_and_local_distance
    b v errorConstant growthConstant κ h dist
    hh hκ herrorConstant hgrowthConstant hdist hvalue herror hdominates
  linarith

/-- On a local risky element, quadratic upper growth and an `O(h^2)`
coefficient error give a two-sided `O(h^2)` coefficient bound. -/
theorem abs_coefficient_le_quadratic_on_local_strip
    (b v valueConstant errorConstant κ h dist : ℝ)
    (hh : 0 ≤ h)
    (hdistNonneg : 0 ≤ dist)
    (hκ : 0 ≤ κ)
    (hvalueConstant : 0 ≤ valueConstant)
    (herrorConstant : 0 ≤ errorConstant)
    (hdist : dist ≤ κ * h)
    (hvalue : |v| ≤ valueConstant * (dist + h) ^ 2)
    (herror : |b - v| ≤ errorConstant * h ^ 2) :
    |b| ≤ (valueConstant * (κ + 1) ^ 2 + errorConstant) * h ^ 2 := by
  have hleft : 0 ≤ dist + h := add_nonneg hdistNonneg hh
  have hright : 0 ≤ (κ + 1) * h :=
    mul_nonneg (by linarith) hh
  have hsum : dist + h ≤ (κ + 1) * h := by
    nlinarith
  have hproduct :
      0 ≤ ((κ + 1) * h - (dist + h)) *
        ((κ + 1) * h + (dist + h)) :=
    mul_nonneg (sub_nonneg.mpr hsum) (add_nonneg hright hleft)
  have hsquare : (dist + h) ^ 2 ≤ ((κ + 1) * h) ^ 2 := by
    nlinarith
  have hvalueBound :
      |v| ≤ valueConstant * (κ + 1) ^ 2 * h ^ 2 := by
    calc
      |v| ≤ valueConstant * (dist + h) ^ 2 := hvalue
      _ ≤ valueConstant * ((κ + 1) * h) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare hvalueConstant
      _ = valueConstant * (κ + 1) ^ 2 * h ^ 2 := by ring
  calc
    |b| = |(b - v) + v| := by ring_nf
    _ ≤ |b - v| + |v| := abs_add_le _ _
    _ ≤ errorConstant * h ^ 2 +
        valueConstant * (κ + 1) ^ 2 * h ^ 2 :=
      add_le_add herror hvalueBound
    _ = (valueConstant * (κ + 1) ^ 2 + errorConstant) * h ^ 2 := by ring

end BernsteinObstacle
