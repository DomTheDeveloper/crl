import BernsteinObstacle.CoefficientLocalization
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Positive physical-boundary elements

Boundary-face Bernstein coefficients are handled by exact trace vanishing. For
an off-face lattice point, the remaining analytical input is a uniform inward
linear lower bound. These lemmas certify that the resulting `O(h)` value
strictly dominates an `O(h^2)` coefficient discrepancy once the local element
size is sufficiently small.
-/

/-- Linear inward growth dominates a quadratic coefficient error when
`errorConstant * h <= boundaryGrowth`. -/
theorem quadratic_error_le_linear_growth
    (errorConstant boundaryGrowth h : ℝ)
    (hh : 0 ≤ h)
    (hsmall : errorConstant * h ≤ boundaryGrowth) :
    errorConstant * h ^ 2 ≤ boundaryGrowth * h := by
  calc
    errorConstant * h ^ 2 = (errorConstant * h) * h := by ring
    _ ≤ boundaryGrowth * h := mul_le_mul_of_nonneg_right hsmall hh

/-- On an off-face boundary lattice point, a uniform inward linear lower bound
and sufficiently small local diameter force the corresponding coefficient to
be nonnegative. -/
theorem boundary_offFace_coefficient_nonneg
    (b v errorConstant boundaryGrowth h : ℝ)
    (hh : 0 ≤ h)
    (hsmall : errorConstant * h ≤ boundaryGrowth)
    (hvalue : boundaryGrowth * h ≤ v)
    (herror : |b - v| ≤ errorConstant * h ^ 2) :
    0 ≤ b := by
  have hthreshold : errorConstant * h ^ 2 ≤ v :=
    (quadratic_error_le_linear_growth errorConstant boundaryGrowth h hh hsmall).trans hvalue
  exact coefficient_nonneg_of_abs_sub_le b v (errorConstant * h ^ 2)
    herror hthreshold

/-- Contrapositive form: under the inward linear-growth hypothesis, a negative
off-face coefficient certifies failure of the required small-element condition. -/
theorem boundary_errorConstant_mul_h_gt_of_coefficient_neg
    (b v errorConstant boundaryGrowth h : ℝ)
    (hh : 0 ≤ h)
    (hvalue : boundaryGrowth * h ≤ v)
    (herror : |b - v| ≤ errorConstant * h ^ 2)
    (hb : b < 0) :
    boundaryGrowth < errorConstant * h := by
  by_contra hnot
  have hsmall : errorConstant * h ≤ boundaryGrowth := le_of_not_gt hnot
  have hnonneg := boundary_offFace_coefficient_nonneg
    b v errorConstant boundaryGrowth h hh hsmall hvalue herror
  linarith

end BernsteinObstacle
