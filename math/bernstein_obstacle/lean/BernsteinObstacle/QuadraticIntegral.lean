import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open scoped Interval

namespace BernsteinObstacle

/-- Closed form for an interval integral of a real quadratic polynomial. -/
theorem intervalIntegral_quadraticPolynomial
    (a b c l r : ℝ) :
    (∫ x in l..r, a * x ^ 2 + b * x + c) =
      a * (r ^ 3 - l ^ 3) / 3 +
        b * (r ^ 2 - l ^ 2) / 2 + c * (r - l) := by
  have hquad : IntervalIntegrable (fun x : ℝ => a * x ^ 2)
      MeasureTheory.volume l r :=
    (by fun_prop : Continuous (fun x : ℝ => a * x ^ 2)).intervalIntegrable l r
  have hlin : IntervalIntegrable (fun x : ℝ => b * x)
      MeasureTheory.volume l r :=
    (by fun_prop : Continuous (fun x : ℝ => b * x)).intervalIntegrable l r
  have hconst : IntervalIntegrable (fun _ : ℝ => c)
      MeasureTheory.volume l r :=
    continuous_const.intervalIntegrable l r
  rw [intervalIntegral.integral_add (hquad.add hlin) hconst]
  rw [intervalIntegral.integral_add hquad hlin]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [integral_pow, integral_id, intervalIntegral.integral_const]
  ring

end BernsteinObstacle
