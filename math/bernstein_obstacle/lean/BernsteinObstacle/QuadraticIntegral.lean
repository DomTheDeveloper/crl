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
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [integral_pow, integral_id, intervalIntegral.integral_const]
  ring

end BernsteinObstacle
