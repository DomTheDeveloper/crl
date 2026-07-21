import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open scoped Interval

namespace BernsteinObstacle

/-- Closed form for an interval integral of a real quadratic polynomial.  Keeping
this as a separate lemma makes the sharpness proofs insensitive to the precise
normal form produced by `ring_nf`. -/
theorem intervalIntegral_quadraticPolynomial
    (a b c l r : ℝ) :
    (∫ x in l..r, a * x ^ 2 + b * x + c) =
      a * (r ^ 3 - l ^ 3) / 3 +
        b * (r ^ 2 - l ^ 2) / 2 + c * (r - l) := by
  simp [intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, integral_pow] <;> ring

end BernsteinObstacle
