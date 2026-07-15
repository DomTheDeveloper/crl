import Mathlib

/-!
# Algebra used by the master defect-moment inequality

These are the exact square identities used when passing from row/column first
moments to diagonal first moments.
-/

namespace Checkerboard

/-- Sum/difference square identity used in the weighted Cauchy step. -/
theorem sumDiffSquares (a b : ℝ) :
    (a + b)^2 + (a - b)^2 = 2 * (a^2 + b^2) := by
  ring

/-- The normalized form appearing in the paper. -/
theorem cauchyNumeratorIdentity (a b q : ℝ) (hq : q + 2 ≠ 0) :
    ((a + b)^2 + (a - b)^2) / (4 * (q + 2)) =
      (a^2 + b^2) / (2 * (q + 2)) := by
  rw [sumDiffSquares]
  field_simp
  ring

end Checkerboard
