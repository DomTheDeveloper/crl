import Mathlib

/-!
# Cubic transformation certificate

This file formally checks the algebraic relation between Prellberg's cubic
parameter `p` and the asymptotic constant `α = 2(1-p)`.
-/

namespace Checkerboard

noncomputable section

/-- The cubic polynomial defining the continuum parameter `p`. -/
def pPoly (p : ℝ) : ℝ := 401 * p^3 - 331 * p^2 + 19 * p + 7

/-- The cubic polynomial defining the checkerboard constant `α`. -/
def alphaPoly (a : ℝ) : ℝ := 401 * a^3 - 1744 * a^2 + 2240 * a - 768

/-- Exact polynomial identity behind `α = 2(1-p)`. -/
theorem alphaPoly_transform (p : ℝ) :
    alphaPoly (2 * (1 - p)) = -8 * pPoly p := by
  simp [alphaPoly, pPoly]
  ring

/-- Every root of the `p` cubic gives a root of the `α` cubic. -/
theorem pRoot_gives_alphaRoot {p : ℝ} (hp : pPoly p = 0) :
    alphaPoly (2 * (1 - p)) = 0 := by
  rw [alphaPoly_transform, hp]
  norm_num

/-- The corresponding numerical identity is purely algebraic. -/
theorem alpha_eq_two_sub_two_mul (p : ℝ) :
    2 * (1 - p) = 2 - 2 * p := by ring

end

end Checkerboard
