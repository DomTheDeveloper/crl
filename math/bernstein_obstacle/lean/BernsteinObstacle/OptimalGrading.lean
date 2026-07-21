import BernsteinObstacle.CorrectedSharpRate
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Optimal interface grading consequence

The sharp rate is `h^r + g^(3/2)`. Balancing the interface contribution below
the bulk contribution restores the full degree-`r` rate. Analytically this is
the grading law `g ≲ h^(2r/3)`.
-/

/-- If the interface contribution is no larger than the bulk contribution,
the corrected sharp estimate reduces to the full bulk rate. -/
theorem optimalBulkRate_of_balanced_interface
    (e C h g : ℝ) (r : ℕ)
    (hC : 0 ≤ C)
    (hrate : e ≤ C * (h ^ r + g * Real.sqrt g))
    (hbalance : g * Real.sqrt g ≤ h ^ r) :
    e ≤ 2 * C * h ^ r := by
  have hsum : h ^ r + g * Real.sqrt g ≤ h ^ r + h ^ r :=
    add_le_add (le_refl _) hbalance
  calc
    e ≤ C * (h ^ r + g * Real.sqrt g) := hrate
    _ ≤ C * (h ^ r + h ^ r) := mul_le_mul_of_nonneg_left hsum hC
    _ = 2 * C * h ^ r := by ring

/-- Equality of the interface and bulk scales is a sufficient special case of
optimal grading. -/
theorem optimalBulkRate_of_exact_balance
    (e C h g : ℝ) (r : ℕ)
    (hC : 0 ≤ C)
    (hrate : e ≤ C * (h ^ r + g * Real.sqrt g))
    (hbalance : g * Real.sqrt g = h ^ r) :
    e ≤ 2 * C * h ^ r :=
  optimalBulkRate_of_balanced_interface e C h g r hC hrate hbalance.le

end BernsteinObstacle
