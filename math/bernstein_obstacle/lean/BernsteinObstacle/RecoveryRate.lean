import BernsteinObstacle.SharpRateAlgebra
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Recovery and minimizer sharp-rate composition

This file certifies the last two analytical compositions used in the scoped
free-boundary theorem:

1. bulk interpolation plus a localized clipping correction gives a feasible
   recovery with rate `h^r + hΓ^(3/2)`;
2. the Falk/energy transfer inequality plus multiplier consistency gives the
   same rate for the discrete minimizer.
-/

section RecoveryRate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bulk interpolation estimate and a localized repair estimate combine by
the norm triangle inequality. -/
theorem feasibleRecoveryRate_of_interpolation_and_repair
    (u interpolant repaired : E)
    (A B D h g : ℝ) (r : ℕ)
    (hinterpolation :
      ‖u - interpolant‖ ≤ A * h ^ r + B * (g * Real.sqrt g))
    (hrepair :
      ‖interpolant - repaired‖ ≤ D * (g * Real.sqrt g)) :
    ‖u - repaired‖ ≤
      A * h ^ r + (B + D) * (g * Real.sqrt g) := by
  have htriangle :
      ‖u - repaired‖ ≤ ‖u - interpolant‖ + ‖interpolant - repaired‖ := by
    calc
      ‖u - repaired‖ = ‖(u - interpolant) + (interpolant - repaired)‖ := by
        congr 1
        abel
      _ ≤ ‖u - interpolant‖ + ‖interpolant - repaired‖ := norm_add_le _ _
  calc
    ‖u - repaired‖ ≤ ‖u - interpolant‖ + ‖interpolant - repaired‖ := htriangle
    _ ≤ (A * h ^ r + B * (g * Real.sqrt g)) +
        D * (g * Real.sqrt g) := add_le_add hinterpolation hrepair
    _ = A * h ^ r + (B + D) * (g * Real.sqrt g) := by ring

end RecoveryRate

/-- The exact C8 transfer: a coercive minimizer inequality, a squared recovery
estimate, and an `O(hΓ^3)` multiplier term imply the sharp minimizer rate. -/
theorem sharpMinimizerRate_of_recovery_and_multiplier
    (e recoverySq multiplier α A B D h g : ℝ) (r : ℕ)
    (he : 0 ≤ e) (hα : 0 < α)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (htransfer : α * e ^ 2 ≤ recoverySq + multiplier)
    (hrecovery : recoverySq ≤ A * h ^ (2 * r) + B * g ^ 3)
    (hmultiplier : multiplier ≤ D * g ^ 3) :
    e ≤ Real.sqrt (max A (B + D) / α) *
      (h ^ r + g * Real.sqrt g) := by
  have hBD : 0 ≤ B + D := add_nonneg hB hD
  have henergy :
      α * e ^ 2 ≤ A * h ^ (2 * r) + (B + D) * g ^ 3 := by
    calc
      α * e ^ 2 ≤ recoverySq + multiplier := htransfer
      _ ≤ (A * h ^ (2 * r) + B * g ^ 3) + D * g ^ 3 :=
        add_le_add hrecovery hmultiplier
      _ = A * h ^ (2 * r) + (B + D) * g ^ 3 := by ring
  exact sharpRate_of_energy_components
    e α A (B + D) h g r he hα hA hBD hh hg henergy

end BernsteinObstacle
