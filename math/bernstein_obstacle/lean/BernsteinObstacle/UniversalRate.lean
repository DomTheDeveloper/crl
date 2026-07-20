import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Universal first-order obstacle-rate algebra

The analytical universal theorem produces two squared contributions of order
`h^2`: the positive Bernstein recovery error and the contact-measure
consistency term.  This file certifies the final coercive square-root transfer.
-/

/-- A coercive squared-energy estimate of order `h^2` implies a first-order
norm estimate. -/
theorem universalFirstOrderRate_of_energy
    (e α A B h : ℝ)
    (he : 0 ≤ e) (hα : 0 < α)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (henergy : α * e ^ 2 ≤ (A + B) * h ^ 2) :
    e ≤ Real.sqrt ((A + B) / α) * h := by
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have hratio : 0 ≤ (A + B) / α :=
    div_nonneg hAB (le_of_lt hα)
  have hdiv : e ^ 2 ≤ ((A + B) / α) * h ^ 2 := by
    have htmp : e ^ 2 ≤ ((A + B) * h ^ 2) / α := by
      apply (le_div_iff₀ hα).2
      simpa [mul_comm] using henergy
    calc
      e ^ 2 ≤ ((A + B) * h ^ 2) / α := htmp
      _ = ((A + B) / α) * h ^ 2 := by ring
  have hsqrtSq : (Real.sqrt ((A + B) / α)) ^ 2 = (A + B) / α :=
    Real.sq_sqrt hratio
  have hrhsNonneg : 0 ≤ Real.sqrt ((A + B) / α) * h :=
    mul_nonneg (Real.sqrt_nonneg _) hh
  have hsquareBound :
      e ^ 2 ≤ (Real.sqrt ((A + B) / α) * h) ^ 2 := by
    calc
      e ^ 2 ≤ ((A + B) / α) * h ^ 2 := hdiv
      _ = (Real.sqrt ((A + B) / α) * h) ^ 2 := by
        rw [mul_pow, hsqrtSq]
  nlinarith

/-- The universal obstacle endgame: a squared recovery estimate and a
contact-measure consistency estimate, both of order `h^2`, imply an `O(h)`
minimizer estimate. -/
theorem universalFirstOrderRate_of_recovery_and_measure
    (e recoverySq contact α A B h : ℝ)
    (he : 0 ≤ e) (hα : 0 < α)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (htransfer : α * e ^ 2 ≤ recoverySq + contact)
    (hrecovery : recoverySq ≤ A * h ^ 2)
    (hcontact : contact ≤ B * h ^ 2) :
    e ≤ Real.sqrt ((A + B) / α) * h := by
  have henergy : α * e ^ 2 ≤ (A + B) * h ^ 2 := by
    calc
      α * e ^ 2 ≤ recoverySq + contact := htransfer
      _ ≤ A * h ^ 2 + B * h ^ 2 := add_le_add hrecovery hcontact
      _ = (A + B) * h ^ 2 := by ring
  exact universalFirstOrderRate_of_energy
    e α A B h he hα hA hB hh henergy

end BernsteinObstacle
