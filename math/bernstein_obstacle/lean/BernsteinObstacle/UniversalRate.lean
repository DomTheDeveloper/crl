import BernsteinObstacle.SharpRateAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Universal obstacle-rate algebra

The analytical universal theorem produces two nonnegative squared scales:

* a positive Bernstein recovery scale;
* a contact-measure consistency scale.

This file certifies the coercive square-root transfer for arbitrary scales and
its first-order specialization.
-/

/-- Two nonnegative squared energy scales imply a norm estimate by the sum of
the corresponding scales. -/
theorem twoScaleRate_of_energy_components
    (e α A B s t : ℝ)
    (he : 0 ≤ e) (hα : 0 < α)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (henergy : α * e ^ 2 ≤ A * s ^ 2 + B * t ^ 2) :
    e ≤ Real.sqrt (max A B / α) * (s + t) := by
  let M : ℝ := max A B
  have hM : 0 ≤ M := by
    dsimp [M]
    exact hA.trans (le_max_left A B)
  have hweighted :
      A * s ^ 2 + B * t ^ 2 ≤ M * (s ^ 2 + t ^ 2) := by
    calc
      A * s ^ 2 + B * t ^ 2 ≤ M * s ^ 2 + M * t ^ 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left A B) (sq_nonneg s))
          (mul_le_mul_of_nonneg_right (le_max_right A B) (sq_nonneg t))
      _ = M * (s ^ 2 + t ^ 2) := by ring
  have hsquares : s ^ 2 + t ^ 2 ≤ (s + t) ^ 2 :=
    add_sq_le_sq_add s t hs ht
  have hcoercive : α * e ^ 2 ≤ M * (s + t) ^ 2 := by
    calc
      α * e ^ 2 ≤ A * s ^ 2 + B * t ^ 2 := henergy
      _ ≤ M * (s ^ 2 + t ^ 2) := hweighted
      _ ≤ M * (s + t) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquares hM
  have hdiv : e ^ 2 ≤ (M / α) * (s + t) ^ 2 := by
    have htmp : e ^ 2 ≤ (M * (s + t) ^ 2) / α := by
      apply (le_div_iff₀ hα).2
      simpa [mul_comm] using hcoercive
    calc
      e ^ 2 ≤ (M * (s + t) ^ 2) / α := htmp
      _ = (M / α) * (s + t) ^ 2 := by ring
  have hratio : 0 ≤ M / α :=
    div_nonneg hM (le_of_lt hα)
  have hsqrtSq : (Real.sqrt (M / α)) ^ 2 = M / α :=
    Real.sq_sqrt hratio
  have hrhsNonneg : 0 ≤ Real.sqrt (M / α) * (s + t) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hs ht)
  have hsquareBound :
      e ^ 2 ≤ (Real.sqrt (M / α) * (s + t)) ^ 2 := by
    calc
      e ^ 2 ≤ (M / α) * (s + t) ^ 2 := hdiv
      _ = (Real.sqrt (M / α) * (s + t)) ^ 2 := by
        rw [mul_pow, hsqrtSq]
  have hfinal : e ≤ Real.sqrt (M / α) * (s + t) := by
    nlinarith
  simpa [M] using hfinal

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

/-- The universal first-order obstacle endgame: a squared recovery estimate and
a contact-measure consistency estimate, both of order `h^2`, imply an `O(h)`
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
