import BernsteinObstacle.StripScaling
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Per-element scaling of a Bernstein coefficient correction

A finite-dimensional reference-element inverse estimate has the physical form
`energySq ≤ A h^(d-2) ∑ c_i^2`.  If every correction coefficient is `O(h^2)`,
then the element squared energy is `O(h^(d+2))`.  This is the missing algebraic
bridge between coefficient clipping amplitude and the strip theorem.
-/

/-- Uniform coefficient amplitude bounds the finite coefficient square sum. -/
theorem coefficient_square_sum_le_card_mul
    {I : Type*} [Fintype I]
    (c : I → ℝ) (M h : ℝ)
    (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hcoeff : ∀ i, |c i| ≤ M * h ^ 2) :
    (∑ i : I, c i ^ 2) ≤
      (Fintype.card I : ℝ) * (M * h ^ 2) ^ 2 := by
  have hbound : 0 ≤ M * h ^ 2 :=
    mul_nonneg hM (sq_nonneg h)
  apply sum_le_card_mul_of_le Finset.univ (fun i => c i ^ 2)
    ((M * h ^ 2) ^ 2)
  intro i hi
  have hiabs := hcoeff i
  have hibounds : -(M * h ^ 2) ≤ c i ∧ c i ≤ M * h ^ 2 :=
    (abs_le).mp hiabs
  nlinarith

/-- A reference inverse estimate and `O(h^2)` coefficients give the physical
per-element `O(h^(d+2))` squared-energy estimate. -/
theorem element_correction_energy_le
    {I : Type*} [Fintype I]
    (c : I → ℝ) (energySq A M h : ℝ) (d : ℕ)
    (hd : 2 ≤ d) (hA : 0 ≤ A) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hcoeff : ∀ i, |c i| ≤ M * h ^ 2)
    (henergy :
      energySq ≤ A * h ^ (d - 2) * (∑ i : I, c i ^ 2)) :
    energySq ≤
      A * (Fintype.card I : ℝ) * M ^ 2 * h ^ (d + 2) := by
  have hsum := coefficient_square_sum_le_card_mul c M h hM hh hcoeff
  have hfactor : 0 ≤ A * h ^ (d - 2) :=
    mul_nonneg hA (pow_nonneg hh _)
  have hpow : h ^ (d - 2) * h ^ 4 = h ^ (d + 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    energySq ≤ A * h ^ (d - 2) * (∑ i : I, c i ^ 2) := henergy
    _ ≤ A * h ^ (d - 2) *
        ((Fintype.card I : ℝ) * (M * h ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = A * (Fintype.card I : ℝ) * M ^ 2 *
        (h ^ (d - 2) * h ^ 4) := by ring
    _ = A * (Fintype.card I : ℝ) * M ^ 2 * h ^ (d + 2) := by
      rw [hpow]

/-- A family of corrected elements therefore satisfies the exact per-element
hypothesis required by `strip_sum_energy_le_cubic`. -/
theorem element_correction_energy_bound_for_strip
    {Element I : Type*} [Fintype I]
    (correction : Element → I → ℝ)
    (energySq : Element → ℝ)
    (A M h : ℝ) (d : ℕ)
    (hd : 2 ≤ d) (hA : 0 ≤ A) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hcoeff : ∀ T i, |correction T i| ≤ M * h ^ 2)
    (henergy : ∀ T,
      energySq T ≤ A * h ^ (d - 2) *
        (∑ i : I, correction T i ^ 2)) :
    ∀ T, energySq T ≤
      (A * (Fintype.card I : ℝ) * M ^ 2) * h ^ (d + 2) := by
  intro T
  simpa [mul_assoc] using element_correction_energy_le
    (correction T) (energySq T) A M h d
    hd hA hM hh (hcoeff T) (henergy T)

end BernsteinObstacle
