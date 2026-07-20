import BernsteinObstacle.SimplexPartition
import BernsteinObstacle.UniversalRate
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Finite gradient-modulus and contact-recovery bridge

This file formalizes the finite Bernstein part of the universal arbitrary-contact
estimate.  The genuinely analytic input is isolated as a samplewise first-order
remainder bound.  Once that bound is available, positivity and partition of unity
turn it into an exact whole-simplex contact estimate.

It also packages the summation and coercive square-root steps used to pass from
local recovery/contact contributions to the global rate.
-/

/-- A samplewise first-order modulus estimate propagates through the complete
simplicial Bernstein basis.  This is the finite core of the contact estimate
`B_h g(x) <= h_T * omega_T(h_T)`.

The hypotheses `sample α <= distance α * omega` and `distance α <= h` are the
analytical Taylor/segment and mesh-diameter inputs, respectively. -/
theorem simplexFieldNat_contact_mem_Icc_of_modulus
    (d n : ℕ)
    (sample distance : (Fin (d + 1) → ℕ) → ℝ)
    (h omega : ℝ)
    (hh : 0 ≤ h) (homega : 0 ≤ omega)
    (hsample_nonneg :
      ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        0 ≤ sample α)
    (hsample_modulus :
      ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        sample α ≤ distance α * omega)
    (hdistance :
      ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        distance α ≤ h)
    (x : BarycentricPoint d) :
    simplexFieldNat d n sample x ∈ Set.Icc (0 : ℝ) (h * omega) := by
  apply simplexFieldNat_mem_Icc d n sample 0 (h * omega) _ x
  intro α hα
  constructor
  · exact hsample_nonneg α hα
  · calc
      sample α ≤ distance α * omega := hsample_modulus α hα
      _ ≤ h * omega := mul_le_mul_of_nonneg_right (hdistance α hα) homega

/-- The contact estimate in upper-bound form. -/
theorem simplexFieldNat_contact_le_of_modulus
    (d n : ℕ)
    (sample distance : (Fin (d + 1) → ℕ) → ℝ)
    (h omega : ℝ)
    (hh : 0 ≤ h) (homega : 0 ≤ omega)
    (hsample_nonneg :
      ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        0 ≤ sample α)
    (hsample_modulus :
      ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        sample α ≤ distance α * omega)
    (hdistance :
      ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        distance α ≤ h)
    (x : BarycentricPoint d) :
    simplexFieldNat d n sample x ≤ h * omega := by
  exact (simplexFieldNat_contact_mem_Icc_of_modulus
    d n sample distance h omega hh homega hsample_nonneg
    hsample_modulus hdistance x).2

/-- Elementwise squared recovery estimates sum to the global modulus indicator. -/
theorem sum_local_recovery_sq_le_modulus_indicator
    {ι : Type*} [Fintype ι]
    (localError volume omega : ι → ℝ)
    (hlocal : ∀ i, localError i ^ 2 ≤ volume i * omega i ^ 2) :
    (∑ i, localError i ^ 2) ≤ ∑ i, volume i * omega i ^ 2 := by
  exact Finset.sum_le_sum fun i _ => hlocal i

/-- Nonnegative contact weights preserve pointwise recovery upper bounds.  This is
the finite weighted analogue of integrating the Bernstein contact estimate against
a nonnegative multiplier measure. -/
theorem sum_weighted_contact_recovery_le
    {ι : Type*} [Fintype ι]
    (weight recovery scale : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hrecovery : ∀ i, recovery i ≤ scale i) :
    (∑ i, weight i * recovery i) ≤ ∑ i, weight i * scale i := by
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hrecovery i) (hweight i)

/-- A squared modulus indicator plus a nonnegative contact term gives the exact
universal rate shape `sqrt(etaSq) + sqrt(mu)` after coercive transfer. -/
theorem universalRate_of_modulusIndicator_and_contact
    (e α C etaSq mu : ℝ)
    (he : 0 ≤ e) (hα : 0 < α) (hC : 0 ≤ C)
    (heta : 0 ≤ etaSq) (hmu : 0 ≤ mu)
    (henergy : α * e ^ 2 ≤ C * (etaSq + mu)) :
    e ≤ Real.sqrt (C / α) * (Real.sqrt etaSq + Real.sqrt mu) := by
  have hetaSq : (Real.sqrt etaSq) ^ 2 = etaSq := Real.sq_sqrt heta
  have hmuSq : (Real.sqrt mu) ^ 2 = mu := Real.sq_sqrt hmu
  have henergy' :
      α * e ^ 2 ≤
        C * (Real.sqrt etaSq) ^ 2 + C * (Real.sqrt mu) ^ 2 := by
    calc
      α * e ^ 2 ≤ C * (etaSq + mu) := henergy
      _ = C * (Real.sqrt etaSq) ^ 2 + C * (Real.sqrt mu) ^ 2 := by
        rw [hetaSq, hmuSq]
        ring
  have hrate := twoScaleRate_of_energy_components
    e α C C (Real.sqrt etaSq) (Real.sqrt mu)
    he hα hC hC (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) henergy'
  simpa using hrate

/-- The same bridge in the theorem's notation: if `eta` is already the square
root of the assembled recovery indicator, the result is `eta + sqrt(mu)`. -/
theorem universalRate_of_modulus_and_contact
    (e α C eta mu : ℝ)
    (he : 0 ≤ e) (hα : 0 < α) (hC : 0 ≤ C)
    (heta : 0 ≤ eta) (hmu : 0 ≤ mu)
    (henergy : α * e ^ 2 ≤ C * (eta ^ 2 + mu)) :
    e ≤ Real.sqrt (C / α) * (eta + Real.sqrt mu) := by
  have hmuSq : (Real.sqrt mu) ^ 2 = mu := Real.sq_sqrt hmu
  have henergy' :
      α * e ^ 2 ≤ C * eta ^ 2 + C * (Real.sqrt mu) ^ 2 := by
    calc
      α * e ^ 2 ≤ C * (eta ^ 2 + mu) := henergy
      _ = C * eta ^ 2 + C * (Real.sqrt mu) ^ 2 := by
        rw [hmuSq]
        ring
  have hrate := twoScaleRate_of_energy_components
    e α C C eta (Real.sqrt mu)
    he hα hC hC heta (Real.sqrt_nonneg _) henergy'
  simpa using hrate

end

end BernsteinObstacle
