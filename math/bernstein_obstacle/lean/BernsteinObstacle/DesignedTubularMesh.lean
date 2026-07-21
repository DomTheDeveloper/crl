import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Designed tubular meshes

Elementary quantitative geometry for a mesh designed around a regular free-boundary
arc.  The tangent model has an `O(h)` safety margin, whereas curvature displaces the
arc from its tangent by only `O(h²)`.  These lemmas turn that observation into uniform
Jacobian and phase-separation constants.
-/

/-- The tubular-coordinate Jacobian `1 - t κ` stays between `1/2` and `3/2`
when `|t| ≤ r`, `|κ| ≤ K`, and `K r ≤ 1/2`. -/
theorem tubularJacobian_bounds
    (K r k t : ℝ)
    (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hk : |k| ≤ K) (ht : |t| ≤ r)
    (hKr : K * r ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ 1 - t * k ∧ 1 - t * k ≤ 3 / 2 := by
  have habs : |t * k| ≤ r * K := by
    rw [abs_mul]
    exact mul_le_mul ht hk (abs_nonneg _) hr
  have hrK : r * K ≤ 1 / 2 := by
    simpa [mul_comm] using hKr
  have hupper : t * k ≤ 1 / 2 := by
    calc
      t * k ≤ |t * k| := le_abs_self _
      _ ≤ r * K := habs
      _ ≤ 1 / 2 := hrK
  have hlower : -(1 / 2 : ℝ) ≤ t * k := by
    have hneg : -|t * k| ≤ t * k := neg_abs_le _
    linarith
  constructor <;> linarith

/-- A centered fiber remains uniformly phase separated if the actual crossing is
within one quarter of the fiber half-width from its tangent-model center. -/
theorem centeredFiber_phase_bounds
    (c h delta : ℝ)
    (hc : 0 < c) (hh : 0 < h)
    (hdelta : |delta| ≤ c * h / 2) :
    (1 / 4 : ℝ) ≤ (delta + c * h) / (2 * c * h) ∧
      (delta + c * h) / (2 * c * h) ≤ 3 / 4 := by
  have hden : 0 < 2 * c * h := by positivity
  rcases abs_le.mp hdelta with ⟨hdeltaLower, hdeltaUpper⟩
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith
  · apply (div_le_iff₀ hden).2
    nlinarith

/-- A quadratic curvature displacement fits inside the phase margin once
`K c h ≤ 1`. -/
theorem quadraticDisplacement_within_centeredMargin
    (K c h delta : ℝ)
    (hK : 0 ≤ K) (hc : 0 < c) (hh : 0 < h)
    (hsmall : K * c * h ≤ 1)
    (hdelta : |delta| ≤ K * (c * h) ^ 2 / 2) :
    |delta| ≤ c * h / 2 := by
  have hch : 0 ≤ c * h := by positivity
  have hscaled : K * (c * h) ≤ 1 := by
    simpa [mul_assoc] using hsmall
  have hbound : K * (c * h) ^ 2 / 2 ≤ c * h / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hscaled hch
    nlinarith
  exact hdelta.trans hbound

/-- Curvature-scale displacement preserves the uniform phase interval
`[1/4,3/4]`. -/
theorem curvedFiber_phase_bounds
    (K c h delta : ℝ)
    (hK : 0 ≤ K) (hc : 0 < c) (hh : 0 < h)
    (hsmall : K * c * h ≤ 1)
    (hdelta : |delta| ≤ K * (c * h) ^ 2 / 2) :
    (1 / 4 : ℝ) ≤ (delta + c * h) / (2 * c * h) ∧
      (delta + c * h) / (2 * c * h) ≤ 3 / 4 := by
  apply centeredFiber_phase_bounds c h delta hc hh
  exact quadraticDisplacement_within_centeredMargin
    K c h delta hK hc hh hsmall hdelta

/-- The same smallness condition gives a positive tubular Jacobian on every
normal fiber of half-width `c h`. -/
theorem curvedFiber_jacobian_bounds
    (K c h k t : ℝ)
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hk : |k| ≤ K) (ht : |t| ≤ c * h)
    (hsmall : K * c * h ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ 1 - t * k ∧ 1 - t * k ≤ 3 / 2 := by
  apply tubularJacobian_bounds K (c * h) k t hK (mul_nonneg hc hh) hk ht
  simpa [mul_assoc] using hsmall

/-- Abstract local remainder estimate: if the gradient error is bounded by
`C h^(1+κ)` and the element area is at most `V h²`, then its squared energy is
bounded by `C² V h^(4+2κ)`. -/
theorem curvedElement_remainderEnergy_bound
    (energy C V h : ℝ) (kappa : ℕ)
    (henergy : energy ≤ (C * h ^ (1 + kappa)) ^ 2 * (V * h ^ 2)) :
    energy ≤ C ^ 2 * V * h ^ (4 + 2 * kappa) := by
  calc
    energy ≤ (C * h ^ (1 + kappa)) ^ 2 * (V * h ^ 2) := henergy
    _ = C ^ 2 * V * h ^ (4 + 2 * kappa) := by
      rw [mul_pow, ← pow_add]
      congr 1
      omega

end BernsteinObstacle
