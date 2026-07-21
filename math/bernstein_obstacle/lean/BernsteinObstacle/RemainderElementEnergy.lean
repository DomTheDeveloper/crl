import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory

namespace BernsteinObstacle

noncomputable section

/-!
# Elementwise energy of a higher-order free-boundary remainder

A pointwise squared-gradient bound of order `h^(2+2κ)` integrated over an
element of measure `O(h^d)` gives the elementwise energy order
`h^(d+2+2κ)` required by `RemainderPatchScaling`.
-/

section RemainderElementEnergy

variable {X : Type*} [MeasurableSpace X]

/-- A nonnegative integrable density bounded almost everywhere by `B` has
integral at most the real mass of the domain times `B`. -/
theorem integral_le_realMass_mul_of_ae_le
    (μ : Measure X) [IsFiniteMeasure μ]
    (density : X → ℝ) (B : ℝ)
    (hdensityNonneg : 0 ≤ᵐ[μ] density)
    (hB : 0 ≤ B)
    (hdensityIntegrable : Integrable density μ)
    (hbound : density ≤ᵐ[μ] (fun _ : X => B)) :
    (∫ x, density x ∂μ) ≤ μ.real Set.univ * B := by
  have hconstIntegrable : Integrable (fun _ : X => B) μ :=
    integrable_const B
  have hmono := integral_mono_of_nonneg
    hdensityNonneg hconstIntegrable hbound
  simpa [smul_eq_mul] using hmono

/-- Pointwise `G² h^(2+2κ)` density and volume `V h^d` imply the local
`V G² h^(d+2+2κ)` energy bound. -/
theorem remainderElement_energy_le_higherOrder
    (μ : Measure X) [IsFiniteMeasure μ]
    (density : X → ℝ)
    (G V h : ℝ) (d κ : ℕ)
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hh : 0 ≤ h)
    (hdensityNonneg : 0 ≤ᵐ[μ] density)
    (hdensityIntegrable : Integrable density μ)
    (hpointwise :
      density ≤ᵐ[μ] (fun _ : X => G ^ 2 * h ^ (2 + 2 * κ)))
    (hvolume : μ.real Set.univ ≤ V * h ^ d) :
    (∫ x, density x ∂μ) ≤
      (V * G ^ 2) * h ^ (d + 2 + 2 * κ) := by
  have hB : 0 ≤ G ^ 2 * h ^ (2 + 2 * κ) := by positivity
  have hintegral := integral_le_realMass_mul_of_ae_le
    μ density (G ^ 2 * h ^ (2 + 2 * κ))
    hdensityNonneg hB hdensityIntegrable hpointwise
  have hvolumeScaled :
      μ.real Set.univ * (G ^ 2 * h ^ (2 + 2 * κ)) ≤
        (V * h ^ d) * (G ^ 2 * h ^ (2 + 2 * κ)) :=
    mul_le_mul_of_nonneg_right hvolume hB
  calc
    (∫ x, density x ∂μ) ≤
        μ.real Set.univ * (G ^ 2 * h ^ (2 + 2 * κ)) := hintegral
    _ ≤ (V * h ^ d) * (G ^ 2 * h ^ (2 + 2 * κ)) := hvolumeScaled
    _ = (V * G ^ 2) * h ^ (d + 2 + 2 * κ) := by
      rw [show d + 2 + 2 * κ = d + (2 + 2 * κ) by omega, pow_add]
      ring

end RemainderElementEnergy

end

end BernsteinObstacle
