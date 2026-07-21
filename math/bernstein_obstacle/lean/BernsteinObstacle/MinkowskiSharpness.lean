import BernsteinObstacle.MinkowskiSaturation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open scoped Interval

namespace BernsteinObstacle

/-!
# Exact sharpness of the quadratic codimension-one clipping scale

For the phase-locked quadratic cut-cell model, clipping the negative middle
Bernstein coefficient produces a correction whose derivative energy is exactly
a nonzero constant times `h^3`, so the `H^1` seminorm has the matching
`h * sqrt h` scale.
-/

def phaseLockedQuadraticSlopeEnergyDensity
    (h theta x : ℝ) : ℝ :=
  ((1 - theta) ^ 2 * (h - 2 * x)) ^ 2

theorem phaseLockedQuadraticSlopeEnergyDensity_expand
    (h theta x : ℝ) :
    phaseLockedQuadraticSlopeEnergyDensity h theta x =
      (1 - theta) ^ 4 * (h ^ 2 - 4 * h * x + 4 * x ^ 2) := by
  unfold phaseLockedQuadraticSlopeEnergyDensity
  ring

theorem intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity
    (h theta : ℝ) :
    (∫ x in (0 : ℝ)..h,
      phaseLockedQuadraticSlopeEnergyDensity h theta x) =
        (1 - theta) ^ 4 * h ^ 3 / 3 := by
  have hdensity :
      (fun x : ℝ => phaseLockedQuadraticSlopeEnergyDensity h theta x) =
        fun x : ℝ => (1 - theta) ^ 4 *
          (h ^ 2 - 4 * h * x + 4 * x ^ 2) := by
    funext x
    exact phaseLockedQuadraticSlopeEnergyDensity_expand h theta x
  rw [hdensity, intervalIntegral.integral_const_mul]
  simp [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_pow]
  ring

theorem intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity_eq_scale_sq
    (h theta : ℝ) (hh : 0 ≤ h) :
    (∫ x in (0 : ℝ)..h,
      phaseLockedQuadraticSlopeEnergyDensity h theta x) =
      (((1 - theta) ^ 2 / Real.sqrt 3) * (h * Real.sqrt h)) ^ 2 := by
  rw [intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity]
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hscale : (h * Real.sqrt h) ^ 2 = h ^ 3 :=
    threeHalvesScale_sq h hh
  rw [mul_pow, div_pow, hsqrt3, hscale]
  ring

theorem phaseLockedQuadraticSlopeEnergy_lowerBound
    (h theta delta e : ℝ)
    (hh : 0 ≤ h) (hdelta : 0 ≤ delta)
    (hphase : delta ≤ 1 - theta)
    (he : 0 ≤ e)
    (heq : e ^ 2 =
      ∫ x in (0 : ℝ)..h,
        phaseLockedQuadraticSlopeEnergyDensity h theta x) :
    delta ^ 2 / Real.sqrt 3 * (h * Real.sqrt h) ≤ e := by
  have hphaseNonneg : 0 ≤ 1 - theta := hdelta.trans hphase
  have hpow : delta ^ 4 ≤ (1 - theta) ^ 4 := by
    exact pow_le_pow_left₀ hdelta hphase 4
  have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hscaleNonneg : 0 ≤ h * Real.sqrt h :=
    mul_nonneg hh (Real.sqrt_nonneg _)
  have htargetNonneg :
      0 ≤ delta ^ 2 / Real.sqrt 3 * (h * Real.sqrt h) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hsqrt3pos)) hscaleNonneg
  have henergy :
      (delta ^ 2 / Real.sqrt 3 * (h * Real.sqrt h)) ^ 2 ≤ e ^ 2 := by
    rw [heq, intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity]
    have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := by norm_num
    have hscale : (h * Real.sqrt h) ^ 2 = h ^ 3 :=
      threeHalvesScale_sq h hh
    rw [mul_pow, div_pow, hsqrt3, hscale]
    have hh3 : 0 ≤ h ^ 3 := pow_nonneg hh _
    have hmul : delta ^ 4 * h ^ 3 ≤ (1 - theta) ^ 4 * h ^ 3 :=
      mul_le_mul_of_nonneg_right hpow hh3
    nlinarith
  nlinarith

end BernsteinObstacle
