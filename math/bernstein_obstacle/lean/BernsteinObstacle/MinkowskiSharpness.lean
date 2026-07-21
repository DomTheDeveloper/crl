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
  have hfun :
      (fun x : ℝ => phaseLockedQuadraticSlopeEnergyDensity h theta x) =
        fun x : ℝ =>
          (1 - theta) ^ 4 * (h ^ 2 - 4 * h * x + 4 * x ^ 2) := by
    funext x
    exact phaseLockedQuadraticSlopeEnergyDensity_expand h theta x
  have hIconst :
      IntervalIntegrable (fun _ : ℝ => h ^ 2) volume 0 h :=
    continuous_const.intervalIntegrable
  have hIlin :
      IntervalIntegrable (fun x : ℝ => (4 * h) * x) volume 0 h :=
    (continuous_const.mul continuous_id).intervalIntegrable
  have hIquad :
      IntervalIntegrable (fun x : ℝ => 4 * x ^ 2) volume 0 h :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable
  have hpoly :
      (∫ x in (0 : ℝ)..h, h ^ 2 - 4 * h * x + 4 * x ^ 2) =
        (∫ _ in (0 : ℝ)..h, h ^ 2) -
          (4 * h) * (∫ x in (0 : ℝ)..h, x) +
            4 * (∫ x in (0 : ℝ)..h, x ^ 2) := by
    rw [intervalIntegral.integral_add (hIconst.sub hIlin) hIquad,
      intervalIntegral.integral_sub hIconst hIlin,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hfun, intervalIntegral.integral_const_mul, hpoly]
  rw [intervalIntegral.integral_const, integral_id, integral_pow]
  norm_num
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
  calc
    (1 - theta) ^ 4 * h ^ 3 / 3 =
        ((1 - theta) ^ 4 / (Real.sqrt 3) ^ 2) *
          (h * Real.sqrt h) ^ 2 := by
      rw [hsqrt3, hscale]
      ring
    _ = (((1 - theta) ^ 2 / Real.sqrt 3) *
          (h * Real.sqrt h)) ^ 2 := by ring

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
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hscale : (h * Real.sqrt h) ^ 2 = h ^ 3 :=
    threeHalvesScale_sq h hh
  have htargetSq :
      (delta ^ 2 / Real.sqrt 3 * (h * Real.sqrt h)) ^ 2 =
        delta ^ 4 / 3 * h ^ 3 := by
    calc
      (delta ^ 2 / Real.sqrt 3 * (h * Real.sqrt h)) ^ 2 =
          delta ^ 4 / (Real.sqrt 3) ^ 2 *
            (h * Real.sqrt h) ^ 2 := by ring
      _ = delta ^ 4 / 3 * h ^ 3 := by rw [hsqrt3, hscale]
  have henergy :
      (delta ^ 2 / Real.sqrt 3 * (h * Real.sqrt h)) ^ 2 ≤ e ^ 2 := by
    rw [htargetSq, heq,
      intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity]
    have hh3 : 0 ≤ h ^ 3 := pow_nonneg hh _
    calc
      delta ^ 4 / 3 * h ^ 3 ≤ (1 - theta) ^ 4 / 3 * h ^ 3 := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hpow (by norm_num)) hh3
      _ = (1 - theta) ^ 4 * h ^ 3 / 3 := by ring
  nlinarith

end BernsteinObstacle
