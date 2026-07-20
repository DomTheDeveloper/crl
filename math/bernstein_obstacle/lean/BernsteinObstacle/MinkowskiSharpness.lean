import BernsteinObstacle.MinkowskiSaturation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open scoped Interval

namespace BernsteinObstacle

/-!
# Exact sharpness of the quadratic codimension-one clipping scale

For the phase-locked quadratic cut-cell model, clipping the negative middle
Bernstein coefficient produces

`d_h(x) = (1 - theta)^2 * x * (h - x)`.

The derivative is `(1 - theta)^2 * (h - 2*x)`.  The exact interval integral of
its square is `(1 - theta)^4 * h^3 / 3`.  Thus the `H^1` seminorm is exactly a
nonzero constant times `h * sqrt h` whenever the phase is fixed away from one.
This supplies a matching lower model for the previously verified upper rate.
-/

/-- The exact squared slope profile of the phase-locked clipping correction. -/
def phaseLockedQuadraticSlopeEnergyDensity
    (h theta x : ℝ) : ℝ :=
  ((1 - theta) ^ 2 * (h - 2 * x)) ^ 2

/-- Polynomial expansion of the squared slope profile. -/
theorem phaseLockedQuadraticSlopeEnergyDensity_expand
    (h theta x : ℝ) :
    phaseLockedQuadraticSlopeEnergyDensity h theta x =
      (1 - theta) ^ 4 * (h ^ 2 - 4 * h * x + 4 * x ^ 2) := by
  unfold phaseLockedQuadraticSlopeEnergyDensity
  ring

/-- Exact derivative-energy identity for the clipped phase-locked quadratic
cut-cell model. -/
theorem intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity
    (h theta : ℝ) :
    (∫ x in (0 : ℝ)..h,
      phaseLockedQuadraticSlopeEnergyDensity h theta x) =
        (1 - theta) ^ 4 * h ^ 3 / 3 := by
  simp_rw [phaseLockedQuadraticSlopeEnergyDensity_expand]
  rw [intervalIntegral.integral_const_mul]
  simp [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_pow]
  ring

/-- The exact squared `H^1`-seminorm scale, written in the same form used by the
upper-bound theorem. -/
theorem intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity_eq_scale_sq
    (h theta : ℝ) (hh : 0 ≤ h) :
    (∫ x in (0 : ℝ)..h,
      phaseLockedQuadraticSlopeEnergyDensity h theta x) =
      (((1 - theta) ^ 2 / Real.sqrt 3) * (h * Real.sqrt h)) ^ 2 := by
  rw [intervalIntegral_phaseLockedQuadraticSlopeEnergyDensity]
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hscale : (h * Real.sqrt h) ^ 2 = h ^ 3 :=
    threeHalvesScale_sq h hh
  rw [div_mul_eq_mul_div, mul_pow, div_pow, hsqrt3, hscale]
  ring

/-- A fixed nondegenerate phase gives a positive matching lower bound of order
`h^(3/2)` for the clipping correction seminorm. -/
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
    calc
      delta ^ 4 / 3 * h ^ 3 ≤ (1 - theta) ^ 4 / 3 * h ^ 3 := by
        gcongr
      _ = (1 - theta) ^ 4 * h ^ 3 / 3 := by ring
  nlinarith

end BernsteinObstacle
