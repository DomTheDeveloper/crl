import BernsteinObstacle.MinkowskiSaturation
import BernsteinObstacle.QuadraticIntegral
import Mathlib.Tactic

open scoped Interval

namespace BernsteinObstacle

/-!
# Exact quadratic-hinge projection lower bound

This file proves the sharp one-dimensional kernel needed for the full-space
saturation theorem. The target derivative is the broken affine function

`0` on `[0, theta]`, and `2 * (x - theta)` on `[theta, 1]`.

Every quadratic polynomial has an affine derivative `alpha * x + beta`. The
squared derivative error admits an exact completed-square decomposition. A
scaled version on `[0, h]` then gives the sharp `h^3` energy law and the
corresponding `h * sqrt h` seminorm lower bound, uniformly when the cut phase
stays away from the endpoints.
-/

/-- Optimal slope of the affine `L²` projection of the normalized quadratic
hinge derivative. -/
def quadraticHingeOptimalSlope (theta : ℝ) : ℝ :=
  2 * (1 - theta) ^ 2 * (2 * theta + 1)

/-- Optimal intercept of the affine `L²` projection of the normalized
quadratic hinge derivative. -/
def quadraticHingeOptimalIntercept (theta : ℝ) : ℝ :=
  -2 * theta * (1 - theta) ^ 2

/-- Squared derivative error between the normalized quadratic hinge and an
arbitrary quadratic polynomial with derivative `alpha * x + beta`. -/
noncomputable def quadraticHingeAffineDerivativeErrorSq
    (theta alpha beta : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..theta, (alpha * x + beta) ^ 2) +
    ∫ x in theta..1, (2 * (x - theta) - (alpha * x + beta)) ^ 2

theorem quadraticHinge_leftError_expand
    (alpha beta x : ℝ) :
    (alpha * x + beta) ^ 2 =
      alpha ^ 2 * x ^ 2 + 2 * alpha * beta * x + beta ^ 2 := by
  ring

theorem quadraticHinge_rightError_expand
    (theta alpha beta x : ℝ) :
    (2 * (x - theta) - (alpha * x + beta)) ^ 2 =
      (2 - alpha) ^ 2 * x ^ 2 -
        2 * (2 - alpha) * (2 * theta + beta) * x +
          (2 * theta + beta) ^ 2 := by
  ring

/-- Exact completed-square identity for the derivative error against every
quadratic approximant. -/
theorem quadraticHingeAffineDerivativeErrorSq_identity
    (theta alpha beta : ℝ) :
    quadraticHingeAffineDerivativeErrorSq theta alpha beta =
      ((4 : ℝ) / 3) * theta ^ 3 * (1 - theta) ^ 3 +
        ((beta - quadraticHingeOptimalIntercept theta) +
          (alpha - quadraticHingeOptimalSlope theta) / 2) ^ 2 +
        (alpha - quadraticHingeOptimalSlope theta) ^ 2 / 12 := by
  have hleft :
      (∫ x in (0 : ℝ)..theta, (alpha * x + beta) ^ 2) =
        alpha ^ 2 * (theta ^ 3 - 0 ^ 3) / 3 +
          (2 * alpha * beta) * (theta ^ 2 - 0 ^ 2) / 2 +
          beta ^ 2 * (theta - 0) := by
    convert intervalIntegral_quadraticPolynomial
      (alpha ^ 2) (2 * alpha * beta) (beta ^ 2) 0 theta using 1 <;> ring
  have hright :
      (∫ x in theta..1, (2 * (x - theta) - (alpha * x + beta)) ^ 2) =
        (2 - alpha) ^ 2 * (1 ^ 3 - theta ^ 3) / 3 +
          (-2 * (2 - alpha) * (2 * theta + beta)) *
            (1 ^ 2 - theta ^ 2) / 2 +
          (2 * theta + beta) ^ 2 * (1 - theta) := by
    convert intervalIntegral_quadraticPolynomial
      ((2 - alpha) ^ 2)
      (-2 * (2 - alpha) * (2 * theta + beta))
      ((2 * theta + beta) ^ 2) theta 1 using 1 <;> ring
  unfold quadraticHingeAffineDerivativeErrorSq
  rw [hleft, hright]
  simp [quadraticHingeOptimalSlope, quadraticHingeOptimalIntercept]
  ring

/-- The explicit affine derivative attains the sharp normalized error. -/
theorem quadraticHingeAffineDerivativeErrorSq_at_optimal
    (theta : ℝ) :
    quadraticHingeAffineDerivativeErrorSq theta
        (quadraticHingeOptimalSlope theta)
        (quadraticHingeOptimalIntercept theta) =
      ((4 : ℝ) / 3) * theta ^ 3 * (1 - theta) ^ 3 := by
  rw [quadraticHingeAffineDerivativeErrorSq_identity]
  ring

/-- Every quadratic approximant has at least the sharp normalized squared
`H¹`-seminorm error. -/
theorem quadraticHingeAffineDerivativeErrorSq_lowerBound
    (theta alpha beta : ℝ) :
    ((4 : ℝ) / 3) * theta ^ 3 * (1 - theta) ^ 3 ≤
      quadraticHingeAffineDerivativeErrorSq theta alpha beta := by
  rw [quadraticHingeAffineDerivativeErrorSq_identity]
  nlinarith [sq_nonneg
      ((beta - quadraticHingeOptimalIntercept theta) +
        (alpha - quadraticHingeOptimalSlope theta) / 2),
    sq_nonneg (alpha - quadraticHingeOptimalSlope theta)]

/-- A phase interval `[eta, 1 - eta]` gives a uniform normalized lower bound. -/
theorem quadraticHingeAffineDerivativeErrorSq_uniformLowerBound
    (theta eta alpha beta : ℝ)
    (heta : 0 ≤ eta)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta) :
    ((4 : ℝ) / 3) * eta ^ 6 ≤
      quadraticHingeAffineDerivativeErrorSq theta alpha beta := by
  have hthetaNonneg : 0 ≤ theta := heta.trans hleft
  have hright' : eta ≤ 1 - theta := by
    linarith
  have hthetaPow : eta ^ 3 ≤ theta ^ 3 :=
    pow_le_pow_left₀ heta hleft 3
  have hrightPow : eta ^ 3 ≤ (1 - theta) ^ 3 :=
    pow_le_pow_left₀ heta hright' 3
  have hproduct : eta ^ 3 * eta ^ 3 ≤ theta ^ 3 * (1 - theta) ^ 3 :=
    mul_le_mul hthetaPow hrightPow (pow_nonneg heta 3)
      (pow_nonneg hthetaNonneg 3)
  have hscaled := mul_le_mul_of_nonneg_left hproduct
    (by norm_num : 0 ≤ (4 : ℝ) / 3)
  calc
    ((4 : ℝ) / 3) * eta ^ 6 =
        ((4 : ℝ) / 3) * (eta ^ 3 * eta ^ 3) := by ring
    _ ≤ ((4 : ℝ) / 3) * (theta ^ 3 * (1 - theta) ^ 3) := hscaled
    _ = ((4 : ℝ) / 3) * theta ^ 3 * (1 - theta) ^ 3 := by ring
    _ ≤ quadraticHingeAffineDerivativeErrorSq theta alpha beta :=
      quadraticHingeAffineDerivativeErrorSq_lowerBound theta alpha beta

/-- Optimal slope after amplitude scaling on an interval of length `h`. -/
def scaledQuadraticHingeOptimalSlope (amplitude theta : ℝ) : ℝ :=
  amplitude * quadraticHingeOptimalSlope theta

/-- Optimal intercept after amplitude and interval scaling. -/
def scaledQuadraticHingeOptimalIntercept
    (amplitude h theta : ℝ) : ℝ :=
  amplitude * h * quadraticHingeOptimalIntercept theta

/-- Squared derivative error for
`amplitude * (x - theta * h)₊²` on `[0, h]` against an arbitrary quadratic
polynomial with derivative `alpha * x + beta`. -/
noncomputable def scaledQuadraticHingeAffineDerivativeErrorSq
    (amplitude h theta alpha beta : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..theta * h, (alpha * x + beta) ^ 2) +
    ∫ x in theta * h..h,
      (2 * amplitude * (x - theta * h) - (alpha * x + beta)) ^ 2

theorem scaledQuadraticHinge_rightError_expand
    (amplitude h theta alpha beta x : ℝ) :
    (2 * amplitude * (x - theta * h) - (alpha * x + beta)) ^ 2 =
      (2 * amplitude - alpha) ^ 2 * x ^ 2 -
        2 * (2 * amplitude - alpha) *
          (2 * amplitude * theta * h + beta) * x +
          (2 * amplitude * theta * h + beta) ^ 2 := by
  ring

/-- Exact scaled completed-square identity. Its first term is the sharp best
quadratic squared `H¹`-seminorm error. -/
theorem scaledQuadraticHingeAffineDerivativeErrorSq_identity
    (amplitude h theta alpha beta : ℝ) :
    scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta alpha beta =
      ((4 : ℝ) / 3) * amplitude ^ 2 * theta ^ 3 *
          (1 - theta) ^ 3 * h ^ 3 +
        h *
          ((beta - scaledQuadraticHingeOptimalIntercept amplitude h theta) +
            h * (alpha - scaledQuadraticHingeOptimalSlope amplitude theta) / 2) ^ 2 +
        h ^ 3 *
          (alpha - scaledQuadraticHingeOptimalSlope amplitude theta) ^ 2 / 12 := by
  have hleft :
      (∫ x in (0 : ℝ)..theta * h, (alpha * x + beta) ^ 2) =
        alpha ^ 2 * ((theta * h) ^ 3 - 0 ^ 3) / 3 +
          (2 * alpha * beta) * ((theta * h) ^ 2 - 0 ^ 2) / 2 +
          beta ^ 2 * (theta * h - 0) := by
    convert intervalIntegral_quadraticPolynomial
      (alpha ^ 2) (2 * alpha * beta) (beta ^ 2) 0 (theta * h) using 1 <;> ring
  have hright :
      (∫ x in theta * h..h,
        (2 * amplitude * (x - theta * h) - (alpha * x + beta)) ^ 2) =
        (2 * amplitude - alpha) ^ 2 * (h ^ 3 - (theta * h) ^ 3) / 3 +
          (-2 * (2 * amplitude - alpha) *
            (2 * amplitude * theta * h + beta)) *
              (h ^ 2 - (theta * h) ^ 2) / 2 +
          (2 * amplitude * theta * h + beta) ^ 2 *
            (h - theta * h) := by
    convert intervalIntegral_quadraticPolynomial
      ((2 * amplitude - alpha) ^ 2)
      (-2 * (2 * amplitude - alpha) *
        (2 * amplitude * theta * h + beta))
      ((2 * amplitude * theta * h + beta) ^ 2)
      (theta * h) h using 1 <;> ring
  unfold scaledQuadraticHingeAffineDerivativeErrorSq
  rw [hleft, hright]
  simp [scaledQuadraticHingeOptimalSlope,
    scaledQuadraticHingeOptimalIntercept,
    quadraticHingeOptimalSlope, quadraticHingeOptimalIntercept]
  ring

/-- The scaled explicit affine derivative attains the sharp energy. -/
theorem scaledQuadraticHingeAffineDerivativeErrorSq_at_optimal
    (amplitude h theta : ℝ) :
    scaledQuadraticHingeAffineDerivativeErrorSq amplitude h theta
        (scaledQuadraticHingeOptimalSlope amplitude theta)
        (scaledQuadraticHingeOptimalIntercept amplitude h theta) =
      ((4 : ℝ) / 3) * amplitude ^ 2 * theta ^ 3 *
        (1 - theta) ^ 3 * h ^ 3 := by
  rw [scaledQuadraticHingeAffineDerivativeErrorSq_identity]
  ring

/-- For nonnegative interval length, every quadratic approximant satisfies the
sharp scaled energy lower bound. -/
theorem scaledQuadraticHingeAffineDerivativeErrorSq_lowerBound
    (amplitude h theta alpha beta : ℝ)
    (hh : 0 ≤ h) :
    ((4 : ℝ) / 3) * amplitude ^ 2 * theta ^ 3 *
        (1 - theta) ^ 3 * h ^ 3 ≤
      scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta alpha beta := by
  rw [scaledQuadraticHingeAffineDerivativeErrorSq_identity]
  have hfirst :
      0 ≤ h *
        ((beta - scaledQuadraticHingeOptimalIntercept amplitude h theta) +
          h * (alpha - scaledQuadraticHingeOptimalSlope amplitude theta) / 2) ^ 2 :=
    mul_nonneg hh (sq_nonneg _)
  have hsecond :
      0 ≤ h ^ 3 *
        (alpha - scaledQuadraticHingeOptimalSlope amplitude theta) ^ 2 / 12 := by
    positivity
  linarith

/-- Uniform phase separation gives an explicit `h^3` lower bound for every
quadratic approximant. -/
theorem scaledQuadraticHingeAffineDerivativeErrorSq_uniformLowerBound
    (amplitude h theta eta alpha beta : ℝ)
    (hh : 0 ≤ h)
    (heta : 0 ≤ eta)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta) :
    ((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3 ≤
      scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta alpha beta := by
  have hthetaNonneg : 0 ≤ theta := heta.trans hleft
  have hright' : eta ≤ 1 - theta := by
    linarith
  have hthetaPow : eta ^ 3 ≤ theta ^ 3 :=
    pow_le_pow_left₀ heta hleft 3
  have hrightPow : eta ^ 3 ≤ (1 - theta) ^ 3 :=
    pow_le_pow_left₀ heta hright' 3
  have hproduct : eta ^ 3 * eta ^ 3 ≤ theta ^ 3 * (1 - theta) ^ 3 :=
    mul_le_mul hthetaPow hrightPow (pow_nonneg heta 3)
      (pow_nonneg hthetaNonneg 3)
  have hfactor :
      0 ≤ ((4 : ℝ) / 3) * amplitude ^ 2 * h ^ 3 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hproduct hfactor
  calc
    ((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3 =
        (((4 : ℝ) / 3) * amplitude ^ 2 * h ^ 3) *
          (eta ^ 3 * eta ^ 3) := by ring
    _ ≤ (((4 : ℝ) / 3) * amplitude ^ 2 * h ^ 3) *
          (theta ^ 3 * (1 - theta) ^ 3) := hscaled
    _ = ((4 : ℝ) / 3) * amplitude ^ 2 * theta ^ 3 *
          (1 - theta) ^ 3 * h ^ 3 := by ring
    _ ≤ scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta alpha beta :=
      scaledQuadraticHingeAffineDerivativeErrorSq_lowerBound
        amplitude h theta alpha beta hh

/-- Square-root form of the uniform sharp lower bound. This is the exact
one-dimensional `h^(3/2)` obstruction for the full quadratic polynomial space,
not merely for a particular clipping operator. -/
theorem scaledQuadraticHinge_fullSpace_threeHalvesLowerBound
    (amplitude h theta eta alpha beta error : ℝ)
    (hamplitude : 0 ≤ amplitude)
    (hh : 0 ≤ h)
    (heta : 0 ≤ eta)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta)
    (herror : 0 ≤ error)
    (herrorSq : error ^ 2 =
      scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta alpha beta) :
    (2 * amplitude * eta ^ 3 / Real.sqrt 3) *
        (h * Real.sqrt h) ≤ error := by
  have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have htargetNonneg :
      0 ≤ (2 * amplitude * eta ^ 3 / Real.sqrt 3) *
        (h * Real.sqrt h) := by
    positivity
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := by
    norm_num
  have hscale : (h * Real.sqrt h) ^ 2 = h ^ 3 :=
    threeHalvesScale_sq h hh
  have htargetSq :
      ((2 * amplitude * eta ^ 3 / Real.sqrt 3) *
        (h * Real.sqrt h)) ^ 2 =
        ((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3 := by
    rw [mul_pow, div_pow, hsqrt3, hscale]
    ring
  have henergy :=
    scaledQuadraticHingeAffineDerivativeErrorSq_uniformLowerBound
      amplitude h theta eta alpha beta hh heta hleft hright
  have hsquare :
      ((2 * amplitude * eta ^ 3 / Real.sqrt 3) *
        (h * Real.sqrt h)) ^ 2 ≤ error ^ 2 := by
    rw [htargetSq, herrorSq]
    exact henergy
  nlinarith

end BernsteinObstacle
