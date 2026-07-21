import BernsteinObstacle.QuadraticHingeProjection
import BernsteinObstacle.QuadraticLineRestriction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory

namespace BernsteinObstacle

noncomputable section

/-!
# Transverse-prism lifting of the quadratic-hinge obstruction

The one-dimensional sharp lower bound is integrated over a finite tangential
cross-section. This file intentionally keeps the geometric change-of-variables
step explicit: a later physical simplex theorem must provide the cross-section
measure lower bound and show that the physical local energy dominates this
iterated transverse energy.
-/

section TransversePrism

variable {Y : Type*} [MeasurableSpace Y]

/-- Integrating the sharp one-dimensional lower bound over a finite tangential
cross-section multiplies it by the real mass of that cross-section. The
functions `alpha` and `beta` are the affine normal-derivative coefficients of an
arbitrary quadratic approximant along each transverse fiber. -/
theorem transversePrism_fiberIntegral_lowerBound
    (μ : Measure Y) [IsFiniteMeasure μ]
    (amplitude h theta eta : ℝ)
    (alpha beta : Y → ℝ)
    (hh : 0 ≤ h)
    (heta : 0 ≤ eta)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta)
    (hIntegrable : Integrable
      (fun y => scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta (alpha y) (beta y)) μ) :
    μ.real Set.univ *
        (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3) ≤
      ∫ y, scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta (alpha y) (beta y) ∂μ := by
  let c : ℝ := ((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hconstNonneg :
      0 ≤ᵐ[μ] (fun _ : Y => c) :=
    Filter.Eventually.of_forall (fun _ => hc)
  have hpoint :
      (fun _ : Y => c) ≤ᵐ[μ]
        (fun y => scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta (alpha y) (beta y)) :=
    Filter.Eventually.of_forall (fun y =>
      scaledQuadraticHingeAffineDerivativeErrorSq_uniformLowerBound
        amplitude h theta eta (alpha y) (beta y)
        hh heta hleft hright)
  have hmono := integral_mono_of_nonneg hconstNonneg hIntegrable hpoint
  simpa [c, smul_eq_mul] using hmono

/-- A tangential cross-section of mass at least `M * h^(d-1)` lifts the
one-dimensional `h^3` obstruction to an elementwise `h^(d+2)` lower bound.

The hypothesis `hLocalDominates` is the precise remaining change-of-variables
obligation for a physical cut simplex: its local squared `H¹` error must dominate
the iterated normal-derivative error over the embedded transverse prism. -/
theorem transversePrism_localEnergy_lowerBound
    (μ : Measure Y) [IsFiniteMeasure μ]
    (amplitude h theta eta M localEnergy : ℝ)
    (d : ℕ)
    (alpha beta : Y → ℝ)
    (hd : 1 ≤ d)
    (hh : 0 ≤ h)
    (heta : 0 ≤ eta)
    (hM : 0 ≤ M)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta)
    (hMass : M * h ^ (d - 1) ≤ μ.real Set.univ)
    (hIntegrable : Integrable
      (fun y => scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta (alpha y) (beta y)) μ)
    (hLocalDominates :
      (∫ y, scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta (alpha y) (beta y) ∂μ) ≤ localEnergy) :
    (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M) *
        h ^ (d + 2) ≤ localEnergy := by
  let c : ℝ := ((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hmassScaled :
      (M * h ^ (d - 1)) * c ≤ μ.real Set.univ * c :=
    mul_le_mul_of_nonneg_right hMass hc
  have hfiber := transversePrism_fiberIntegral_lowerBound
    μ amplitude h theta eta alpha beta hh heta hleft hright hIntegrable
  have hpow : h ^ (d - 1) * h ^ 3 = h ^ (d + 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M) *
        h ^ (d + 2) = (M * h ^ (d - 1)) * c := by
      dsimp [c]
      rw [← hpow]
      ring
    _ ≤ μ.real Set.univ * c := hmassScaled
    _ = μ.real Set.univ *
        (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3) := by
      rfl
    _ ≤ ∫ y, scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta (alpha y) (beta y) ∂μ := hfiber
    _ ≤ localEnergy := hLocalDominates

/-- Specialization of the prism lower bound to an actual coordinate-free
quadratic polynomial. The fiber slope and intercept are derived from the
quadratic restriction theorem rather than supplied as unrelated functions. -/
theorem transversePrism_quadraticPolynomial_localEnergy_lowerBound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (q : QuadraticPolynomialData E)
    (base : Y → E) (direction : E)
    (amplitude h theta eta M localEnergy : ℝ)
    (d : ℕ)
    (hd : 1 ≤ d)
    (hh : 0 ≤ h)
    (heta : 0 ≤ eta)
    (hM : 0 ≤ M)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta)
    (hMass : M * h ^ (d - 1) ≤ μ.real Set.univ)
    (hIntegrable : Integrable
      (fun y => scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta
        (q.lineDerivativeSlope direction)
        (q.lineDerivativeIntercept (base y) direction)) μ)
    (hLocalDominates :
      (∫ y, scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta
        (q.lineDerivativeSlope direction)
        (q.lineDerivativeIntercept (base y) direction) ∂μ) ≤ localEnergy) :
    (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M) *
        h ^ (d + 2) ≤ localEnergy := by
  exact transversePrism_localEnergy_lowerBound
    μ amplitude h theta eta M localEnergy d
    (fun _ => q.lineDerivativeSlope direction)
    (fun y => q.lineDerivativeIntercept (base y) direction)
    hd hh heta hM hleft hright hMass hIntegrable hLocalDominates

end TransversePrism

end

end BernsteinObstacle
