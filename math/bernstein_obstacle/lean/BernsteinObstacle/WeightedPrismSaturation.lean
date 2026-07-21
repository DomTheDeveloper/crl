import BernsteinObstacle.ReferencePrismSaturation

open MeasureTheory

namespace BernsteinObstacle

noncomputable section

section WeightedPrism

variable {Y : Type*} [MeasurableSpace Y]

/-- A pointwise lower bound on a nonnegative change-of-variables Jacobian
transfers the sharp fiber obstruction to the weighted physical energy. -/
theorem weightedTransversePrism_fiberIntegral_lowerBound
    (μ : Measure Y) [IsFiniteMeasure μ]
    (amplitude h theta eta J0 : ℝ)
    (alpha beta jacobian : Y → ℝ)
    (hh : 0 ≤ h)
    (heta : 0 ≤ eta)
    (hJ0 : 0 ≤ J0)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta)
    (hJacobian : ∀ y, J0 ≤ jacobian y)
    (hIntegrable : Integrable
      (fun y => jacobian y *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta (alpha y) (beta y)) μ) :
    μ.real Set.univ *
        (J0 * (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3)) ≤
      ∫ y, jacobian y *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta (alpha y) (beta y) ∂μ := by
  let c : ℝ := ((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hconstNonneg :
      0 ≤ᵐ[μ] (fun _ : Y => J0 * c) :=
    Filter.Eventually.of_forall (fun _ => mul_nonneg hJ0 hc)
  have hpoint :
      (fun _ : Y => J0 * c) ≤ᵐ[μ]
        (fun y => jacobian y *
          scaledQuadraticHingeAffineDerivativeErrorSq
            amplitude h theta (alpha y) (beta y)) :=
    Filter.Eventually.of_forall fun y => by
      have hfiber :
          c ≤ scaledQuadraticHingeAffineDerivativeErrorSq
            amplitude h theta (alpha y) (beta y) := by
        exact scaledQuadraticHingeAffineDerivativeErrorSq_uniformLowerBound
          amplitude h theta eta (alpha y) (beta y)
          hh heta hleft hright
      have hjacNonneg : 0 ≤ jacobian y := hJ0.trans (hJacobian y)
      exact mul_le_mul (hJacobian y) hfiber hc hjacNonneg
  have hmono := integral_mono_of_nonneg hconstNonneg hIntegrable hpoint
  simpa [c, smul_eq_mul] using hmono

/-- A Jacobian lower bound, a tangential mass lower bound, and the exact
fiberwise quadratic obstruction imply the mapped elementwise `h^(d+2)` lower
bound. -/
theorem weightedTransversePrism_localEnergy_lowerBound
    (μ : Measure Y) [IsFiniteMeasure μ]
    (amplitude h theta eta M J0 : ℝ)
    (d : ℕ)
    (alpha beta jacobian : Y → ℝ)
    (hd : 1 ≤ d)
    (hh : 0 ≤ h)
    (heta : 0 ≤ eta)
    (hM : 0 ≤ M)
    (hJ0 : 0 ≤ J0)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta)
    (hMass : M * h ^ (d - 1) ≤ μ.real Set.univ)
    (hJacobian : ∀ y, J0 ≤ jacobian y)
    (hIntegrable : Integrable
      (fun y => jacobian y *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta (alpha y) (beta y)) μ) :
    (J0 * (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M)) *
        h ^ (d + 2) ≤
      ∫ y, jacobian y *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta (alpha y) (beta y) ∂μ := by
  let c : ℝ := J0 * (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hmassScaled :
      (M * h ^ (d - 1)) * c ≤ μ.real Set.univ * c :=
    mul_le_mul_of_nonneg_right hMass hc
  have hfiber := weightedTransversePrism_fiberIntegral_lowerBound
    μ amplitude h theta eta J0 alpha beta jacobian
    hh heta hJ0 hleft hright hJacobian hIntegrable
  have hpow : h ^ (d - 1) * h ^ 3 = h ^ (d + 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (J0 * (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M)) *
        h ^ (d + 2) = (M * h ^ (d - 1)) * c := by
      dsimp [c]
      rw [← hpow]
      ring
    _ ≤ μ.real Set.univ * c := hmassScaled
    _ = μ.real Set.univ *
        (J0 * (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * h ^ 3)) := by
      rfl
    _ ≤ ∫ y, jacobian y *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta (alpha y) (beta y) ∂μ := hfiber

/-- Jacobian-weighted local lower bound specialized to an actual quadratic
polynomial restricted to transverse affine fibers. -/
theorem weightedTransversePrism_quadraticPolynomial_localEnergy_lowerBound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (q : QuadraticPolynomialData E)
    (base : Y → E) (direction : E)
    (jacobian : Y → ℝ)
    (amplitude h theta eta M J0 : ℝ)
    (d : ℕ)
    (hd : 1 ≤ d)
    (hh : 0 ≤ h)
    (heta : 0 ≤ eta)
    (hM : 0 ≤ M)
    (hJ0 : 0 ≤ J0)
    (hleft : eta ≤ theta)
    (hright : theta ≤ 1 - eta)
    (hMass : M * h ^ (d - 1) ≤ μ.real Set.univ)
    (hJacobian : ∀ y, J0 ≤ jacobian y)
    (hIntegrable : Integrable
      (fun y => jacobian y *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta
          (q.lineDerivativeSlope direction)
          (q.lineDerivativeIntercept (base y) direction)) μ) :
    (J0 * (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M)) *
        h ^ (d + 2) ≤
      ∫ y, jacobian y *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h theta
          (q.lineDerivativeSlope direction)
          (q.lineDerivativeIntercept (base y) direction) ∂μ := by
  exact weightedTransversePrism_localEnergy_lowerBound
    μ amplitude h theta eta M J0 d
    (fun _ => q.lineDerivativeSlope direction)
    (fun y => q.lineDerivativeIntercept (base y) direction)
    jacobian hd hh heta hM hJ0 hleft hright hMass hJacobian hIntegrable

end WeightedPrism

end

end BernsteinObstacle
