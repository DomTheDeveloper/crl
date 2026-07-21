import BernsteinObstacle.TransversePrismSaturation

open MeasureTheory

namespace BernsteinObstacle

noncomputable section

section ReferencePrism

variable {Y : Type*} [MeasurableSpace Y]

/-- On the reference product prism, the local normal-derivative energy is
exactly the iterated fiber integral. Hence the local `h^(d+2)` obstruction
follows without a separate energy-domination assumption. -/
theorem referencePrism_exactEnergy_lowerBound
    (μ : Measure Y) [IsFiniteMeasure μ]
    (amplitude h theta eta M : ℝ)
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
        amplitude h theta (alpha y) (beta y)) μ) :
    (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M) *
        h ^ (d + 2) ≤
      ∫ y, scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta (alpha y) (beta y) ∂μ := by
  exact transversePrism_localEnergy_lowerBound
    μ amplitude h theta eta M
    (∫ y, scaledQuadraticHingeAffineDerivativeErrorSq
      amplitude h theta (alpha y) (beta y) ∂μ)
    d alpha beta hd hh heta hM hleft hright hMass hIntegrable le_rfl

/-- Exact reference-prism lower bound for a genuine coordinate-free quadratic
polynomial restricted to transverse affine lines. -/
theorem referencePrism_quadraticPolynomial_exactEnergy_lowerBound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (q : QuadraticPolynomialData E)
    (base : Y → E) (direction : E)
    (amplitude h theta eta M : ℝ)
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
        (q.lineDerivativeIntercept (base y) direction)) μ) :
    (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M) *
        h ^ (d + 2) ≤
      ∫ y, scaledQuadraticHingeAffineDerivativeErrorSq
        amplitude h theta
        (q.lineDerivativeSlope direction)
        (q.lineDerivativeIntercept (base y) direction) ∂μ := by
  exact transversePrism_quadraticPolynomial_localEnergy_lowerBound
    μ q base direction amplitude h theta eta M
    (∫ y, scaledQuadraticHingeAffineDerivativeErrorSq
      amplitude h theta
      (q.lineDerivativeSlope direction)
      (q.lineDerivativeIntercept (base y) direction) ∂μ)
    d hd hh heta hM hleft hright hMass hIntegrable le_rfl

end ReferencePrism

end

end BernsteinObstacle
