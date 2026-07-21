import BernsteinObstacle.CurvedExplicitThreshold
import BernsteinObstacle.InterfaceCoverCount
import BernsteinObstacle.FreeBoundaryRemainderSaturation
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Explicit global curved-interface saturation

Below the concrete threshold `h ≤ 1/(2 K c)`, every retained curved prism has
local ideal energy at least

`(amplitude² M / 6144) h^(d+2)`.

A codimension-one interface cover supplies `N / h^(d-1)` retained elements, so
the global ideal error is bounded below by

`sqrt ((amplitude² M / 6144) N) * h * sqrt h`.

The final theorem absorbs a higher-order free-boundary remainder and retains
one half of this explicit leading constant.
-/

/-- The exact local coefficient supplied by the curved prism theorem. -/
def curvedLocalEnergyConstant (amplitude M : ℝ) : ℝ :=
  amplitude ^ 2 * M / 6144

@[simp] theorem curvedLocalEnergyConstant_nonneg
    (amplitude M : ℝ) (hM : 0 ≤ M) :
    0 ≤ curvedLocalEnergyConstant amplitude M := by
  unfold curvedLocalEnergyConstant
  positivity

/-- Compose the explicit curved-prism theorem on every retained element with
interface-cover counting and global energy domination. -/
theorem curvedPatch_threeHalves_explicit
    {ι Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (S : Finset ι)
    (energy interfaceMass : ι → ℝ)
    (alpha beta t k : ι → Y → ℝ)
    (delta : ι → ℝ)
    (error amplitude K c h M N totalInterface coverC : ℝ)
    (d : ℕ)
    (herror : 0 ≤ error)
    (hK : 0 < K) (hc : 0 < c) (hh : 0 < h)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hd : 1 ≤ d)
    (hCoverC : 0 < coverC)
    (hthreshold : h ≤ curvedMeshThreshold K c)
    (hdelta : ∀ i ∈ S, |delta i| ≤ K * (c * h) ^ 2 / 2)
    (ht : ∀ i ∈ S, ∀ y, |t i y| ≤ c * h)
    (hk : ∀ i ∈ S, ∀ y, |k i y| ≤ K)
    (hMass : M * h ^ (d - 1) ≤ μ.real Set.univ)
    (hIntegrable : ∀ i ∈ S, Integrable
      (fun y => (1 - t i y * k i y) *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h ((delta i + c * h) / (2 * c * h))
          (alpha i y) (beta i y)) μ)
    (hLocalDominates : ∀ i ∈ S,
      (∫ y, (1 - t i y * k i y) *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h ((delta i + c * h) / (2 * c * h))
          (alpha i y) (beta i y) ∂μ) ≤ energy i)
    (hsumSq : ∑ i ∈ S, energy i ≤ error ^ 2)
    (hcovered : coverC * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocalInterface : ∀ i ∈ S,
      interfaceMass i ≤ coverC * h ^ (d - 1)) :
    Real.sqrt (curvedLocalEnergyConstant amplitude M * N) *
        (h * Real.sqrt h) ≤ error := by
  have hLocalC : 0 ≤ curvedLocalEnergyConstant amplitude M :=
    curvedLocalEnergyConstant_nonneg amplitude M hM
  have henergy : ∀ i ∈ S,
      curvedLocalEnergyConstant amplitude M * h ^ (d + 2) ≤ energy i := by
    intro i hi
    exact curvedWeightedPrism_localEnergy_lowerBound_explicit
      μ amplitude K c h (delta i) M (energy i) d
      (alpha i) (beta i) (t i) (k i)
      hK hc hh hM hd hthreshold (hdelta i hi)
      (ht i hi) (hk i hi) hMass (hIntegrable i hi) (hLocalDominates i hi)
  exact cutPatch_error_ge_threeHalves_of_interfaceCover_of_sum_le_sq
    S energy interfaceMass error
    (curvedLocalEnergyConstant amplitude M) N totalInterface coverC h d
    herror hd hh hLocalC hN hCoverC hsumSq henergy
    hcovered hcover hlocalInterface

/-- The explicit global curved lower bound survives a higher-order
free-boundary remainder. The conclusion retains half of the ideal leading
constant. -/
theorem curvedPatch_threeHalves_with_remainder_explicit
    {ι Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (S : Finset ι)
    (energy interfaceMass : ι → ℝ)
    (alpha beta t k : ι → Y → ℝ)
    (delta : ι → ℝ)
    (idealError actualError remainderError : ℝ)
    (amplitude K c h M N totalInterface coverC R : ℝ)
    (d κ : ℕ)
    (hidealError : 0 ≤ idealError)
    (hK : 0 < K) (hc : 0 < c) (hh : 0 < h)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hd : 1 ≤ d)
    (hCoverC : 0 < coverC) (hR : 0 ≤ R)
    (hthreshold : h ≤ curvedMeshThreshold K c)
    (hdelta : ∀ i ∈ S, |delta i| ≤ K * (c * h) ^ 2 / 2)
    (ht : ∀ i ∈ S, ∀ y, |t i y| ≤ c * h)
    (hk : ∀ i ∈ S, ∀ y, |k i y| ≤ K)
    (hMass : M * h ^ (d - 1) ≤ μ.real Set.univ)
    (hIntegrable : ∀ i ∈ S, Integrable
      (fun y => (1 - t i y * k i y) *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h ((delta i + c * h) / (2 * c * h))
          (alpha i y) (beta i y)) μ)
    (hLocalDominates : ∀ i ∈ S,
      (∫ y, (1 - t i y * k i y) *
        scaledQuadraticHingeAffineDerivativeErrorSq
          amplitude h ((delta i + c * h) / (2 * c * h))
          (alpha i y) (beta i y) ∂μ) ≤ energy i)
    (hsumSq : ∑ i ∈ S, energy i ≤ idealError ^ 2)
    (hcovered : coverC * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocalInterface : ∀ i ∈ S,
      interfaceMass i ≤ coverC * h ^ (d - 1))
    (htriangle : idealError ≤ actualError + remainderError)
    (hremainder : remainderError ≤ R * h ^ κ * (h * Real.sqrt h))
    (hsmall : 2 * R * h ^ κ ≤
      Real.sqrt (curvedLocalEnergyConstant amplitude M * N)) :
    (Real.sqrt (curvedLocalEnergyConstant amplitude M * N) / 2) *
        (h * Real.sqrt h) ≤ actualError := by
  have hideal := curvedPatch_threeHalves_explicit
    μ S energy interfaceMass alpha beta t k delta
    idealError amplitude K c h M N totalInterface coverC d
    hidealError hK hc hh hM hN hd hCoverC hthreshold
    hdelta ht hk hMass hIntegrable hLocalDominates hsumSq
    hcovered hcover hlocalInterface
  exact threeHalvesLowerBound_survives_higherOrderRemainder
    idealError actualError remainderError
    (Real.sqrt (curvedLocalEnergyConstant amplitude M * N)) R h κ
    hR hh.le hideal htriangle hremainder hsmall

end

end BernsteinObstacle
