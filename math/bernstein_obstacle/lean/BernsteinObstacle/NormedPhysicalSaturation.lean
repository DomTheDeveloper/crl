import BernsteinObstacle.PhysicalSaturationComposition
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Normed-space physical saturation theorem

The scalar composition theorem is lifted to actual approximation objects.  The
reverse-triangle comparison is derived from the exact decomposition
`actual = ideal + remainder`, so the final conclusion is a direct lower bound
for `‖actual - approx‖`.
-/

/-- Normed-space form of the complete cut-patch saturation theorem. -/
theorem norm_physicalCutPatch_threeHalvesLowerBound_of_interfaceCover_and_remainder
    {E ι : Type*} [NormedAddCommGroup E]
    (S : Finset ι) (energy interfaceMass : ι → ℝ)
    (actual ideal approx remainder : E)
    (localC N totalInterface coverC R h : ℝ)
    (d κ : ℕ)
    (hdecomp : actual = ideal + remainder)
    (hd : 1 ≤ d)
    (hh : 0 < h)
    (hLocalC : 0 ≤ localC)
    (hN : 0 ≤ N)
    (hCoverC : 0 < coverC)
    (hR : 0 ≤ R)
    (hidealErrorSq : ‖ideal - approx‖ ^ 2 = ∑ i ∈ S, energy i)
    (henergy : ∀ i ∈ S, localC * h ^ (d + 2) ≤ energy i)
    (hcovered : coverC * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocalInterface :
      ∀ i ∈ S, interfaceMass i ≤ coverC * h ^ (d - 1))
    (hremainder :
      ‖remainder‖ ≤ R * h ^ κ * (h * Real.sqrt h))
    (hsmall : 2 * R * h ^ κ ≤ Real.sqrt (localC * N)) :
    (Real.sqrt (localC * N) / 2) * (h * Real.sqrt h) ≤
      ‖actual - approx‖ := by
  exact physicalCutPatch_threeHalvesLowerBound_of_interfaceCover_and_remainder
    S energy interfaceMass
    ‖ideal - approx‖ ‖actual - approx‖ ‖remainder‖
    localC N totalInterface coverC R h d κ
    (norm_nonneg _) hd hh hLocalC hN hCoverC hR
    hidealErrorSq henergy hcovered hcover hlocalInterface
    (idealApproximationError_le_actual_add_remainder
      actual ideal approx remainder hdecomp)
    hremainder hsmall

/-- Explicit mapped-quadratic normed-space specialization.  Under positive
geometric constants, its leading coefficient is nonzero by
`mappedQuadraticHingeLeadingCoefficient_pos`. -/
theorem norm_physicalMappedQuadraticHinge_threeHalvesLowerBound
    {E ι : Type*} [NormedAddCommGroup E]
    (S : Finset ι) (energy interfaceMass : ι → ℝ)
    (actual ideal approx remainder : E)
    (J0 amplitude eta M N totalInterface coverC R h : ℝ)
    (d κ : ℕ)
    (hdecomp : actual = ideal + remainder)
    (hd : 1 ≤ d)
    (hh : 0 < h)
    (hJ0 : 0 ≤ J0)
    (hM : 0 ≤ M)
    (hN : 0 ≤ N)
    (hCoverC : 0 < coverC)
    (hR : 0 ≤ R)
    (hidealErrorSq : ‖ideal - approx‖ ^ 2 = ∑ i ∈ S, energy i)
    (henergy : ∀ i ∈ S,
      mappedQuadraticHingeLocalConstant J0 amplitude eta M *
        h ^ (d + 2) ≤ energy i)
    (hcovered : coverC * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocalInterface :
      ∀ i ∈ S, interfaceMass i ≤ coverC * h ^ (d - 1))
    (hremainder :
      ‖remainder‖ ≤ R * h ^ κ * (h * Real.sqrt h))
    (hsmall :
      2 * R * h ^ κ ≤
        Real.sqrt
          (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N)) :
    (Real.sqrt
        (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N) / 2) *
      (h * Real.sqrt h) ≤ ‖actual - approx‖ := by
  exact norm_physicalCutPatch_threeHalvesLowerBound_of_interfaceCover_and_remainder
    S energy interfaceMass actual ideal approx remainder
    (mappedQuadraticHingeLocalConstant J0 amplitude eta M)
    N totalInterface coverC R h d κ hdecomp hd hh
    (mappedQuadraticHingeLocalConstant_nonneg J0 amplitude eta M hJ0 hM)
    hN hCoverC hR hidealErrorSq henergy hcovered hcover
    hlocalInterface hremainder hsmall

end BernsteinObstacle
