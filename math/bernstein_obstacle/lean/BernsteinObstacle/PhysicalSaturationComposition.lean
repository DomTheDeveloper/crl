import BernsteinObstacle.InterfaceCoverCount
import BernsteinObstacle.FreeBoundaryRemainderSaturation
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Physical full-space saturation composition

This file composes the independently audited lower-bound layers. Once the
mapped-prism estimate supplies a uniform local constant, interface coverage
supplies the codimension-one element count, and the free-boundary remainder is
higher order, the actual physical error retains a nonzero `h * sqrt h` lower
bound.
-/

/-- Explicit local squared-energy constant produced by a mapped transverse
prism with Jacobian lower bound `J0`, hinge amplitude `amplitude`, phase margin
`eta`, and tangential-mass constant `M`. -/
noncomputable def mappedQuadraticHingeLocalConstant
    (J0 amplitude eta M : ℝ) : ℝ :=
  J0 * (((4 : ℝ) / 3) * amplitude ^ 2 * eta ^ 6 * M)

/-- The mapped local constant is nonnegative under the natural geometric and
nondegeneracy assumptions. -/
theorem mappedQuadraticHingeLocalConstant_nonneg
    (J0 amplitude eta M : ℝ)
    (hJ0 : 0 ≤ J0) (hM : 0 ≤ M) :
    0 ≤ mappedQuadraticHingeLocalConstant J0 amplitude eta M := by
  unfold mappedQuadraticHingeLocalConstant
  positivity

/-- Strictly positive geometry, hinge amplitude, and phase margin give a
strictly positive local saturation constant. -/
theorem mappedQuadraticHingeLocalConstant_pos
    (J0 amplitude eta M : ℝ)
    (hJ0 : 0 < J0) (hamplitude : 0 < amplitude)
    (heta : 0 < eta) (hM : 0 < M) :
    0 < mappedQuadraticHingeLocalConstant J0 amplitude eta M := by
  unfold mappedQuadraticHingeLocalConstant
  positivity

/-- Under a positive lower cut-count constant, the coefficient in the final
`h * sqrt h` obstruction is itself strictly positive. -/
theorem mappedQuadraticHingeLeadingCoefficient_pos
    (J0 amplitude eta M N : ℝ)
    (hJ0 : 0 < J0) (hamplitude : 0 < amplitude)
    (heta : 0 < eta) (hM : 0 < M) (hN : 0 < N) :
    0 < Real.sqrt
      (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N) / 2 := by
  have hlocal :
      0 < mappedQuadraticHingeLocalConstant J0 amplitude eta M :=
    mappedQuadraticHingeLocalConstant_pos
      J0 amplitude eta M hJ0 hamplitude heta hM
  have hproduct :
      0 < mappedQuadraticHingeLocalConstant J0 amplitude eta M * N :=
    mul_pos hlocal hN
  positivity

/-- Complete lower-bound composition with a higher-order free-boundary
remainder. The exact quadratic model first yields the ideal global
three-halves obstruction. The reverse triangle inequality and the explicit
smallness condition then preserve half of that leading constant for the actual
physical solution. -/
theorem physicalCutPatch_threeHalvesLowerBound_of_interfaceCover_and_remainder
    {ι : Type*} (S : Finset ι)
    (energy interfaceMass : ι → ℝ)
    (idealError actualError remainderError localC N totalInterface coverC R h : ℝ)
    (d κ : ℕ)
    (hidealError : 0 ≤ idealError)
    (hd : 1 ≤ d)
    (hh : 0 < h)
    (hLocalC : 0 ≤ localC)
    (hN : 0 ≤ N)
    (hCoverC : 0 < coverC)
    (hR : 0 ≤ R)
    (hidealErrorSq : idealError ^ 2 = ∑ i ∈ S, energy i)
    (henergy : ∀ i ∈ S, localC * h ^ (d + 2) ≤ energy i)
    (hcovered : coverC * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocalInterface :
      ∀ i ∈ S, interfaceMass i ≤ coverC * h ^ (d - 1))
    (htriangle : idealError ≤ actualError + remainderError)
    (hremainder :
      remainderError ≤ R * h ^ κ * (h * Real.sqrt h))
    (hsmall : 2 * R * h ^ κ ≤ Real.sqrt (localC * N)) :
    (Real.sqrt (localC * N) / 2) * (h * Real.sqrt h) ≤ actualError := by
  have hideal :
      Real.sqrt (localC * N) * (h * Real.sqrt h) ≤ idealError :=
    cutPatch_error_ge_threeHalves_of_interfaceCover
      S energy interfaceMass idealError localC N totalInterface coverC h d
      hidealError hd hh hLocalC hN hCoverC hidealErrorSq henergy
      hcovered hcover hlocalInterface
  exact threeHalvesLowerBound_survives_higherOrderRemainder
    idealError actualError remainderError (Real.sqrt (localC * N)) R h κ
    hR (le_of_lt hh) hideal htriangle hremainder hsmall

/-- Explicit mapped-quadratic specialization of the full physical saturation
composition. -/
theorem physicalMappedQuadraticHinge_threeHalvesLowerBound
    {ι : Type*} (S : Finset ι)
    (energy interfaceMass : ι → ℝ)
    (idealError actualError remainderError : ℝ)
    (J0 amplitude eta M N totalInterface coverC R h : ℝ)
    (d κ : ℕ)
    (hidealError : 0 ≤ idealError)
    (hd : 1 ≤ d)
    (hh : 0 < h)
    (hJ0 : 0 ≤ J0)
    (hM : 0 ≤ M)
    (hN : 0 ≤ N)
    (hCoverC : 0 < coverC)
    (hR : 0 ≤ R)
    (hidealErrorSq : idealError ^ 2 = ∑ i ∈ S, energy i)
    (henergy : ∀ i ∈ S,
      mappedQuadraticHingeLocalConstant J0 amplitude eta M *
        h ^ (d + 2) ≤ energy i)
    (hcovered : coverC * N ≤ totalInterface)
    (hcover : totalInterface ≤ ∑ i ∈ S, interfaceMass i)
    (hlocalInterface :
      ∀ i ∈ S, interfaceMass i ≤ coverC * h ^ (d - 1))
    (htriangle : idealError ≤ actualError + remainderError)
    (hremainder :
      remainderError ≤ R * h ^ κ * (h * Real.sqrt h))
    (hsmall :
      2 * R * h ^ κ ≤
        Real.sqrt
          (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N)) :
    (Real.sqrt
        (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N) / 2) *
      (h * Real.sqrt h) ≤ actualError := by
  exact physicalCutPatch_threeHalvesLowerBound_of_interfaceCover_and_remainder
    S energy interfaceMass idealError actualError remainderError
    (mappedQuadraticHingeLocalConstant J0 amplitude eta M)
    N totalInterface coverC R h d κ hidealError hd hh
    (mappedQuadraticHingeLocalConstant_nonneg J0 amplitude eta M hJ0 hM)
    hN hCoverC hR hidealErrorSq henergy hcovered hcover
    hlocalInterface htriangle hremainder hsmall

end BernsteinObstacle
