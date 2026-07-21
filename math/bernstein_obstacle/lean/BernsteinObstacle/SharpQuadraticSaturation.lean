import BernsteinObstacle.NormedPhysicalSaturation
import BernsteinObstacle.GrandSaturationRate
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Two-sided sharp quadratic-contact saturation

This file closes the sharpness package by combining the certified physical
full-space lower bound with the quadratic-contact upper estimate.  On the
asymptotic range `0 < h ≤ 1`, each quadratic bulk term `h^2` is bounded by the
interface scale `h * sqrt h`.  Consequently the approximation error is trapped
between two explicit multiples of `h * sqrt h`, and the lower multiplier is
strictly positive under the stated nondegeneracy assumptions.
-/

/-- On `0 ≤ h ≤ 1`, the quadratic bulk scale is dominated by the
three-halves interface scale. -/
theorem quadraticScale_le_threeHalvesScale
    (h : ℝ) (hh : 0 ≤ h) (hle : h ≤ 1) :
    h ^ 2 ≤ h * Real.sqrt h := by
  have hsq_le : h ^ 2 ≤ h := by
    nlinarith
  have hh_le_sqrt : h ≤ Real.sqrt h :=
    (Real.le_sqrt hh hh).2 hsq_le
  have hmul := mul_le_mul_of_nonneg_left hh_le_sqrt hh
  simpa [pow_two] using hmul

/-- Flagship sharp-saturation theorem for quadratic contact.

The first conjunct certifies that the explicit lower coefficient is nonzero.
The second and third conjuncts give the two-sided `h * sqrt h` sandwich.  The
lower estimate is the full-space physical obstruction; the upper estimate is
the quadratic-contact energy bound with both bulk `h^2` terms absorbed into the
same three-halves scale. -/
theorem bernsteinBezier_quadraticContact_fullSpace_threeHalvesSaturation
    {E ι : Type*} [NormedAddCommGroup E]
    (S : Finset ι) (energy interfaceMass : ι → ℝ)
    (actual ideal approx remainder : E)
    (alpha P A B J0 amplitude eta M N totalInterface coverC R h : ℝ)
    (d κ : ℕ)
    (hdecomp : actual = ideal + remainder)
    (hd : 1 ≤ d)
    (hh : 0 < h)
    (hle : h ≤ 1)
    (halpha : 0 < alpha)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hJ0 : 0 < J0)
    (hamplitude : 0 < amplitude)
    (heta : 0 < eta)
    (hM : 0 < M)
    (hN : 0 < N)
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
          (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N))
    (hupperEnergy :
      alpha * ‖actual - approx‖ ^ 2 ≤
        P * h ^ 4 + A * h ^ 4 + B * h ^ 3) :
    0 < Real.sqrt
          (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N) / 2 ∧
      (Real.sqrt
          (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N) / 2) *
          (h * Real.sqrt h) ≤ ‖actual - approx‖ ∧
      ‖actual - approx‖ ≤
        (3 * Real.sqrt (max P (max A B) / alpha)) *
          (h * Real.sqrt h) := by
  have hlowerCoefficient :
      0 < Real.sqrt
          (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N) / 2 :=
    mappedQuadraticHingeLeadingCoefficient_pos
      J0 amplitude eta M N hJ0 hamplitude heta hM hN
  have hlower :
      (Real.sqrt
          (mappedQuadraticHingeLocalConstant J0 amplitude eta M * N) / 2) *
          (h * Real.sqrt h) ≤ ‖actual - approx‖ :=
    norm_physicalMappedQuadraticHinge_threeHalvesLowerBound
      S energy interfaceMass actual ideal approx remainder
      J0 amplitude eta M N totalInterface coverC R h d κ
      hdecomp hd hh hJ0.le hM.le hN.le hCoverC hR
      hidealErrorSq henergy hcovered hcover hlocalInterface
      hremainder hsmall
  have hupperBase :
      ‖actual - approx‖ ≤
        Real.sqrt (max P (max A B) / alpha) *
          (h ^ 2 + h ^ 2 + h * Real.sqrt h) := by
    exact grandSharpRate_quadraticContact_saturation
      ‖actual - approx‖ alpha P A B h h 2 2 2
      (by omega) (norm_nonneg _) halpha hP hA hB
      hh.le hh.le (by simpa using hupperEnergy)
  have hquadratic := quadraticScale_le_threeHalvesScale h hh.le hle
  have hsum :
      h ^ 2 + h ^ 2 + h * Real.sqrt h ≤
        3 * (h * Real.sqrt h) := by
    nlinarith
  have hcoefficient :
      0 ≤ Real.sqrt (max P (max A B) / alpha) :=
    Real.sqrt_nonneg _
  have hupper :
      ‖actual - approx‖ ≤
        (3 * Real.sqrt (max P (max A B) / alpha)) *
          (h * Real.sqrt h) := by
    calc
      ‖actual - approx‖ ≤
          Real.sqrt (max P (max A B) / alpha) *
            (h ^ 2 + h ^ 2 + h * Real.sqrt h) := hupperBase
      _ ≤ Real.sqrt (max P (max A B) / alpha) *
            (3 * (h * Real.sqrt h)) :=
          mul_le_mul_of_nonneg_left hsum hcoefficient
      _ = (3 * Real.sqrt (max P (max A B) / alpha)) *
            (h * Real.sqrt h) := by ring
  exact ⟨hlowerCoefficient, hlower, hupper⟩

end BernsteinObstacle
