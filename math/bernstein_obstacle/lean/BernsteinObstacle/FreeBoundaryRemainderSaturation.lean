import BernsteinObstacle.MinkowskiSaturation
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Stability of the three-halves obstruction under higher-order remainders

A regular free-boundary solution is only asymptotic to the exact quadratic hinge.
The reverse triangle inequality reduces the physical lower bound to an explicit
smallness condition on the higher-order remainder. This file isolates that
absorption step without introducing any PDE-specific assumptions.
-/

/-- An actual decomposition `actual = ideal + remainder` supplies the exact
reverse-triangle comparison used by the scalar saturation argument. -/
theorem idealApproximationError_le_actual_add_remainder
    {E : Type*} [NormedAddCommGroup E]
    (actual ideal approx remainder : E)
    (hdecomp : actual = ideal + remainder) :
    ‖ideal - approx‖ ≤ ‖actual - approx‖ + ‖remainder‖ := by
  have hid : ideal - approx = (actual - approx) - remainder := by
    rw [hdecomp]
    abel
  rw [hid]
  exact norm_sub_le _ _

/-- An ideal lower bound survives whenever the perturbation is at most half of
the leading obstruction. -/
theorem lowerBound_survives_half_remainder
    (idealError actualError remainderError leading scale : ℝ)
    (hideal : leading * scale ≤ idealError)
    (htriangle : idealError ≤ actualError + remainderError)
    (hremainder : remainderError ≤ (leading / 2) * scale) :
    (leading / 2) * scale ≤ actualError := by
  linarith

/-- A higher-order remainder of size
`R * h^κ * (h * sqrt h)` is absorbable when `2 * R * h^κ ≤ leading`.
The resulting physical lower bound retains half of the sharp leading constant. -/
theorem threeHalvesLowerBound_survives_higherOrderRemainder
    (idealError actualError remainderError leading R h : ℝ)
    (κ : ℕ)
    (hR : 0 ≤ R)
    (hh : 0 ≤ h)
    (hideal : leading * (h * Real.sqrt h) ≤ idealError)
    (htriangle : idealError ≤ actualError + remainderError)
    (hremainder :
      remainderError ≤ R * h ^ κ * (h * Real.sqrt h))
    (hsmall : 2 * R * h ^ κ ≤ leading) :
    (leading / 2) * (h * Real.sqrt h) ≤ actualError := by
  have hscale : 0 ≤ h * Real.sqrt h :=
    mul_nonneg hh (Real.sqrt_nonneg _)
  have hcoefficient : R * h ^ κ ≤ leading / 2 := by
    linarith
  have habsorb :
      R * h ^ κ * (h * Real.sqrt h) ≤
        (leading / 2) * (h * Real.sqrt h) :=
    mul_le_mul_of_nonneg_right hcoefficient hscale
  exact lowerBound_survives_half_remainder
    idealError actualError remainderError leading (h * Real.sqrt h)
    hideal htriangle (hremainder.trans habsorb)

/-- Normed-space form of remainder absorption. The reverse-triangle hypothesis
is derived from the exact decomposition instead of supplied independently. -/
theorem norm_threeHalvesLowerBound_survives_higherOrderRemainder
    {E : Type*} [NormedAddCommGroup E]
    (actual ideal approx remainder : E)
    (leading R h : ℝ) (κ : ℕ)
    (hdecomp : actual = ideal + remainder)
    (hR : 0 ≤ R)
    (hh : 0 ≤ h)
    (hideal :
      leading * (h * Real.sqrt h) ≤ ‖ideal - approx‖)
    (hremainder :
      ‖remainder‖ ≤ R * h ^ κ * (h * Real.sqrt h))
    (hsmall : 2 * R * h ^ κ ≤ leading) :
    (leading / 2) * (h * Real.sqrt h) ≤ ‖actual - approx‖ := by
  exact threeHalvesLowerBound_survives_higherOrderRemainder
    ‖ideal - approx‖ ‖actual - approx‖ ‖remainder‖ leading R h κ
    hR hh hideal
    (idealApproximationError_le_actual_add_remainder
      actual ideal approx remainder hdecomp)
    hremainder hsmall

/-- If the higher-order coefficient already satisfies a half-leading bound,
then the physical three-halves obstruction follows directly. -/
theorem threeHalvesLowerBound_survives_coefficientBound
    (idealError actualError remainderError leading remainderCoefficient h : ℝ)
    (hh : 0 ≤ h)
    (hideal : leading * (h * Real.sqrt h) ≤ idealError)
    (htriangle : idealError ≤ actualError + remainderError)
    (hremainder :
      remainderError ≤ remainderCoefficient * (h * Real.sqrt h))
    (hcoefficient : remainderCoefficient ≤ leading / 2) :
    (leading / 2) * (h * Real.sqrt h) ≤ actualError := by
  have hscale : 0 ≤ h * Real.sqrt h :=
    mul_nonneg hh (Real.sqrt_nonneg _)
  have habsorb :
      remainderCoefficient * (h * Real.sqrt h) ≤
        (leading / 2) * (h * Real.sqrt h) :=
    mul_le_mul_of_nonneg_right hcoefficient hscale
  exact lowerBound_survives_half_remainder
    idealError actualError remainderError leading (h * Real.sqrt h)
    hideal htriangle (hremainder.trans habsorb)

end BernsteinObstacle
