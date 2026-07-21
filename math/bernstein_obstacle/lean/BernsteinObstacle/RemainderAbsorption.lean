import BernsteinObstacle.LowerStripSaturation
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Stability of three-halves saturation under higher-order remainders

The physical free-boundary profile is a quadratic hinge plus a smoother
remainder. This file isolates the exact algebra needed to retain a positive
fraction of the sharp `h * sqrt h` obstruction after subtracting that
higher-order remainder.
-/

/-- A model lower bound `A * h^(3/2)` survives a remainder bounded by
`B * h^κ * h^(3/2)` whenever `B * h^κ ≤ A / 2`. -/
theorem threeHalvesLowerBound_stable_under_higherOrderRemainder
    (modelError trueError remainderError A B h : ℝ) (κ : ℕ)
    (hmodelError : 0 ≤ modelError)
    (htrueError : 0 ≤ trueError)
    (hremainderError : 0 ≤ remainderError)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hmodel : A * (h * Real.sqrt h) ≤ modelError)
    (hremainder : remainderError ≤
      (B * h ^ κ) * (h * Real.sqrt h))
    (htriangle : modelError ≤ trueError + remainderError)
    (hsmall : B * h ^ κ ≤ A / 2) :
    (A / 2) * (h * Real.sqrt h) ≤ trueError := by
  have hscale : 0 ≤ h * Real.sqrt h :=
    mul_nonneg hh (Real.sqrt_nonneg h)
  have hremainderHalf :
      remainderError ≤ (A / 2) * (h * Real.sqrt h) := by
    exact hremainder.trans
      (mul_le_mul_of_nonneg_right hsmall hscale)
  nlinarith

/-- Version with a retained fraction `rho`, useful when a later physical
regularity theorem gives a sharper remainder threshold. -/
theorem threeHalvesLowerBound_stable_with_fraction
    (modelError trueError remainderError A rho h : ℝ)
    (hmodelError : 0 ≤ modelError)
    (htrueError : 0 ≤ trueError)
    (hremainderError : 0 ≤ remainderError)
    (hA : 0 ≤ A) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hh : 0 ≤ h)
    (hmodel : A * (h * Real.sqrt h) ≤ modelError)
    (hremainder : remainderError ≤
      ((1 - rho) * A) * (h * Real.sqrt h))
    (htriangle : modelError ≤ trueError + remainderError) :
    (rho * A) * (h * Real.sqrt h) ≤ trueError := by
  have hscale : 0 ≤ h * Real.sqrt h :=
    mul_nonneg hh (Real.sqrt_nonneg h)
  nlinarith

/-- Direct continuation of the global cut-patch theorem: once the exact
quadratic model has coefficient `sqrt (C*N)`, any higher-order free-boundary
remainder satisfying the explicit half-constant threshold leaves a nonzero
three-halves obstruction for the true profile. -/
theorem freeBoundary_error_ge_half_threeHalves_of_model_remainder
    (modelError trueError remainderError C N B h : ℝ) (κ : ℕ)
    (hmodelError : 0 ≤ modelError)
    (htrueError : 0 ≤ trueError)
    (hremainderError : 0 ≤ remainderError)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hmodel : Real.sqrt (C * N) * (h * Real.sqrt h) ≤ modelError)
    (hremainder : remainderError ≤
      (B * h ^ κ) * (h * Real.sqrt h))
    (htriangle : modelError ≤ trueError + remainderError)
    (hsmall : B * h ^ κ ≤ Real.sqrt (C * N) / 2) :
    (Real.sqrt (C * N) / 2) * (h * Real.sqrt h) ≤ trueError := by
  exact threeHalvesLowerBound_stable_under_higherOrderRemainder
    modelError trueError remainderError (Real.sqrt (C * N)) B h κ
    hmodelError htrueError hremainderError (Real.sqrt_nonneg _) hB hh
    hmodel hremainder htriangle hsmall

end BernsteinObstacle
