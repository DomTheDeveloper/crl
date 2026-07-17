import Checkerboard.LP.DualHandelmanData
import Checkerboard.LP.DualProfilePositivity
import Checkerboard.LP.ContinuumModel

/-!
# Exact continuum dual feasibility certificate

The generated Handelman module proves nonnegativity of the real obstacle slack
on the whole triangular chamber.  This file lifts that statement to the
`ℝ≥0∞`-valued dual profiles used by `ContinuumDualFeasible`.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter

/-- The exact real obstacle sum is at least one throughout the chamber. -/
theorem certifiedDual_real_obstacle_ge_one
    (z : ContinuumPoint) (hz : z ∈ continuumTriangle) :
    1 ≤ certifiedDualAReal (coordX z) +
      certifiedDualAReal (coordOneSubY z) +
      certifiedDualBReal (coordSum z) +
      certifiedDualBReal (coordDiff z) := by
  have hslack := certifiedDualSlackXY_nonneg z hz
  unfold certifiedDualSlackXY coordX coordOneSubY coordSum coordDiff at hslack ⊢
  linarith

/-- The extended-real obstacle inequality follows without any subtraction or
finiteness assumption because all four profile values are nonnegative. -/
theorem certifiedDual_obstacle
    (z : ContinuumPoint) (hz : z ∈ continuumTriangle) :
    1 ≤ pairedObstacle certifiedDualA certifiedDualB z := by
  have hAx : 0 ≤ certifiedDualAReal (coordX z) :=
    certifiedDualAReal_nonneg _
  have hAy : 0 ≤ certifiedDualAReal (coordOneSubY z) :=
    certifiedDualAReal_nonneg _
  have hBs : 0 ≤ certifiedDualBReal (coordSum z) :=
    certifiedDualBReal_nonneg _
  have hBd : 0 ≤ certifiedDualBReal (coordDiff z) :=
    certifiedDualBReal_nonneg _
  have hreal := certifiedDual_real_obstacle_ge_one z hz
  unfold pairedObstacle certifiedDualA certifiedDualB
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by norm_num
    _ ≤ ENNReal.ofReal
        (certifiedDualAReal (coordX z) +
          certifiedDualAReal (coordOneSubY z) +
          certifiedDualBReal (coordSum z) +
          certifiedDualBReal (coordDiff z)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (certifiedDualAReal (coordX z)) +
        ENNReal.ofReal (certifiedDualAReal (coordOneSubY z)) +
        ENNReal.ofReal (certifiedDualBReal (coordSum z)) +
        ENNReal.ofReal (certifiedDualBReal (coordDiff z)) := by
      rw [ENNReal.ofReal_add (add_nonneg hAx hAy) hBs,
        ENNReal.ofReal_add hAx hAy,
        ENNReal.ofReal_add (add_nonneg (add_nonneg hAx hAy) hBs) hBd]

/-- The reconstructed exact profiles form a feasible continuum dual pair. -/
theorem certifiedDual_feasible :
    ContinuumDualFeasible certifiedDualA certifiedDualB :=
  ⟨measurable_certifiedDualA, measurable_certifiedDualB,
    certifiedDual_obstacle⟩

end

end Checkerboard
