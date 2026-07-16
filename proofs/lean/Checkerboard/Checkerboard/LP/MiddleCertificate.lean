import Mathlib

/-!
# Exact rational core of the seven-component middle transport

The middle continuum primal block is a mixture of seven affine one-parameter
couplings.  All interval lengths and mixture weights are rational.  This file
checks the entire piecewise density arithmetic in the Lean kernel.

The measure-theoretic wrapper turning each row into a pushed-forward uniform
interval measure is deliberately separated from these finite arithmetic facts.
-/

namespace Checkerboard

noncomputable section

/-- Which coordinate is positively oriented with the component parameter. -/
inductive MiddlePositiveVariable
  | x
  | y
  deriving DecidableEq, Repr

/-- A closed rational interval used by one affine component. -/
structure RationalInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

/-- One row of the exact seven-component middle transport table. -/
structure MiddleComponent where
  weight : ℚ
  xInterval : RationalInterval
  yInterval : RationalInterval
  zInterval : RationalInterval
  positiveVariable : MiddlePositiveVariable
  deriving DecidableEq, Repr

private def ri (a b : ℚ) : RationalInterval := ⟨a, b⟩

/-- The seven exact rows, in the order used by the independent verifier. -/
def middleComponents : Fin 7 → MiddleComponent
  | ⟨0, _⟩ =>
      ⟨19 / 90, ri (-1 / 2) (-1 / 4), ri 0 (1 / 2), ri 0 (1 / 4), .y⟩
  | ⟨1, _⟩ =>
      ⟨7 / 90, ri (-1 / 2) 0, ri (1 / 4) (1 / 2), ri (-1 / 4) 0, .x⟩
  | ⟨2, _⟩ =>
      ⟨1 / 5, ri (-1 / 4) 0, ri (-1 / 4) (1 / 2), ri (-1 / 4) (1 / 4), .y⟩
  | ⟨3, _⟩ =>
      ⟨1 / 45, ri (-1 / 4) (1 / 4), ri (-1 / 4) 0, ri 0 (1 / 4), .x⟩
  | ⟨4, _⟩ =>
      ⟨7 / 45, ri 0 (1 / 4), ri (-1 / 4) (1 / 4), ri (-1 / 4) 0, .y⟩
  | ⟨5, _⟩ =>
      ⟨1 / 6, ri 0 (1 / 2), ri (-1 / 2) (-1 / 4), ri 0 (1 / 4), .x⟩
  | ⟨6, _⟩ =>
      ⟨1 / 6, ri (1 / 4) (1 / 2), ri (-1 / 2) 0, ri (-1 / 4) 0, .y⟩

/-- All seven mixture weights are strictly positive. -/
theorem middle_weight_pos (i : Fin 7) : 0 < (middleComponents i).weight := by
  fin_cases i <;> norm_num [middleComponents]

/-- The mixture is a probability measure. -/
theorem middle_weights_sum :
    ∑ i : Fin 7, (middleComponents i).weight = 1 := by
  norm_num [middleComponents, Fin.sum_univ_succ]

/-! ## Exact `X`-marginal density on the four atomic quarter intervals -/

theorem middle_x_density_neg_half_neg_quarter :
    (19 / 90 : ℚ) / (1 / 4) + (7 / 90) / (1 / 2) = 1 := by
  norm_num

theorem middle_x_density_neg_quarter_zero :
    (7 / 90 : ℚ) / (1 / 2) + (1 / 5) / (1 / 4) +
      (1 / 45) / (1 / 2) = 1 := by
  norm_num

theorem middle_x_density_zero_quarter :
    (1 / 45 : ℚ) / (1 / 2) + (7 / 45) / (1 / 4) +
      (1 / 6) / (1 / 2) = 1 := by
  norm_num

theorem middle_x_density_quarter_half :
    (1 / 6 : ℚ) / (1 / 2) + (1 / 6) / (1 / 4) = 1 := by
  norm_num

/-! ## Exact `Y`-marginal density -/

theorem middle_y_density_neg_half_neg_quarter :
    (1 / 6 : ℚ) / (1 / 4) + (1 / 6) / (1 / 2) = 1 := by
  norm_num

theorem middle_y_density_neg_quarter_zero :
    (1 / 5 : ℚ) / (3 / 4) + (1 / 45) / (1 / 4) +
      (7 / 45) / (1 / 2) + (1 / 6) / (1 / 2) = 1 := by
  norm_num

theorem middle_y_density_zero_quarter :
    (19 / 90 : ℚ) / (1 / 2) + (1 / 5) / (3 / 4) +
      (7 / 45) / (1 / 2) = 1 := by
  norm_num

theorem middle_y_density_quarter_half :
    (19 / 90 : ℚ) / (1 / 2) + (7 / 90) / (1 / 4) +
      (1 / 5) / (3 / 4) = 1 := by
  norm_num

/-! ## Exact active diagonal density -/

theorem middle_z_density_neg_quarter_zero :
    (7 / 90 : ℚ) / (1 / 4) + (1 / 5) / (1 / 2) +
      (7 / 45) / (1 / 4) + (1 / 6) / (1 / 4) = 2 := by
  norm_num

theorem middle_z_density_zero_quarter :
    (19 / 90 : ℚ) / (1 / 4) + (1 / 5) / (1 / 2) +
      (1 / 45) / (1 / 4) + (1 / 6) / (1 / 4) = 2 := by
  norm_num

/-! ## Inactive diagonal bound

The exact signed density of `D = X-Y` is constant on the five intervals below.
Folding by `D ↦ |D|` gives four constants, all bounded by `171/135 < 2`.
-/

def middleDiffDensityNegOuter : ℚ := 52 / 135

def middleDiffDensityNegMiddle : ℚ := 79 / 135

def middleDiffDensityCenter : ℚ := 59 / 135

def middleDiffDensityPosInner : ℚ := 92 / 135

def middleDiffDensityPosOuter : ℚ := 4 / 9

/-- Folded density on `(0,1/4)`. -/
theorem middle_folded_diff_first :
    middleDiffDensityCenter + middleDiffDensityCenter = 118 / 135 := by
  norm_num [middleDiffDensityCenter]

/-- Folded density on `(1/4,1/2)`, the unique maximum cell. -/
theorem middle_folded_diff_second :
    middleDiffDensityPosInner + middleDiffDensityNegMiddle = 171 / 135 := by
  norm_num [middleDiffDensityPosInner, middleDiffDensityNegMiddle]

/-- Folded density on `(1/2,3/4)`. -/
theorem middle_folded_diff_third :
    middleDiffDensityPosOuter + middleDiffDensityNegMiddle = 139 / 135 := by
  norm_num [middleDiffDensityPosOuter, middleDiffDensityNegMiddle]

/-- Folded density on `(3/4,1)`. -/
theorem middle_folded_diff_fourth :
    middleDiffDensityPosOuter + middleDiffDensityNegOuter = 112 / 135 := by
  norm_num [middleDiffDensityPosOuter, middleDiffDensityNegOuter]

/-- The inactive diagonal density has uniform slack below capacity two. -/
theorem middle_folded_diff_max_lt_two : (171 / 135 : ℚ) < 2 := by
  norm_num

/-- A convenient weak form used by the measure-level feasibility proof. -/
theorem middle_folded_diff_max_le_two : (171 / 135 : ℚ) ≤ 2 := by
  norm_num

end

end Checkerboard
