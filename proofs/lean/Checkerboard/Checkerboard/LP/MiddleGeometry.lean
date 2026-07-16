import Checkerboard.LP.MiddleCertificate
import Checkerboard.LP.PrimalParameterBounds
import Checkerboard.LP.ContinuumModel

/-!
# Pointwise geometry of the seven-component middle certificate

This file turns the rational interval table into seven explicit affine curves.
It checks `X+Y+Z=0`, all coordinate ranges, and the folded map into the
continuum triangle.  The later measure module only has to combine these curves
with the exact mixture weights and pushforward-density calculations.
-/

namespace Checkerboard

noncomputable section

open Set

namespace RationalInterval

/-- Midpoint and length of a rational interval. -/
def midpoint (I : RationalInterval) : ℚ := (I.lo + I.hi) / 2

def length (I : RationalInterval) : ℚ := I.hi - I.lo

/-- Affine parametrization by `t ∈ [-1/2,1/2]`, in either orientation. -/
def affineMap (I : RationalInterval) (forward : Bool) (t : ℚ) : ℚ :=
  midpoint I + (if forward then length I else -length I) * t

/-- Either orientation parametrizes the same closed interval. -/
theorem affineMap_mem_Icc
    {I : RationalInterval} {forward : Bool} {t : ℚ}
    (hI : I.lo ≤ I.hi) (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    affineMap I forward t ∈ Set.Icc I.lo I.hi := by
  rcases ht with ⟨htl, htu⟩
  cases forward <;>
    simp [affineMap, midpoint, length] <;>
    constructor <;> linarith

end RationalInterval

/-- Orientation of the `X` coordinate in one middle component. -/
def MiddleComponent.xForward (C : MiddleComponent) : Bool :=
  match C.positiveVariable with
  | .x => true
  | .y => false

/-- Orientation of the `Y` coordinate in one middle component. -/
def MiddleComponent.yForward (C : MiddleComponent) : Bool :=
  match C.positiveVariable with
  | .x => false
  | .y => true

/-- The positive-slope variable is always `X` or `Y`, so `Z` is reversed. -/
def MiddleComponent.zForward (_C : MiddleComponent) : Bool := false

/-- Exact affine coordinates of component `i`. -/
def middleX (i : Fin 7) (t : ℚ) : ℚ :=
  (middleComponents i).xInterval.affineMap (middleComponents i).xForward t

def middleY (i : Fin 7) (t : ℚ) : ℚ :=
  (middleComponents i).yInterval.affineMap (middleComponents i).yForward t

def middleZ (i : Fin 7) (t : ℚ) : ℚ :=
  (middleComponents i).zInterval.affineMap (middleComponents i).zForward t

/-- Every listed interval is correctly ordered. -/
theorem middle_component_intervals_ordered (i : Fin 7) :
    (middleComponents i).xInterval.lo ≤ (middleComponents i).xInterval.hi ∧
    (middleComponents i).yInterval.lo ≤ (middleComponents i).yInterval.hi ∧
    (middleComponents i).zInterval.lo ≤ (middleComponents i).zInterval.hi := by
  fin_cases i <;> norm_num [middleComponents]

/-- The three affine coordinates satisfy the required pointwise plane equation. -/
theorem middle_xyz_sum_zero (i : Fin 7) (t : ℚ) :
    middleX i t + middleY i t + middleZ i t = 0 := by
  fin_cases i <;>
    norm_num [middleX, middleY, middleZ, middleComponents,
      MiddleComponent.xForward, MiddleComponent.yForward,
      MiddleComponent.zForward, RationalInterval.affineMap,
      RationalInterval.midpoint, RationalInterval.length] <;>
    ring

/-- Coordinate-wise membership in the intervals from the certificate table. -/
theorem middleX_mem_component_interval
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    middleX i t ∈ Set.Icc (middleComponents i).xInterval.lo
      (middleComponents i).xInterval.hi := by
  exact RationalInterval.affineMap_mem_Icc
    (middle_component_intervals_ordered i).1 ht

theorem middleY_mem_component_interval
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    middleY i t ∈ Set.Icc (middleComponents i).yInterval.lo
      (middleComponents i).yInterval.hi := by
  exact RationalInterval.affineMap_mem_Icc
    (middle_component_intervals_ordered i).2.1 ht

theorem middleZ_mem_component_interval
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    middleZ i t ∈ Set.Icc (middleComponents i).zInterval.lo
      (middleComponents i).zInterval.hi := by
  exact RationalInterval.affineMap_mem_Icc
    (middle_component_intervals_ordered i).2.2 ht

/-- Global centered-coordinate ranges. -/
theorem middleX_mem_centered
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    middleX i t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2) := by
  have h := middleX_mem_component_interval i ht
  fin_cases i <;> norm_num [middleComponents] at h ⊢ <;> constructor <;> linarith

theorem middleY_mem_centered
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    middleY i t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2) := by
  have h := middleY_mem_component_interval i ht
  fin_cases i <;> norm_num [middleComponents] at h ⊢ <;> constructor <;> linarith

theorem middleZ_mem_centered
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    middleZ i t ∈ Set.Icc (-1 / 4 : ℚ) (1 / 4) := by
  have h := middleZ_mem_component_interval i ht
  fin_cases i <;> norm_num [middleComponents] at h ⊢ <;> constructor <;> linarith

/-- Shifted uniform coordinates before folding. -/
def middleA (i : Fin 7) (t : ℚ) : ℚ := middleX i t + 1 / 2

def middleB (i : Fin 7) (t : ℚ) : ℚ := middleY i t + 1 / 2

/-- The shifted coordinates lie in the unit interval. -/
theorem middleA_mem_unit
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    middleA i t ∈ Set.Icc (0 : ℚ) 1 := by
  have h := middleX_mem_centered i ht
  constructor <;> simp [middleA] <;> linarith

theorem middleB_mem_unit
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    middleB i t ∈ Set.Icc (0 : ℚ) 1 := by
  have h := middleY_mem_centered i ht
  constructor <;> simp [middleB] <;> linarith

/-- The active diagonal coordinate is `1-Z`. -/
theorem middleA_add_middleB
    (i : Fin 7) (t : ℚ) :
    middleA i t + middleB i t = 1 - middleZ i t := by
  have h := middle_xyz_sum_zero i t
  simp [middleA, middleB]
  linarith

/-- Folded real point used by the middle primal block. -/
def middleMappedX (i : Fin 7) (t : ℚ) : ℝ :=
  primalC + middleLength * min (middleA i t : ℝ) (middleB i t : ℝ)

def middleMappedY (i : Fin 7) (t : ℚ) : ℝ :=
  1 - (primalC + middleLength * max (middleA i t : ℝ) (middleB i t : ℝ))

private theorem primalC_pos : 0 < primalC := by
  rw [primalC_reduced]
  have h : 0 < evalAtCheckerboardP (5 / 76 : ℚ) (64 / 19) (-401 / 76) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  simpa [evalAtCheckerboardP, quadraticAt] using h

private theorem primalE_pos : 0 < primalE := by
  rw [primalE_reduced]
  have h : 0 < evalAtCheckerboardP (-33 / 152 : ℚ) (185 / 76) (-401 / 152) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  simpa [evalAtCheckerboardP, quadraticAt] using h

private theorem middle_y_floor_identity :
    1 - primalC - middleLength = outerLength := by
  rw [outerLength_eq_one_sub_primalD]
  simp [middleLength]
  ring

private theorem middle_diag_lower_identity :
    2 * primalC - 1 + middleLength * (3 / 4) = primalE := by
  simp [middleLength, primalD, primalE]
  ring

private theorem middle_diag_upper_identity :
    2 * primalC - 1 + middleLength * (5 / 4) = primalF := by
  simp [middleLength, primalD, primalF]
  ring

/-- Exact pointwise support of every middle component after folding. -/
theorem middleMapped_mem_continuumTriangle
    (i : Fin 7) {t : ℚ} (ht : t ∈ Set.Icc (-1 / 2 : ℚ) (1 / 2)) :
    (middleMappedX i t, middleMappedY i t) ∈ continuumTriangle := by
  have haQ := middleA_mem_unit i ht
  have hbQ := middleB_mem_unit i ht
  have hzQ := middleZ_mem_centered i ht
  have habQ := middleA_add_middleB i t
  let a : ℝ := middleA i t
  let b : ℝ := middleB i t
  have ha0 : 0 ≤ a := by exact_mod_cast haQ.1
  have ha1 : a ≤ 1 := by exact_mod_cast haQ.2
  have hb0 : 0 ≤ b := by exact_mod_cast hbQ.1
  have hb1 : b ≤ 1 := by exact_mod_cast hbQ.2
  have hzlo : (-1 / 4 : ℝ) ≤ (middleZ i t : ℝ) := by exact_mod_cast hzQ.1
  have hzhi : (middleZ i t : ℝ) ≤ 1 / 4 := by exact_mod_cast hzQ.2
  have hab : a + b = 1 - (middleZ i t : ℝ) := by exact_mod_cast habQ
  have hmin0 : 0 ≤ min a b := le_min ha0 hb0
  have hmax1 : max a b ≤ 1 := max_le ha1 hb1
  have hminmax : min a b ≤ max a b := min_le_max a b
  have hM : 0 ≤ middleLength := le_of_lt middleLength_pos
  have hfloor : 0 < 1 - primalC - middleLength := by
    rw [middle_y_floor_identity]
    exact outerLength_pos
  have hy : 0 ≤ middleMappedY i t := by
    dsimp [middleMappedY, a, b] at hmax1 ⊢
    have hprod : middleLength * max (middleA i t : ℝ) (middleB i t : ℝ) ≤
        middleLength * 1 := mul_le_mul_of_nonneg_left hmax1 hM
    nlinarith
  have hsum : middleMappedX i t + middleMappedY i t ≤ 1 := by
    dsimp [middleMappedX, middleMappedY, a, b]
    have hprod : 0 ≤ middleLength * (max (middleA i t : ℝ) (middleB i t : ℝ) -
        min (middleA i t : ℝ) (middleB i t : ℝ)) :=
      mul_nonneg hM (sub_nonneg.mpr hminmax)
    nlinarith
  have hdiag : 0 ≤ middleMappedX i t - middleMappedY i t := by
    have hAB : (3 / 4 : ℝ) ≤ a + b := by nlinarith
    have hdelta : 0 ≤ middleLength * ((a + b) - 3 / 4) :=
      mul_nonneg hM (sub_nonneg.mpr hAB)
    have hminaddmax : min a b + max a b = a + b := min_add_max a b
    dsimp [middleMappedX, middleMappedY, a, b]
    rw [middle_diag_lower_identity] at hdelta
    nlinarith [primalE_pos]
  exact ⟨hy, sub_nonneg.mp hdiag, hsum⟩

/-- Exact diagonal formulas used in the pushforward calculation. -/
theorem middleMapped_diff (i : Fin 7) (t : ℚ) :
    middleMappedX i t - middleMappedY i t =
      2 * primalC - 1 + middleLength *
        ((middleA i t : ℝ) + (middleB i t : ℝ)) := by
  simp [middleMappedX, middleMappedY, min_add_max]
  ring

theorem middleMapped_sum (i : Fin 7) (t : ℚ) :
    middleMappedX i t + middleMappedY i t =
      1 - middleLength * |(middleA i t : ℝ) - (middleB i t : ℝ)| := by
  by_cases h : (middleA i t : ℝ) ≤ (middleB i t : ℝ)
  · simp [middleMappedX, middleMappedY, min_eq_left h, max_eq_right h,
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have h' : (middleB i t : ℝ) ≤ (middleA i t : ℝ) := le_of_not_ge h
    simp [middleMappedX, middleMappedY, min_eq_right h', max_eq_left h',
      abs_of_nonneg (sub_nonneg.mpr h')]
    ring

/-- The inactive diagonal support starts strictly after the outer certificate's
last active endpoint. -/
theorem primalG_lt_one_sub_middleLength :
    primalG < 1 - middleLength := by
  have h : 0 < evalAtCheckerboardP (-33 / 76 : ℚ) (147 / 38) (-401 / 76) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  rw [primalG_reduced, middleLength_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

end

end Checkerboard
