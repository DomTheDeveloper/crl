import Checkerboard.LP.IntervalDensityMeasure
import Checkerboard.LP.PrimalParameterBounds
import Checkerboard.LP.ContinuumModel

/-!
# Exact two-segment middle primal block

The linear contact region admits a considerably smaller certificate than the
seven-row folded table.  In normalized coordinates `X,Y`, use the two segments

* `(0,3/4) → (1/2,1/2)`;
* `(0,1)   → (1/2,3/4)`.

Each carries half of the normalized mass.  After the physical transformation

`x = c + M X`, `1-y = c + M Y`,

and multiplication by total mass `2M`, the paired row/column projection has
exact density four on `[c,d]`, the active difference projection has exact
density four on `[e,f]`, and the inactive sum projection has density at most
`8/3 < 4`.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter

/-- Normalized `X` coordinate shared by the two segments. -/
def middleTwoX (t : ℝ) : ℝ := t / 2 + 1 / 4

/-- Normalized `Y` coordinate of the lower segment. -/
def middleTwoY0 (t : ℝ) : ℝ := 5 / 8 - t / 4

/-- Normalized `Y` coordinate of the upper segment. -/
def middleTwoY1 (t : ℝ) : ℝ := 7 / 8 - t / 4

/-- The two physical affine curves in the continuum triangle. -/
def middleTwoPoint0 (t : ℝ) : ContinuumPoint :=
  (primalC + middleLength * middleTwoX t,
    1 - (primalC + middleLength * middleTwoY0 t))

def middleTwoPoint1 (t : ℝ) : ContinuumPoint :=
  (primalC + middleLength * middleTwoX t,
    1 - (primalC + middleLength * middleTwoY1 t))

lemma measurable_middleTwoPoint0 : Measurable middleTwoPoint0 := by
  unfold middleTwoPoint0 middleTwoX middleTwoY0
  fun_prop

lemma measurable_middleTwoPoint1 : Measurable middleTwoPoint1 := by
  unfold middleTwoPoint1 middleTwoX middleTwoY1
  fun_prop

private theorem primalE_pos_twoSegment : 0 < primalE := by
  rw [primalE_reduced]
  have h : 0 < evalAtCheckerboardP (-33 / 152 : ℚ) (185 / 76) (-401 / 152) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  simpa [evalAtCheckerboardP, quadraticAt] using h

private theorem middleTwo_y_floor :
    1 - primalC - middleLength = outerLength := by
  rw [outerLength_eq_one_sub_primalD]
  simp [middleLength]
  ring

private theorem middleTwo_diff_lower :
    2 * primalC - 1 + middleLength * (3 / 4) = primalE := by
  simp [middleLength, primalD, primalE]
  ring

private theorem middleTwo_diff_upper :
    2 * primalC - 1 + middleLength * (5 / 4) = primalF := by
  simp [middleLength, primalD, primalF]
  ring

/-- Generic support criterion for the physical middle transformation. -/
theorem middleTwo_physical_mem_triangle
    {X Y : ℝ}
    (hY : Y ≤ 1) (hXY : X ≤ Y) (hdiag : 3 / 4 ≤ X + Y) :
    (primalC + middleLength * X,
      1 - (primalC + middleLength * Y)) ∈ continuumTriangle := by
  have hM : 0 ≤ middleLength := le_of_lt middleLength_pos
  have hyfloor : 0 < 1 - primalC - middleLength := by
    rw [middleTwo_y_floor]
    exact outerLength_pos
  have hy : 0 ≤ 1 - (primalC + middleLength * Y) := by
    have hmul := mul_le_mul_of_nonneg_left hY hM
    nlinarith
  have hdiagmul : 0 ≤ middleLength * (X + Y - 3 / 4) :=
    mul_nonneg hM (sub_nonneg.mpr hdiag)
  have horder :
      1 - (primalC + middleLength * Y) ≤
        primalC + middleLength * X := by
    have he := middleTwo_diff_lower
    nlinarith [primalE_pos_twoSegment]
  have hsum :
      primalC + middleLength * X +
        (1 - (primalC + middleLength * Y)) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hXY hM
    nlinarith
  exact ⟨hy, horder, hsum⟩

lemma middleTwo_normalized0
    {t : ℝ} (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    middleTwoY0 t ≤ 1 ∧ middleTwoX t ≤ middleTwoY0 t ∧
      3 / 4 ≤ middleTwoX t + middleTwoY0 t := by
  rcases ht with ⟨htl, htu⟩
  simp [middleTwoX, middleTwoY0]
  constructor
  · linarith
  constructor <;> linarith

lemma middleTwo_normalized1
    {t : ℝ} (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    middleTwoY1 t ≤ 1 ∧ middleTwoX t ≤ middleTwoY1 t ∧
      3 / 4 ≤ middleTwoX t + middleTwoY1 t := by
  rcases ht with ⟨htl, htu⟩
  simp [middleTwoX, middleTwoY1]
  constructor
  · linarith
  constructor <;> linarith

/-- Pointwise support of both affine curves. -/
theorem middleTwoPoint0_mem
    {t : ℝ} (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    middleTwoPoint0 t ∈ continuumTriangle := by
  rcases middleTwo_normalized0 ht with ⟨hY, hXY, hdiag⟩
  exact middleTwo_physical_mem_triangle hY hXY hdiag

theorem middleTwoPoint1_mem
    {t : ℝ} (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    middleTwoPoint1 t ∈ continuumTriangle := by
  rcases middleTwo_normalized1 ht with ⟨hY, hXY, hdiag⟩
  exact middleTwo_physical_mem_triangle hY hXY hdiag

/-- Each physical component has mass `M`; together they have mass `2M`. -/
def middleTwoComponent0 : Measure ContinuumPoint :=
  ENNReal.ofReal middleLength •
    Measure.map middleTwoPoint0 centeredUnitIntervalMeasure

def middleTwoComponent1 : Measure ContinuumPoint :=
  ENNReal.ofReal middleLength •
    Measure.map middleTwoPoint1 centeredUnitIntervalMeasure

def middleTwoMeasure : Measure ContinuumPoint :=
  middleTwoComponent0 + middleTwoComponent1

private theorem middleTwo_half_pos : 0 < middleLength / 2 := by positivity
private theorem middleTwo_quarter_pos : 0 < middleLength / 4 := by positivity
private theorem middleTwo_threeQuarter_pos : 0 < 3 * middleLength / 4 := by positivity

/-! ## Exact component pushforwards -/

theorem middleTwoComponent0_coordX :
    Measure.map coordX middleTwoComponent0 =
      volume.withDensity
        (intervalDensity primalC (primalC + middleLength / 2) 2) := by
  rw [middleTwoComponent0, Measure.map_smul]
  rw [Measure.map_map measurable_middleTwoPoint0 measurable_coordX]
  change ENNReal.ofReal middleLength •
      Measure.map (fun t : ℝ => primalC + middleLength * (t / 2 + 1 / 4))
        centeredUnitIntervalMeasure = _
  have hfun :
      (fun t : ℝ => primalC + middleLength * (t / 2 + 1 / 4)) =
        (fun t : ℝ => (primalC + middleLength / 4) +
          (middleLength / 2) * t) := by
    funext t
    ring
  rw [hfun]
  have h := weighted_map_centered_interval_affine
    (w := middleLength) (m := primalC + middleLength / 4)
    (s := middleLength / 2) (le_of_lt middleLength_pos) middleTwo_half_pos
  have hlo :
      primalC + middleLength / 4 - (middleLength / 2) / 2 = primalC := by ring
  have hhi :
      primalC + middleLength / 4 + (middleLength / 2) / 2 =
        primalC + middleLength / 2 := by ring
  have hratio : middleLength / (middleLength / 2) = 2 := by
    field_simp [middleLength_ne]
  rw [hlo, hhi, hratio] at h
  exact h

theorem middleTwoComponent1_coordX :
    Measure.map coordX middleTwoComponent1 =
      volume.withDensity
        (intervalDensity primalC (primalC + middleLength / 2) 2) := by
  rw [middleTwoComponent1, Measure.map_smul]
  rw [Measure.map_map measurable_middleTwoPoint1 measurable_coordX]
  change ENNReal.ofReal middleLength •
      Measure.map (fun t : ℝ => primalC + middleLength * (t / 2 + 1 / 4))
        centeredUnitIntervalMeasure = _
  simpa only using middleTwoComponent0_coordX

theorem middleTwoComponent0_coordOneSubY :
    Measure.map coordOneSubY middleTwoComponent0 =
      volume.withDensity (intervalDensity
        (primalC + middleLength / 2)
        (primalC + 3 * middleLength / 4) 4) := by
  rw [middleTwoComponent0, Measure.map_smul]
  rw [Measure.map_map measurable_middleTwoPoint0 measurable_coordOneSubY]
  change ENNReal.ofReal middleLength •
      Measure.map (fun t : ℝ => primalC + middleLength * (5 / 8 - t / 4))
        centeredUnitIntervalMeasure = _
  have hfun :
      (fun t : ℝ => primalC + middleLength * (5 / 8 - t / 4)) =
        (fun t : ℝ => (primalC + 5 * middleLength / 8) -
          (middleLength / 4) * t) := by
    funext t
    ring
  rw [hfun]
  have h := weighted_map_centered_interval_affine_neg
    (w := middleLength) (m := primalC + 5 * middleLength / 8)
    (s := middleLength / 4) (le_of_lt middleLength_pos) middleTwo_quarter_pos
  have hlo :
      primalC + 5 * middleLength / 8 - (middleLength / 4) / 2 =
        primalC + middleLength / 2 := by ring
  have hhi :
      primalC + 5 * middleLength / 8 + (middleLength / 4) / 2 =
        primalC + 3 * middleLength / 4 := by ring
  have hratio : middleLength / (middleLength / 4) = 4 := by
    field_simp [middleLength_ne]
  rw [hlo, hhi, hratio] at h
  exact h

theorem middleTwoComponent1_coordOneSubY :
    Measure.map coordOneSubY middleTwoComponent1 =
      volume.withDensity (intervalDensity
        (primalC + 3 * middleLength / 4)
        (primalC + middleLength) 4) := by
  rw [middleTwoComponent1, Measure.map_smul]
  rw [Measure.map_map measurable_middleTwoPoint1 measurable_coordOneSubY]
  change ENNReal.ofReal middleLength •
      Measure.map (fun t : ℝ => primalC + middleLength * (7 / 8 - t / 4))
        centeredUnitIntervalMeasure = _
  have hfun :
      (fun t : ℝ => primalC + middleLength * (7 / 8 - t / 4)) =
        (fun t : ℝ => (primalC + 7 * middleLength / 8) -
          (middleLength / 4) * t) := by
    funext t
    ring
  rw [hfun]
  have h := weighted_map_centered_interval_affine_neg
    (w := middleLength) (m := primalC + 7 * middleLength / 8)
    (s := middleLength / 4) (le_of_lt middleLength_pos) middleTwo_quarter_pos
  have hlo :
      primalC + 7 * middleLength / 8 - (middleLength / 4) / 2 =
        primalC + 3 * middleLength / 4 := by ring
  have hhi :
      primalC + 7 * middleLength / 8 + (middleLength / 4) / 2 =
        primalC + middleLength := by ring
  have hratio : middleLength / (middleLength / 4) = 4 := by
    field_simp [middleLength_ne]
  rw [hlo, hhi, hratio] at h
  exact h

/-- The midpoint of the active difference interval. -/
def middleTwoDiffMid : ℝ := 2 * primalC - 1 + middleLength

theorem middleTwoComponent0_coordDiff :
    Measure.map coordDiff middleTwoComponent0 =
      volume.withDensity
        (intervalDensity primalE middleTwoDiffMid 4) := by
  rw [middleTwoComponent0, Measure.map_smul]
  rw [Measure.map_map measurable_middleTwoPoint0 measurable_coordDiff]
  change ENNReal.ofReal middleLength •
      Measure.map (fun t : ℝ =>
        2 * primalC - 1 + middleLength * (7 / 8 + t / 4))
        centeredUnitIntervalMeasure = _
  have hfun :
      (fun t : ℝ => 2 * primalC - 1 + middleLength * (7 / 8 + t / 4)) =
        (fun t : ℝ => (2 * primalC - 1 + 7 * middleLength / 8) +
          (middleLength / 4) * t) := by
    funext t
    ring
  rw [hfun]
  have h := weighted_map_centered_interval_affine
    (w := middleLength) (m := 2 * primalC - 1 + 7 * middleLength / 8)
    (s := middleLength / 4) (le_of_lt middleLength_pos) middleTwo_quarter_pos
  have hlo :
      2 * primalC - 1 + 7 * middleLength / 8 - (middleLength / 4) / 2 =
        primalE := by
    rw [← middleTwo_diff_lower]
    ring
  have hhi :
      2 * primalC - 1 + 7 * middleLength / 8 + (middleLength / 4) / 2 =
        middleTwoDiffMid := by
    simp [middleTwoDiffMid]
    ring
  have hratio : middleLength / (middleLength / 4) = 4 := by
    field_simp [middleLength_ne]
  rw [hlo, hhi, hratio] at h
  exact h

theorem middleTwoComponent1_coordDiff :
    Measure.map coordDiff middleTwoComponent1 =
      volume.withDensity
        (intervalDensity middleTwoDiffMid primalF 4) := by
  rw [middleTwoComponent1, Measure.map_smul]
  rw [Measure.map_map measurable_middleTwoPoint1 measurable_coordDiff]
  change ENNReal.ofReal middleLength •
      Measure.map (fun t : ℝ =>
        2 * primalC - 1 + middleLength * (9 / 8 + t / 4))
        centeredUnitIntervalMeasure = _
  have hfun :
      (fun t : ℝ => 2 * primalC - 1 + middleLength * (9 / 8 + t / 4)) =
        (fun t : ℝ => (2 * primalC - 1 + 9 * middleLength / 8) +
          (middleLength / 4) * t) := by
    funext t
    ring
  rw [hfun]
  have h := weighted_map_centered_interval_affine
    (w := middleLength) (m := 2 * primalC - 1 + 9 * middleLength / 8)
    (s := middleLength / 4) (le_of_lt middleLength_pos) middleTwo_quarter_pos
  have hlo :
      2 * primalC - 1 + 9 * middleLength / 8 - (middleLength / 4) / 2 =
        middleTwoDiffMid := by
    simp [middleTwoDiffMid]
    ring
  have hhi :
      2 * primalC - 1 + 9 * middleLength / 8 + (middleLength / 4) / 2 =
        primalF := by
    rw [← middleTwo_diff_upper]
    ring
  have hratio : middleLength / (middleLength / 4) = 4 := by
    field_simp [middleLength_ne]
  rw [hlo, hhi, hratio] at h
  exact h

theorem middleTwoComponent0_coordSum :
    Measure.map coordSum middleTwoComponent0 =
      volume.withDensity (intervalDensity
        (1 - 3 * middleLength / 4) 1 (4 / 3)) := by
  rw [middleTwoComponent0, Measure.map_smul]
  rw [Measure.map_map measurable_middleTwoPoint0 measurable_coordSum]
  change ENNReal.ofReal middleLength •
      Measure.map (fun t : ℝ => 1 + middleLength * (-3 / 8 + 3 * t / 4))
        centeredUnitIntervalMeasure = _
  have hfun :
      (fun t : ℝ => 1 + middleLength * (-3 / 8 + 3 * t / 4)) =
        (fun t : ℝ => (1 - 3 * middleLength / 8) +
          (3 * middleLength / 4) * t) := by
    funext t
    ring
  rw [hfun]
  have h := weighted_map_centered_interval_affine
    (w := middleLength) (m := 1 - 3 * middleLength / 8)
    (s := 3 * middleLength / 4) (le_of_lt middleLength_pos)
      middleTwo_threeQuarter_pos
  have hlo :
      1 - 3 * middleLength / 8 - (3 * middleLength / 4) / 2 =
        1 - 3 * middleLength / 4 := by ring
  have hhi :
      1 - 3 * middleLength / 8 + (3 * middleLength / 4) / 2 = 1 := by ring
  have hratio : middleLength / (3 * middleLength / 4) = 4 / 3 := by
    field_simp [middleLength_ne]
  rw [hlo, hhi, hratio] at h
  exact h

theorem middleTwoComponent1_coordSum :
    Measure.map coordSum middleTwoComponent1 =
      volume.withDensity (intervalDensity
        (1 - middleLength) (1 - middleLength / 4) (4 / 3)) := by
  rw [middleTwoComponent1, Measure.map_smul]
  rw [Measure.map_map measurable_middleTwoPoint1 measurable_coordSum]
  change ENNReal.ofReal middleLength •
      Measure.map (fun t : ℝ => 1 + middleLength * (-5 / 8 + 3 * t / 4))
        centeredUnitIntervalMeasure = _
  have hfun :
      (fun t : ℝ => 1 + middleLength * (-5 / 8 + 3 * t / 4)) =
        (fun t : ℝ => (1 - 5 * middleLength / 8) +
          (3 * middleLength / 4) * t) := by
    funext t
    ring
  rw [hfun]
  have h := weighted_map_centered_interval_affine
    (w := middleLength) (m := 1 - 5 * middleLength / 8)
    (s := 3 * middleLength / 4) (le_of_lt middleLength_pos)
      middleTwo_threeQuarter_pos
  have hlo :
      1 - 5 * middleLength / 8 - (3 * middleLength / 4) / 2 =
        1 - middleLength := by ring
  have hhi :
      1 - 5 * middleLength / 8 + (3 * middleLength / 4) / 2 =
        1 - middleLength / 4 := by ring
  have hratio : middleLength / (3 * middleLength / 4) = 4 / 3 := by
    field_simp [middleLength_ne]
  rw [hlo, hhi, hratio] at h
  exact h

/-! ## Combined component maps -/

theorem middleTwoMeasure_coordX :
    Measure.map coordX middleTwoMeasure =
      volume.withDensity (fun x =>
        intervalDensity primalC (primalC + middleLength / 2) 2 x +
        intervalDensity primalC (primalC + middleLength / 2) 2 x) := by
  rw [middleTwoMeasure, Measure.map_add _ _ measurable_coordX,
    middleTwoComponent0_coordX, middleTwoComponent1_coordX]
  symm
  exact withDensity_add_left
    (measurable_intervalDensity _ _ _) _

theorem middleTwoMeasure_coordOneSubY :
    Measure.map coordOneSubY middleTwoMeasure =
      volume.withDensity (fun x =>
        intervalDensity (primalC + middleLength / 2)
          (primalC + 3 * middleLength / 4) 4 x +
        intervalDensity (primalC + 3 * middleLength / 4)
          (primalC + middleLength) 4 x) := by
  rw [middleTwoMeasure, Measure.map_add _ _ measurable_coordOneSubY,
    middleTwoComponent0_coordOneSubY, middleTwoComponent1_coordOneSubY]
  symm
  exact withDensity_add_left
    (measurable_intervalDensity _ _ _) _

theorem middleTwoMeasure_coordDiff :
    Measure.map coordDiff middleTwoMeasure =
      volume.withDensity (fun x =>
        intervalDensity primalE middleTwoDiffMid 4 x +
        intervalDensity middleTwoDiffMid primalF 4 x) := by
  rw [middleTwoMeasure, Measure.map_add _ _ measurable_coordDiff,
    middleTwoComponent0_coordDiff, middleTwoComponent1_coordDiff]
  symm
  exact withDensity_add_left
    (measurable_intervalDensity _ _ _) _

theorem middleTwoMeasure_coordSum :
    Measure.map coordSum middleTwoMeasure =
      volume.withDensity (fun x =>
        intervalDensity (1 - 3 * middleLength / 4) 1 (4 / 3) x +
        intervalDensity (1 - middleLength) (1 - middleLength / 4) (4 / 3) x) := by
  rw [middleTwoMeasure, Measure.map_add _ _ measurable_coordSum,
    middleTwoComponent0_coordSum, middleTwoComponent1_coordSum]
  symm
  exact withDensity_add_left
    (measurable_intervalDensity _ _ _) _

end

end Checkerboard
