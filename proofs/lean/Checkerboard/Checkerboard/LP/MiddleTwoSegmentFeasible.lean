import Checkerboard.LP.MiddleTwoSegment
import Checkerboard.LP.ContinuumProjection

/-!
# Feasibility and mass of the two-segment middle block

This module completes the measure-level verification of the linear contact
certificate.  Endpoint overlaps are discarded as Lebesgue-null sets.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter

/-- The total row/column density of the two-segment block. -/
def middleTwoADensity (x : ℝ) : ℝ≥0∞ :=
  intervalDensity primalC (primalC + middleLength / 2) 2 x +
  intervalDensity primalC (primalC + middleLength / 2) 2 x +
  intervalDensity (primalC + middleLength / 2)
    (primalC + 3 * middleLength / 4) 4 x +
  intervalDensity (primalC + 3 * middleLength / 4)
    (primalC + middleLength) 4 x

/-- The total sum/difference density of the two-segment block. -/
def middleTwoBDensity (x : ℝ) : ℝ≥0∞ :=
  intervalDensity primalE middleTwoDiffMid 4 x +
  intervalDensity middleTwoDiffMid primalF 4 x +
  intervalDensity (1 - 3 * middleLength / 4) 1 (4 / 3) x +
  intervalDensity (1 - middleLength) (1 - middleLength / 4) (4 / 3) x

lemma measurable_middleTwoADensity : Measurable middleTwoADensity := by
  unfold middleTwoADensity
  fun_prop

lemma measurable_middleTwoBDensity : Measurable middleTwoBDensity := by
  unfold middleTwoBDensity
  fun_prop

/-- The paired pushforwards have the displayed densities. -/
theorem pairedAMeasure_middleTwoMeasure :
    pairedAMeasure middleTwoMeasure = volume.withDensity middleTwoADensity := by
  rw [pairedAMeasure, middleTwoMeasure_coordX,
    middleTwoMeasure_coordOneSubY]
  rw [← withDensity_add_left
    (by fun_prop : Measurable (fun x : ℝ =>
      intervalDensity primalC (primalC + middleLength / 2) 2 x +
      intervalDensity primalC (primalC + middleLength / 2) 2 x))]
  rfl

theorem pairedBMeasure_middleTwoMeasure :
    pairedBMeasure middleTwoMeasure = volume.withDensity middleTwoBDensity := by
  rw [pairedBMeasure, middleTwoMeasure_coordSum, middleTwoMeasure_coordDiff]
  rw [add_comm]
  rw [← withDensity_add_left
    (by fun_prop : Measurable (fun x : ℝ =>
      intervalDensity primalE middleTwoDiffMid 4 x +
      intervalDensity middleTwoDiffMid primalF 4 x))]
  rfl

private theorem primalC_pos_middleTwo : 0 < primalC := by
  rw [primalC_reduced]
  have h : 0 < evalAtCheckerboardP (5 / 76 : ℚ) (64 / 19) (-401 / 76) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  simpa [evalAtCheckerboardP, quadraticAt] using h

private theorem primalD_lt_one_middleTwo : primalD < 1 := by
  have h := outerLength_pos
  rw [outerLength_eq_one_sub_primalD] at h
  linarith

private theorem primalF_lt_primalG_middleTwo : primalF < primalG := by
  have h : 0 < evalAtCheckerboardP (53 / 152 : ℚ) (175 / 76) (-1203 / 152) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  rw [primalF_reduced, primalG_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

private theorem primalF_lt_one_sub_middleLength :
    primalF < 1 - middleLength :=
  primalF_lt_primalG_middleTwo.trans primalG_lt_one_sub_middleLength

private theorem one_sub_middleLength_pos : 0 < 1 - middleLength := by
  have hc := primalC_pos_middleTwo
  have hL := outerLength_pos
  have hid : 1 - middleLength = outerLength + primalC := by
    rw [outerLength_eq_one_sub_primalD]
    simp [middleLength]
    ring
  rw [hid]
  positivity

private theorem middleTwo_breakpoint_order :
    primalC < primalC + middleLength / 2 ∧
    primalC + middleLength / 2 < primalC + 3 * middleLength / 4 ∧
    primalC + 3 * middleLength / 4 < primalC + middleLength := by
  have hM := middleLength_pos
  constructor <;> nlinarith

/-- Almost everywhere, the row/column density is at most capacity four. -/
theorem middleTwoADensity_ae_le_capacity :
    middleTwoADensity ≤ᵐ[volume] intervalDensity 0 1 4 := by
  let b1 : ℝ := primalC + middleLength / 2
  let b2 : ℝ := primalC + 3 * middleLength / 4
  let d : ℝ := primalC + middleLength
  have hcd : d = primalD := by
    dsimp [d]
    simp [middleLength]
    ring
  have hc0 : 0 < primalC := primalC_pos_middleTwo
  have hd1 : d < 1 := by rw [hcd]; exact primalD_lt_one_middleTwo
  rcases middleTwo_breakpoint_order with ⟨hcb1,hb1b2,hb2d⟩
  dsimp [b1, b2, d] at hcb1 hb1b2 hb2d ⊢
  filter_upwards [volume.ae_ne primalC,
    volume.ae_ne (primalC + middleLength / 2),
    volume.ae_ne (primalC + 3 * middleLength / 4),
    volume.ae_ne (primalC + middleLength)] with x hxc hxb1 hxb2 hxd
  by_cases h0 : x < primalC
  · have hI0 : x ∉ Set.Icc primalC (primalC + middleLength / 2) := by
      rintro ⟨hx,_⟩; linarith
    have hI1 : x ∉ Set.Icc (primalC + middleLength / 2)
        (primalC + 3 * middleLength / 4) := by
      rintro ⟨hx,_⟩; linarith
    have hI2 : x ∉ Set.Icc (primalC + 3 * middleLength / 4)
        (primalC + middleLength) := by
      rintro ⟨hx,_⟩; linarith
    by_cases hu : x ∈ Set.Icc (0 : ℝ) 1 <;>
      simp [middleTwoADensity, intervalDensity, hI0, hI1, hI2, hu]
  have hcx : primalC < x := lt_of_le_of_ne (not_lt.mp h0) (Ne.symm hxc)
  by_cases h1 : x < primalC + middleLength / 2
  · have hI0 : x ∈ Set.Icc primalC (primalC + middleLength / 2) :=
      ⟨hcx.le, h1.le⟩
    have hI1 : x ∉ Set.Icc (primalC + middleLength / 2)
        (primalC + 3 * middleLength / 4) := by
      rintro ⟨hx,_⟩; linarith
    have hI2 : x ∉ Set.Icc (primalC + 3 * middleLength / 4)
        (primalC + middleLength) := by
      rintro ⟨hx,_⟩; linarith
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    simp [middleTwoADensity, intervalDensity, hI0, hI1, hI2, hu]
  have hb1x : primalC + middleLength / 2 < x :=
    lt_of_le_of_ne (not_lt.mp h1) (Ne.symm hxb1)
  by_cases h2 : x < primalC + 3 * middleLength / 4
  · have hI0 : x ∉ Set.Icc primalC (primalC + middleLength / 2) := by
      rintro ⟨_,hx⟩; linarith
    have hI1 : x ∈ Set.Icc (primalC + middleLength / 2)
        (primalC + 3 * middleLength / 4) := ⟨hb1x.le, h2.le⟩
    have hI2 : x ∉ Set.Icc (primalC + 3 * middleLength / 4)
        (primalC + middleLength) := by
      rintro ⟨hx,_⟩; linarith
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    simp [middleTwoADensity, intervalDensity, hI0, hI1, hI2, hu]
  have hb2x : primalC + 3 * middleLength / 4 < x :=
    lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hxb2)
  by_cases h3 : x < primalC + middleLength
  · have hI0 : x ∉ Set.Icc primalC (primalC + middleLength / 2) := by
      rintro ⟨_,hx⟩; linarith
    have hI1 : x ∉ Set.Icc (primalC + middleLength / 2)
        (primalC + 3 * middleLength / 4) := by
      rintro ⟨_,hx⟩; linarith
    have hI2 : x ∈ Set.Icc (primalC + 3 * middleLength / 4)
        (primalC + middleLength) := ⟨hb2x.le, h3.le⟩
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    simp [middleTwoADensity, intervalDensity, hI0, hI1, hI2, hu]
  have hdx : primalC + middleLength < x :=
    lt_of_le_of_ne (not_lt.mp h3) (Ne.symm hxd)
  have hI0 : x ∉ Set.Icc primalC (primalC + middleLength / 2) := by
    rintro ⟨_,hx⟩; linarith
  have hI1 : x ∉ Set.Icc (primalC + middleLength / 2)
      (primalC + 3 * middleLength / 4) := by
    rintro ⟨_,hx⟩; linarith
  have hI2 : x ∉ Set.Icc (primalC + 3 * middleLength / 4)
      (primalC + middleLength) := by
    rintro ⟨_,hx⟩; linarith
  by_cases hu : x ∈ Set.Icc (0 : ℝ) 1 <;>
    simp [middleTwoADensity, intervalDensity, hI0, hI1, hI2, hu]

private theorem intervalDensity_le_ofReal
    (lo hi c x : ℝ) : intervalDensity lo hi c x ≤ ENNReal.ofReal c := by
  by_cases hx : x ∈ Set.Icc lo hi <;> simp [intervalDensity, hx]

/-- Almost everywhere, the sum/difference density is at most capacity four. -/
theorem middleTwoBDensity_ae_le_capacity :
    middleTwoBDensity ≤ᵐ[volume] intervalDensity 0 1 4 := by
  let a : ℝ := 1 - middleLength
  have ha0 : 0 < a := by
    dsimp [a]
    exact one_sub_middleLength_pos
  have hfa : primalF < a := by
    dsimp [a]
    exact primalF_lt_one_sub_middleLength
  have hmid : primalE < middleTwoDiffMid ∧ middleTwoDiffMid < primalF := by
    constructor
    · have hM := middleLength_pos
      rw [← middleTwo_diff_lower]
      simp [middleTwoDiffMid]
      nlinarith
    · have hM := middleLength_pos
      rw [← middleTwo_diff_upper]
      simp [middleTwoDiffMid]
      nlinarith
  filter_upwards [volume.ae_ne middleTwoDiffMid, volume.ae_ne a] with x hxmid hxa
  have hdiff :
      intervalDensity primalE middleTwoDiffMid 4 x +
        intervalDensity middleTwoDiffMid primalF 4 x ≤ 4 := by
    by_cases h : x < middleTwoDiffMid
    · have hsecond : x ∉ Set.Icc middleTwoDiffMid primalF := by
        rintro ⟨hx,_⟩; linarith
      have hfirst := intervalDensity_le_ofReal primalE middleTwoDiffMid 4 x
      simp [intervalDensity, hsecond] at hfirst ⊢
      exact hfirst
    · have hmx : middleTwoDiffMid < x :=
        lt_of_le_of_ne (not_lt.mp h) (Ne.symm hxmid)
      have hfirstmem : x ∉ Set.Icc primalE middleTwoDiffMid := by
        rintro ⟨_,hx⟩; linarith
      have hsecond := intervalDensity_le_ofReal middleTwoDiffMid primalF 4 x
      simp [intervalDensity, hfirstmem] at hsecond ⊢
      exact hsecond
  have hsum :
      intervalDensity (1 - 3 * middleLength / 4) 1 (4 / 3) x +
        intervalDensity (1 - middleLength) (1 - middleLength / 4) (4 / 3) x ≤ 4 := by
    have h0 := intervalDensity_le_ofReal
      (1 - 3 * middleLength / 4) 1 (4 / 3) x
    have h1 := intervalDensity_le_ofReal
      (1 - middleLength) (1 - middleLength / 4) (4 / 3) x
    have hsum' := add_le_add h0 h1
    norm_num at hsum' ⊢
    exact hsum'.trans (by norm_num)
  by_cases hleft : x < a
  · have hS0 : x ∉ Set.Icc (1 - 3 * middleLength / 4) 1 := by
      rintro ⟨hx,_⟩
      dsimp [a] at hleft
      have hM := middleLength_pos
      nlinarith
    have hS1 : x ∉ Set.Icc (1 - middleLength) (1 - middleLength / 4) := by
      rintro ⟨hx,_⟩
      dsimp [a] at hleft
      linarith
    by_cases hu : x ∈ Set.Icc (0 : ℝ) 1
    · simp [middleTwoBDensity, intervalDensity, hS0, hS1, hu]
      exact hdiff
    · have hxneg : x < 0 := by
        rcases not_and_or.mp hu with h | h
        · exact lt_of_not_ge h
        · exfalso
          have hx1 : 1 < x := lt_of_not_ge h
          dsimp [a] at hleft
          have hM := middleLength_pos
          linarith
      have hD0 : x ∉ Set.Icc primalE middleTwoDiffMid := by
        rintro ⟨hx,_⟩
        linarith [primalE_pos_twoSegment]
      have hD1 : x ∉ Set.Icc middleTwoDiffMid primalF := by
        rintro ⟨hx,_⟩
        linarith [hmid.1, primalE_pos_twoSegment]
      simp [middleTwoBDensity, intervalDensity, hD0, hD1, hS0, hS1, hu]
  · have hax : a < x := lt_of_le_of_ne (not_lt.mp hleft) (Ne.symm hxa)
    have hD0 : x ∉ Set.Icc primalE middleTwoDiffMid := by
      rintro ⟨_,hx⟩
      linarith [hmid.2, hfa]
    have hD1 : x ∉ Set.Icc middleTwoDiffMid primalF := by
      rintro ⟨_,hx⟩
      linarith [hfa]
    by_cases hu : x ∈ Set.Icc (0 : ℝ) 1
    · simp [middleTwoBDensity, intervalDensity, hD0, hD1, hu]
      exact hsum
    · have hxone : 1 < x := by
        rcases not_and_or.mp hu with h | h
        · exfalso
          have hx0 : x < 0 := lt_of_not_ge h
          linarith [ha0]
        · exact lt_of_not_ge h
      have hS0 : x ∉ Set.Icc (1 - 3 * middleLength / 4) 1 := by
        rintro ⟨_,hx⟩; linarith
      have hS1 : x ∉ Set.Icc (1 - middleLength) (1 - middleLength / 4) := by
        rintro ⟨_,hx⟩
        have hM := middleLength_pos
        linarith
      simp [middleTwoBDensity, intervalDensity, hD0, hD1, hS0, hS1, hu]

/-- Both paired projection measures obey the continuum capacity constraints. -/
theorem pairedAMeasure_middleTwoMeasure_le :
    pairedAMeasure middleTwoMeasure ≤ 4 • unitIntervalVolume := by
  rw [pairedAMeasure_middleTwoMeasure]
  calc
    volume.withDensity middleTwoADensity ≤
        volume.withDensity (intervalDensity 0 1 4) :=
      withDensity_mono middleTwoADensity_ae_le_capacity
    _ = 4 • unitIntervalVolume := by
      rw [volume_withDensity_intervalDensity]
      norm_num [unitIntervalVolume]

theorem pairedBMeasure_middleTwoMeasure_le :
    pairedBMeasure middleTwoMeasure ≤ 4 • unitIntervalVolume := by
  rw [pairedBMeasure_middleTwoMeasure]
  calc
    volume.withDensity middleTwoBDensity ≤
        volume.withDensity (intervalDensity 0 1 4) :=
      withDensity_mono middleTwoBDensity_ae_le_capacity
    _ = 4 • unitIntervalVolume := by
      rw [volume_withDensity_intervalDensity]
      norm_num [unitIntervalVolume]

/-- The two physical components are supported in the continuum triangle. -/
theorem middleTwoComponent0_compl_zero :
    middleTwoComponent0 continuumTriangleᶜ = 0 := by
  rw [middleTwoComponent0, Measure.smul_apply]
  rw [Measure.map_apply measurable_middleTwoPoint0 measurableSet_continuumTriangle.compl]
  have hmeas : MeasurableSet (middleTwoPoint0 ⁻¹' continuumTriangleᶜ) :=
    measurableSet_continuumTriangle.compl.preimage measurable_middleTwoPoint0
  rw [centeredUnitIntervalMeasure, Measure.restrict_apply hmeas]
  have hset :
      middleTwoPoint0 ⁻¹' continuumTriangleᶜ ∩
        Set.Icc (-1 / 2 : ℝ) (1 / 2) = ∅ := by
    ext t
    constructor
    · rintro ⟨htc,ht⟩
      exact (htc (middleTwoPoint0_mem ht)).elim
    · simp
  rw [hset]
  simp

theorem middleTwoComponent1_compl_zero :
    middleTwoComponent1 continuumTriangleᶜ = 0 := by
  rw [middleTwoComponent1, Measure.smul_apply]
  rw [Measure.map_apply measurable_middleTwoPoint1 measurableSet_continuumTriangle.compl]
  have hmeas : MeasurableSet (middleTwoPoint1 ⁻¹' continuumTriangleᶜ) :=
    measurableSet_continuumTriangle.compl.preimage measurable_middleTwoPoint1
  rw [centeredUnitIntervalMeasure, Measure.restrict_apply hmeas]
  have hset :
      middleTwoPoint1 ⁻¹' continuumTriangleᶜ ∩
        Set.Icc (-1 / 2 : ℝ) (1 / 2) = ∅ := by
    ext t
    constructor
    · rintro ⟨htc,ht⟩
      exact (htc (middleTwoPoint1_mem ht)).elim
    · simp
  rw [hset]
  simp

theorem middleTwoMeasure_support :
    ∀ᵐ z ∂middleTwoMeasure, z ∈ continuumTriangle := by
  rw [show (∀ᵐ z ∂middleTwoMeasure, z ∈ continuumTriangle) ↔
      middleTwoMeasure continuumTriangleᶜ = 0 by
        exact mem_ae_iff]
  rw [middleTwoMeasure, Measure.add_apply,
    middleTwoComponent0_compl_zero, middleTwoComponent1_compl_zero]
  simp

/-- Exact mass of the middle block. -/
theorem middleTwoComponent0_univ :
    middleTwoComponent0 Set.univ = ENNReal.ofReal middleLength := by
  simp [middleTwoComponent0, centeredUnitIntervalMeasure_univ,
    measurable_middleTwoPoint0]

theorem middleTwoComponent1_univ :
    middleTwoComponent1 Set.univ = ENNReal.ofReal middleLength := by
  simp [middleTwoComponent1, centeredUnitIntervalMeasure_univ,
    measurable_middleTwoPoint1]

theorem middleTwoMeasure_univ :
    middleTwoMeasure Set.univ = ENNReal.ofReal (2 * middleLength) := by
  rw [middleTwoMeasure, Measure.add_apply,
    middleTwoComponent0_univ, middleTwoComponent1_univ]
  rw [← ENNReal.ofReal_add (le_of_lt middleLength_pos)
    (le_of_lt middleLength_pos)]
  congr 1
  ring

/-- The middle block is a concrete continuum primal-feasible measure. -/
theorem middleTwoMeasure_feasible : ContinuumPrimalFeasible middleTwoMeasure :=
  continuumPrimalFeasible_of_paired_le middleTwoMeasure_support
    pairedAMeasure_middleTwoMeasure_le pairedBMeasure_middleTwoMeasure_le

end

end Checkerboard
