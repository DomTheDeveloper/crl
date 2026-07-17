import Checkerboard.LP.OuterPhysicalCertificate
import Checkerboard.LP.MiddleTwoSegmentFeasible

/-!
# Exact continuum primal certificate

The physical outer and middle blocks are added.  Their paired one-dimensional
pushforwards partition the capacity intervals up to finitely many endpoints.
The resulting measure is feasible and has total mass exactly `checkerboardAlpha`.
-/

namespace Checkerboard

noncomputable section

open MeasureTheory Set Filter

/-- The full explicit continuum primal measure. -/
def checkerboardContinuumPrimal : Measure ContinuumPoint :=
  outerPhysicalMeasure + middleTwoMeasure

/-- Its paired row/column density. -/
def checkerboardContinuumADensity (x : ℝ) : ℝ≥0∞ :=
  intervalDensity checkerboardP primalC 4 x +
    intervalDensity primalD 1 4 x + middleTwoADensity x

/-- Its paired diagonal density. -/
def checkerboardContinuumBDensity (x : ℝ) : ℝ≥0∞ :=
  intervalDensity 0 primalE 4 x +
    intervalDensity primalF primalG 4 x + middleTwoBDensity x

lemma measurable_checkerboardContinuumADensity :
    Measurable checkerboardContinuumADensity := by
  unfold checkerboardContinuumADensity
  fun_prop

lemma measurable_checkerboardContinuumBDensity :
    Measurable checkerboardContinuumBDensity := by
  unfold checkerboardContinuumBDensity
  fun_prop

private theorem four_smul_restrict_eq_withDensity (lo hi : ℝ) :
    4 • volume.restrict (Set.Icc lo hi) =
      volume.withDensity (intervalDensity lo hi 4) := by
  rw [volume_withDensity_intervalDensity]
  norm_num

/-- Exact paired row/column density of the complete primal certificate. -/
theorem pairedAMeasure_checkerboardContinuumPrimal :
    pairedAMeasure checkerboardContinuumPrimal =
      volume.withDensity checkerboardContinuumADensity := by
  unfold checkerboardContinuumPrimal pairedAMeasure
  rw [Measure.map_add _ _ measurable_coordX,
    Measure.map_add _ _ measurable_coordOneSubY]
  have hregroup :
      Measure.map coordX outerPhysicalMeasure + Measure.map coordX middleTwoMeasure +
          (Measure.map coordOneSubY outerPhysicalMeasure +
            Measure.map coordOneSubY middleTwoMeasure) =
        (Measure.map coordX outerPhysicalMeasure +
            Measure.map coordOneSubY outerPhysicalMeasure) +
          (Measure.map coordX middleTwoMeasure +
            Measure.map coordOneSubY middleTwoMeasure) := by
    ac_rfl
  rw [hregroup, ← pairedAMeasure, ← pairedAMeasure,
    pairedAMeasure_outerPhysicalMeasure,
    pairedAMeasure_middleTwoMeasure]
  rw [four_smul_restrict_eq_withDensity,
    four_smul_restrict_eq_withDensity]
  rw [← withDensity_add_left
    (measurable_intervalDensity checkerboardP primalC 4)]
  rw [← withDensity_add_left
    ((measurable_intervalDensity checkerboardP primalC 4).add
      (measurable_intervalDensity primalD 1 4))]
  rfl

/-- Exact paired diagonal density of the complete primal certificate. -/
theorem pairedBMeasure_checkerboardContinuumPrimal :
    pairedBMeasure checkerboardContinuumPrimal =
      volume.withDensity checkerboardContinuumBDensity := by
  unfold checkerboardContinuumPrimal pairedBMeasure
  rw [Measure.map_add _ _ measurable_coordSum,
    Measure.map_add _ _ measurable_coordDiff]
  have hregroup :
      Measure.map coordSum outerPhysicalMeasure + Measure.map coordSum middleTwoMeasure +
          (Measure.map coordDiff outerPhysicalMeasure +
            Measure.map coordDiff middleTwoMeasure) =
        (Measure.map coordSum outerPhysicalMeasure +
            Measure.map coordDiff outerPhysicalMeasure) +
          (Measure.map coordSum middleTwoMeasure +
            Measure.map coordDiff middleTwoMeasure) := by
    ac_rfl
  rw [hregroup, ← pairedBMeasure, ← pairedBMeasure,
    pairedBMeasure_outerPhysicalMeasure,
    pairedBMeasure_middleTwoMeasure]
  rw [four_smul_restrict_eq_withDensity,
    four_smul_restrict_eq_withDensity]
  rw [← withDensity_add_left
    (measurable_intervalDensity 0 primalE 4)]
  rw [← withDensity_add_left
    ((measurable_intervalDensity 0 primalE 4).add
      (measurable_intervalDensity primalF primalG 4))]
  rfl

/-! ## Row/column capacity -/

private theorem checkerboardP_pos : 0 < checkerboardP := by
  have hp := checkerboardP_mem.1
  norm_num [pLower] at hp ⊢
  linarith

private theorem primalC_lt_primalD : primalC < primalD := by
  simpa [middleLength] using middleLength_pos

private theorem primalD_lt_one : primalD < 1 := by
  have h := outerLength_pos
  rw [outerLength_eq_one_sub_primalD] at h
  linarith

private theorem middleTwoADensity_zero_of_lt_c {x : ℝ} (hx : x < primalC) :
    middleTwoADensity x = 0 := by
  have h0 : x ∉ Set.Icc primalC (primalC + middleLength / 2) := by
    rintro ⟨h,_⟩; linarith
  have h1 : x ∉ Set.Icc (primalC + middleLength / 2)
      (primalC + 3 * middleLength / 4) := by
    rintro ⟨h,_⟩
    have hM := middleLength_pos
    linarith
  have h2 : x ∉ Set.Icc (primalC + 3 * middleLength / 4)
      (primalC + middleLength) := by
    rintro ⟨h,_⟩
    have hM := middleLength_pos
    linarith
  simp [middleTwoADensity, intervalDensity, h0, h1, h2]

private theorem middleTwoADensity_zero_of_d_lt {x : ℝ} (hx : primalD < x) :
    middleTwoADensity x = 0 := by
  have hcd : primalC + middleLength = primalD := by
    simp [middleLength]
  have h0 : x ∉ Set.Icc primalC (primalC + middleLength / 2) := by
    rintro ⟨_,h⟩
    have hM := middleLength_pos
    linarith
  have h1 : x ∉ Set.Icc (primalC + middleLength / 2)
      (primalC + 3 * middleLength / 4) := by
    rintro ⟨_,h⟩
    have hM := middleLength_pos
    linarith
  have h2 : x ∉ Set.Icc (primalC + 3 * middleLength / 4)
      (primalC + middleLength) := by
    rintro ⟨_,h⟩
    rw [hcd] at h
    linarith
  simp [middleTwoADensity, intervalDensity, h0, h1, h2]

/-- The complete paired row/column density is bounded by capacity four. -/
theorem checkerboardContinuumADensity_ae_le_capacity :
    checkerboardContinuumADensity ≤ᵐ[volume] intervalDensity 0 1 4 := by
  have hpc : checkerboardP < primalC := by
    simpa [outerLength] using outerLength_pos
  have hcd := primalC_lt_primalD
  have hd1 := primalD_lt_one
  filter_upwards [middleTwoADensity_ae_le_capacity,
    volume.ae_ne checkerboardP, volume.ae_ne primalC,
    volume.ae_ne primalD, volume.ae_ne (1 : ℝ)] with x hmid hxp hxc hxd hx1
  by_cases h0 : x < checkerboardP
  · have hpcI : x ∉ Set.Icc checkerboardP primalC := by
      rintro ⟨h,_⟩; linarith
    have hdI : x ∉ Set.Icc primalD 1 := by
      rintro ⟨h,_⟩; linarith
    have hm0 := middleTwoADensity_zero_of_lt_c (h0.trans hpc)
    by_cases hu : x ∈ Set.Icc (0 : ℝ) 1 <;>
      simp [checkerboardContinuumADensity, intervalDensity, hpcI, hdI, hm0, hu]
  have hpx : checkerboardP < x :=
    lt_of_le_of_ne (not_lt.mp h0) (Ne.symm hxp)
  by_cases h1 : x < primalC
  · have hpI : x ∈ Set.Icc checkerboardP primalC := ⟨hpx.le, h1.le⟩
    have hdI : x ∉ Set.Icc primalD 1 := by
      rintro ⟨h,_⟩; linarith
    have hm0 := middleTwoADensity_zero_of_lt_c h1
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [checkerboardP_pos]
    simp [checkerboardContinuumADensity, intervalDensity, hpI, hdI, hm0, hu]
  have hcx : primalC < x :=
    lt_of_le_of_ne (not_lt.mp h1) (Ne.symm hxc)
  by_cases h2 : x < primalD
  · have hpI : x ∉ Set.Icc checkerboardP primalC := by
      rintro ⟨_,h⟩; linarith
    have hdI : x ∉ Set.Icc primalD 1 := by
      rintro ⟨h,_⟩; linarith
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [checkerboardP_pos]
    simp [checkerboardContinuumADensity, intervalDensity, hpI, hdI, hu]
    simpa [intervalDensity, hu] using hmid
  have hdx : primalD < x :=
    lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hxd)
  by_cases h3 : x < 1
  · have hpI : x ∉ Set.Icc checkerboardP primalC := by
      rintro ⟨_,h⟩; linarith
    have hdI : x ∈ Set.Icc primalD 1 := ⟨hdx.le, h3.le⟩
    have hm0 := middleTwoADensity_zero_of_d_lt hdx
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [checkerboardP_pos]
    simp [checkerboardContinuumADensity, intervalDensity, hpI, hdI, hm0, hu]
  have h1x : 1 < x := lt_of_le_of_ne (not_lt.mp h3) (Ne.symm hx1)
  have hpI : x ∉ Set.Icc checkerboardP primalC := by
    rintro ⟨_,h⟩; linarith
  have hdI : x ∉ Set.Icc primalD 1 := by
    rintro ⟨_,h⟩; linarith
  have hm0 := middleTwoADensity_zero_of_d_lt (hd1.trans h1x)
  have hu : x ∉ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨_,h⟩; linarith
  simp [checkerboardContinuumADensity, intervalDensity, hpI, hdI, hm0, hu]

/-! ## Diagonal capacity -/

private theorem middleTwoBDensity_zero_of_lt_e {x : ℝ} (hx : x < primalE) :
    middleTwoBDensity x = 0 := by
  rcases middleTwo_projection_breakpoint_order with ⟨he0,hef,hfg,hga,ha1⟩
  have h0 : x ∉ Set.Icc primalE middleTwoDiffMid := by
    rintro ⟨h,_⟩; linarith
  have h1 : x ∉ Set.Icc middleTwoDiffMid primalF := by
    rintro ⟨h,_⟩
    have hm : primalE < middleTwoDiffMid := by
      rw [← middleTwo_diff_lower]
      simp [middleTwoDiffMid]
      nlinarith [middleLength_pos]
    linarith
  have h2 : x ∉ Set.Icc (1 - 3 * middleLength / 4) 1 := by
    rintro ⟨h,_⟩
    have hstart : primalE < 1 - 3 * middleLength / 4 := by
      linarith [hfg, hga, middleLength_pos]
    linarith
  have h3 : x ∉ Set.Icc (1 - middleLength) (1 - middleLength / 4) := by
    rintro ⟨h,_⟩
    linarith [hef, hfg, hga]
  simp [middleTwoBDensity, intervalDensity, h0, h1, h2, h3]

private theorem middleTwoBDensity_zero_of_f_lt_of_lt_a
    {x : ℝ} (hfx : primalF < x) (hxa : x < 1 - middleLength) :
    middleTwoBDensity x = 0 := by
  have hmlo : primalE < middleTwoDiffMid := by
    rw [← middleTwo_diff_lower]
    simp [middleTwoDiffMid]
    nlinarith [middleLength_pos]
  have hmhi : middleTwoDiffMid < primalF := by
    rw [← middleTwo_diff_upper]
    simp [middleTwoDiffMid]
    nlinarith [middleLength_pos]
  have h0 : x ∉ Set.Icc primalE middleTwoDiffMid := by
    rintro ⟨_,h⟩; linarith
  have h1 : x ∉ Set.Icc middleTwoDiffMid primalF := by
    rintro ⟨_,h⟩; linarith
  have h2 : x ∉ Set.Icc (1 - 3 * middleLength / 4) 1 := by
    rintro ⟨h,_⟩
    have hM := middleLength_pos
    linarith
  have h3 : x ∉ Set.Icc (1 - middleLength) (1 - middleLength / 4) := by
    rintro ⟨h,_⟩; linarith
  simp [middleTwoBDensity, intervalDensity, h0, h1, h2, h3]

private theorem middleTwoBDensity_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    middleTwoBDensity x = 0 := by
  have h0 : x ∉ Set.Icc primalE middleTwoDiffMid := by
    rintro ⟨_,h⟩
    have hM := middleLength_pos
    rw [← middleTwo_diff_upper] at h
    simp [middleTwoDiffMid] at h
    nlinarith
  have h1 : x ∉ Set.Icc middleTwoDiffMid primalF := by
    rintro ⟨_,h⟩
    have hfg := middleTwo_projection_breakpoint_order.2.2.1
    have hga := middleTwo_projection_breakpoint_order.2.2.2.1
    have ha1 := middleTwo_projection_breakpoint_order.2.2.2.2
    linarith
  have h2 : x ∉ Set.Icc (1 - 3 * middleLength / 4) 1 := by
    rintro ⟨_,h⟩; linarith
  have h3 : x ∉ Set.Icc (1 - middleLength) (1 - middleLength / 4) := by
    rintro ⟨_,h⟩
    have hM := middleLength_pos
    linarith
  simp [middleTwoBDensity, intervalDensity, h0, h1, h2, h3]

/-- The complete paired diagonal density is bounded by capacity four. -/
theorem checkerboardContinuumBDensity_ae_le_capacity :
    checkerboardContinuumBDensity ≤ᵐ[volume] intervalDensity 0 1 4 := by
  rcases middleTwo_projection_breakpoint_order with ⟨he0,hef,hfg,hga,ha1⟩
  let a : ℝ := 1 - middleLength
  filter_upwards [middleTwoBDensity_ae_le_capacity,
    volume.ae_ne (0 : ℝ), volume.ae_ne primalE,
    volume.ae_ne primalF, volume.ae_ne primalG,
    volume.ae_ne a, volume.ae_ne (1 : ℝ)] with x hmid hx0 hxe hxf hxg hxa hx1
  by_cases h0 : x < 0
  · have hE : x ∉ Set.Icc 0 primalE := by rintro ⟨h,_⟩; linarith
    have hG : x ∉ Set.Icc primalF primalG := by rintro ⟨h,_⟩; linarith
    have hm0 := middleTwoBDensity_zero_of_lt_e (h0.trans he0)
    have hu : x ∉ Set.Icc (0 : ℝ) 1 := by rintro ⟨h,_⟩; linarith
    simp [checkerboardContinuumBDensity, intervalDensity, hE, hG, hm0, hu]
  have hx0' : 0 < x := lt_of_le_of_ne (not_lt.mp h0) (Ne.symm hx0)
  by_cases h1 : x < primalE
  · have hE : x ∈ Set.Icc 0 primalE := ⟨hx0'.le,h1.le⟩
    have hG : x ∉ Set.Icc primalF primalG := by rintro ⟨h,_⟩; linarith
    have hm0 := middleTwoBDensity_zero_of_lt_e h1
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    simp [checkerboardContinuumBDensity, intervalDensity, hE, hG, hm0, hu]
  have hex : primalE < x := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm hxe)
  by_cases h2 : x < primalF
  · have hE : x ∉ Set.Icc 0 primalE := by rintro ⟨_,h⟩; linarith
    have hG : x ∉ Set.Icc primalF primalG := by rintro ⟨h,_⟩; linarith
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    simp [checkerboardContinuumBDensity, intervalDensity, hE, hG, hu]
    simpa [intervalDensity, hu] using hmid
  have hfx : primalF < x := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hxf)
  by_cases h3 : x < primalG
  · have hE : x ∉ Set.Icc 0 primalE := by rintro ⟨_,h⟩; linarith
    have hG : x ∈ Set.Icc primalF primalG := ⟨hfx.le,h3.le⟩
    have hm0 := middleTwoBDensity_zero_of_f_lt_of_lt_a hfx (h3.trans hga)
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    simp [checkerboardContinuumBDensity, intervalDensity, hE, hG, hm0, hu]
  have hgx : primalG < x := lt_of_le_of_ne (not_lt.mp h3) (Ne.symm hxg)
  by_cases h4 : x < a
  · have hE : x ∉ Set.Icc 0 primalE := by rintro ⟨_,h⟩; linarith
    have hG : x ∉ Set.Icc primalF primalG := by rintro ⟨_,h⟩; linarith
    have hm0 := middleTwoBDensity_zero_of_f_lt_of_lt_a (hfg.trans hgx) h4
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [a] at h4
      constructor <;> linarith
    simp [checkerboardContinuumBDensity, intervalDensity, hE, hG, hm0, hu]
  have hax : a < x := lt_of_le_of_ne (not_lt.mp h4) (Ne.symm hxa)
  by_cases h5 : x < 1
  · have hE : x ∉ Set.Icc 0 primalE := by rintro ⟨_,h⟩; linarith
    have hG : x ∉ Set.Icc primalF primalG := by rintro ⟨_,h⟩; linarith
    have hu : x ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith
    simp [checkerboardContinuumBDensity, intervalDensity, hE, hG, hu]
    simpa [intervalDensity, hu] using hmid
  have h1x : 1 < x := lt_of_le_of_ne (not_lt.mp h5) (Ne.symm hx1)
  have hE : x ∉ Set.Icc 0 primalE := by rintro ⟨_,h⟩; linarith
  have hG : x ∉ Set.Icc primalF primalG := by rintro ⟨_,h⟩; linarith
  have hm0 := middleTwoBDensity_zero_of_one_lt h1x
  have hu : x ∉ Set.Icc (0 : ℝ) 1 := by rintro ⟨_,h⟩; linarith
  simp [checkerboardContinuumBDensity, intervalDensity, hE, hG, hm0, hu]

/-! ## Feasibility and exact objective -/

theorem pairedAMeasure_checkerboardContinuumPrimal_le :
    pairedAMeasure checkerboardContinuumPrimal ≤ 4 • unitIntervalVolume := by
  rw [pairedAMeasure_checkerboardContinuumPrimal]
  calc
    volume.withDensity checkerboardContinuumADensity ≤
        volume.withDensity (intervalDensity 0 1 4) :=
      withDensity_mono checkerboardContinuumADensity_ae_le_capacity
    _ = 4 • unitIntervalVolume := by
      rw [volume_withDensity_intervalDensity]
      norm_num [unitIntervalVolume]

theorem pairedBMeasure_checkerboardContinuumPrimal_le :
    pairedBMeasure checkerboardContinuumPrimal ≤ 4 • unitIntervalVolume := by
  rw [pairedBMeasure_checkerboardContinuumPrimal]
  calc
    volume.withDensity checkerboardContinuumBDensity ≤
        volume.withDensity (intervalDensity 0 1 4) :=
      withDensity_mono checkerboardContinuumBDensity_ae_le_capacity
    _ = 4 • unitIntervalVolume := by
      rw [volume_withDensity_intervalDensity]
      norm_num [unitIntervalVolume]

theorem checkerboardContinuumPrimal_support :
    ∀ᵐ z ∂checkerboardContinuumPrimal, z ∈ continuumTriangle := by
  rw [mem_ae_iff]
  have ho : outerPhysicalMeasure continuumTriangleᶜ = 0 :=
    mem_ae_iff.mp outerPhysicalMeasure_support
  have hm : middleTwoMeasure continuumTriangleᶜ = 0 :=
    mem_ae_iff.mp middleTwoMeasure_support
  rw [checkerboardContinuumPrimal, Measure.add_apply, ho, hm]
  simp

theorem checkerboardContinuumPrimal_feasible :
    ContinuumPrimalFeasible checkerboardContinuumPrimal :=
  continuumPrimalFeasible_of_paired_le checkerboardContinuumPrimal_support
    pairedAMeasure_checkerboardContinuumPrimal_le
    pairedBMeasure_checkerboardContinuumPrimal_le

theorem checkerboardContinuumPrimal_univ :
    checkerboardContinuumPrimal Set.univ = ENNReal.ofReal checkerboardAlpha := by
  rw [checkerboardContinuumPrimal, Measure.add_apply,
    outerPhysicalMeasure_univ, middleTwoMeasure_univ]
  rw [← ENNReal.ofReal_add
    (by positivity : 0 ≤ 4 * outerLength)
    (by positivity : 0 ≤ 2 * middleLength)]
  congr 1
  linarith [primal_block_mass_identity]

/-- Exact primal objective certificate. -/
theorem checkerboardContinuumPrimal_value :
    continuumPrimalValue checkerboardContinuumPrimal =
      ENNReal.ofReal checkerboardAlpha :=
  checkerboardContinuumPrimal_univ

end

end Checkerboard
