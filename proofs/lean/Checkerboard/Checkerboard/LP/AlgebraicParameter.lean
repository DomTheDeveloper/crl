import Checkerboard.CubicTransform

/-!
# The isolated checkerboard cubic parameter

This file defines the exact real parameter used by the four-direction LP theorem.
It proves existence and uniqueness of the root in the published rational isolating
interval, then defines `checkerboardAlpha = 2 * (1 - checkerboardP)`.
-/

namespace Checkerboard

noncomputable section

/-- Lower endpoint of the exact rational isolating interval for `p`. -/
def pLower : ℝ := 2115883 / 10000000

/-- Upper endpoint of the exact rational isolating interval for `p`. -/
def pUpper : ℝ := 2115884 / 10000000

lemma pLower_lt_pUpper : pLower < pUpper := by
  norm_num [pLower, pUpper]

lemma pPoly_pLower_pos : 0 < pPoly pLower := by
  norm_num [pPoly, pLower]

lemma pPoly_pUpper_neg : pPoly pUpper < 0 := by
  norm_num [pPoly, pUpper]

lemma continuous_pPoly : Continuous pPoly := by
  unfold pPoly
  fun_prop

/-- The defining cubic has a root in the exact rational isolating interval. -/
theorem exists_p_root_in_isolating_interval :
    ∃ p ∈ Set.Icc pLower pUpper, pPoly p = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (pPoly pUpper) (pPoly pLower) :=
    ⟨le_of_lt pPoly_pUpper_neg, le_of_lt pPoly_pLower_pos⟩
  have himage : (0 : ℝ) ∈ pPoly '' Set.Icc pLower pUpper :=
    (intermediate_value_Icc' pLower_lt_pUpper.le continuous_pPoly.continuousOn) hzero
  rcases himage with ⟨p, hp, hp0⟩
  exact ⟨p, hp, hp0⟩

private lemma pLower_coarse : (21 / 100 : ℝ) ≤ pLower := by
  norm_num [pLower]

private lemma pUpper_coarse : pUpper ≤ (11 / 50 : ℝ) := by
  norm_num [pUpper]

/-- The root in the isolating interval is unique. -/
theorem p_root_unique_in_isolating_interval {x y : ℝ}
    (hxI : x ∈ Set.Icc pLower pUpper)
    (hyI : y ∈ Set.Icc pLower pUpper)
    (hx : pPoly x = 0) (hy : pPoly y = 0) : x = y := by
  have hxl : (21 / 100 : ℝ) ≤ x := pLower_coarse.trans hxI.1
  have hyl : (21 / 100 : ℝ) ≤ y := pLower_coarse.trans hyI.1
  have hxu : x ≤ (11 / 50 : ℝ) := hxI.2.trans pUpper_coarse
  have hyu : y ≤ (11 / 50 : ℝ) := hyI.2.trans pUpper_coarse
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hx_sq : x ^ 2 ≤ (11 / 50 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxu) (add_nonneg (by norm_num) hx0)]
  have hy_sq : y ^ 2 ≤ (11 / 50 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyu) (add_nonneg (by norm_num) hy0)]
  have hxy₁ : x * y ≤ (11 / 50 : ℝ) * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxu) hy0]
  have hxy₂ : (11 / 50 : ℝ) * y ≤ (11 / 50 : ℝ) ^ 2 := by
    nlinarith
  have hxy : x * y ≤ (11 / 50 : ℝ) ^ 2 := hxy₁.trans hxy₂
  let bracket : ℝ := 401 * (x ^ 2 + x * y + y ^ 2) - 331 * (x + y) + 19
  have hbracket : bracket < 0 := by
    dsimp [bracket]
    nlinarith [hx_sq, hy_sq, hxy]
  have hfactor : (x - y) * bracket = 0 := by
    have hid : pPoly x - pPoly y = (x - y) * bracket := by
      dsimp [bracket]
      simp [pPoly]
      ring
    rw [← hid, hx, hy]
    ring
  rcases mul_eq_zero.mp hfactor with hxy0 | hbr0
  · exact sub_eq_zero.mp hxy0
  · exact False.elim ((ne_of_lt hbracket) hbr0)

/-- The exact middle root used in the checkerboard certificates. -/
def checkerboardP : ℝ := Classical.choose exists_p_root_in_isolating_interval

lemma checkerboardP_mem : checkerboardP ∈ Set.Icc pLower pUpper :=
  (Classical.choose_spec exists_p_root_in_isolating_interval).1

lemma checkerboardP_root : pPoly checkerboardP = 0 :=
  (Classical.choose_spec exists_p_root_in_isolating_interval).2

/-- Characterization of `checkerboardP` by the cubic and isolating interval. -/
theorem eq_checkerboardP_of_root_in_interval {p : ℝ}
    (hpI : p ∈ Set.Icc pLower pUpper) (hp : pPoly p = 0) :
    p = checkerboardP :=
  p_root_unique_in_isolating_interval hpI checkerboardP_mem hp checkerboardP_root

/-- The exact asymptotic constant for the four-direction relaxation. -/
def checkerboardAlpha : ℝ := 2 * (1 - checkerboardP)

lemma checkerboardAlpha_root : alphaPoly checkerboardAlpha = 0 := by
  exact pRoot_gives_alphaRoot checkerboardP_root

lemma checkerboardAlpha_pos : 0 < checkerboardAlpha := by
  have hp : checkerboardP < 1 := checkerboardP_mem.2.trans_lt (by norm_num [pUpper])
  simp [checkerboardAlpha]
  linarith

lemma checkerboardAlpha_lt_two : checkerboardAlpha < 2 := by
  have hp : 0 < checkerboardP :=
    (by norm_num [pLower] : 0 < pLower).trans_le checkerboardP_mem.1
  simp [checkerboardAlpha]
  linarith

end

end Checkerboard
