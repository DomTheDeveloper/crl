import Checkerboard.LP.CubicInterval
import Checkerboard.LP.PrimalParameters

/-!
# Reduced cubic-field formulas and strict breakpoint ordering

The raw certificate definitions contain rational functions in `p`. Modulo the
defining cubic they reduce to small coefficient triples. These reductions and
all strict interval-order facts are checked here from the rational isolating
interval, with no decimal arithmetic.
-/

namespace Checkerboard

noncomputable section

/-- The denominator in the published formula for `c` is strictly positive. -/
theorem primal_denominator_pos :
    0 < 71 * checkerboardP ^ 2 - 66 * checkerboardP + 11 := by
  have h : 0 < evalAtCheckerboardP (11 : ℚ) (-66) 71 := by
    apply evalAtCheckerboardP_pos_of_right
    · norm_num
    · norm_num [pUpper]
    · norm_num [quadraticAt, pUpper]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

lemma primal_denominator_ne :
    2 * (71 * checkerboardP ^ 2 - 66 * checkerboardP + 11) ≠ 0 := by
  exact mul_ne_zero (by norm_num) (ne_of_gt primal_denominator_pos)

/-- Reduced representative of `c` in the basis `1,p,p²`. -/
theorem primalC_reduced :
    primalC = 5 / 76 + (64 / 19) * checkerboardP - (401 / 76) * checkerboardP ^ 2 := by
  let c₀ : ℝ := 5 / 76 + (64 / 19) * checkerboardP - (401 / 76) * checkerboardP ^ 2
  have hid :
      (187 * checkerboardP^3 - 211 * checkerboardP^2 + 61 * checkerboardP - 5) -
          c₀ * (2 * (71 * checkerboardP^2 - 66 * checkerboardP + 11)) =
        ((71 * checkerboardP - 35) / 38) * pPoly checkerboardP := by
    dsimp [c₀]
    simp [pPoly]
    ring
  rw [checkerboardP_root] at hid
  simp only [mul_zero] at hid
  unfold primalC
  apply (div_eq_iff primal_denominator_ne).2
  exact sub_eq_zero.mp hid

/-- All remaining unnormalized parameters reduce by linear algebra from `c`. -/
theorem primalD_reduced :
    primalD = 71 / 76 - (45 / 19) * checkerboardP + (401 / 76) * checkerboardP ^ 2 := by
  simp [primalD, primalC_reduced]
  ring

theorem primalE_reduced :
    primalE = -33 / 152 + (185 / 76) * checkerboardP - (401 / 152) * checkerboardP ^ 2 := by
  simp [primalE, primalC_reduced]
  ring

theorem primalF_reduced :
    primalF = 33 / 152 - (33 / 76) * checkerboardP + (401 / 152) * checkerboardP ^ 2 := by
  simp [primalF, primalC_reduced]
  ring

theorem primalG_reduced :
    primalG = 43 / 76 + (71 / 38) * checkerboardP - (401 / 76) * checkerboardP ^ 2 := by
  simp [primalG, primalC_reduced]
  ring

theorem outerLength_reduced :
    outerLength = 5 / 76 + (45 / 19) * checkerboardP - (401 / 76) * checkerboardP ^ 2 := by
  simp [outerLength, primalC_reduced]
  ring

theorem middleLength_reduced :
    middleLength = 33 / 38 - (109 / 19) * checkerboardP + (401 / 38) * checkerboardP ^ 2 := by
  simp [middleLength, primalD_reduced, primalC_reduced]
  ring

/-- Both block scales are strictly positive. -/
theorem outerLength_pos : 0 < outerLength := by
  rw [outerLength_reduced]
  have h : 0 < evalAtCheckerboardP (5 / 76 : ℚ) (45 / 19) (-401 / 76) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

theorem middleLength_pos : 0 < middleLength := by
  rw [middleLength_reduced]
  have h : 0 < evalAtCheckerboardP (33 / 38 : ℚ) (-109 / 19) (401 / 38) := by
    apply evalAtCheckerboardP_pos_of_right
    · norm_num
    · norm_num [pUpper]
    · norm_num [quadraticAt, pUpper]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

lemma outerLength_ne : outerLength ≠ 0 := ne_of_gt outerLength_pos
lemma middleLength_ne : middleLength ≠ 0 := ne_of_gt middleLength_pos

/-- Reduced representatives of the normalized outer parameters. -/
theorem outerR_reduced :
    outerR = 539 / 912 + (487 / 456) * checkerboardP - (1203 / 304) * checkerboardP ^ 2 := by
  let r₀ : ℝ := 539 / 912 + (487 / 456) * checkerboardP - (1203 / 304) * checkerboardP ^ 2
  have hid :
      checkerboardP - r₀ *
          (5 / 76 + (45 / 19) * checkerboardP - (401 / 76) * checkerboardP ^ 2) =
        -((3609 * checkerboardP + 385) / 69312) * pPoly checkerboardP := by
    dsimp [r₀]
    simp [pPoly]
    ring
  rw [checkerboardP_root] at hid
  simp only [mul_zero, neg_zero] at hid
  unfold outerR
  apply (div_eq_iff outerLength_ne).2
  rw [outerLength_reduced]
  exact sub_eq_zero.mp hid

theorem outerQ_reduced :
    outerQ = -713 / 912 + (871 / 152) * checkerboardP - (6817 / 912) * checkerboardP ^ 2 := by
  let q₀ : ℝ := -713 / 912 + (871 / 152) * checkerboardP - (6817 / 912) * checkerboardP ^ 2
  let f₀ : ℝ := 33 / 152 - (33 / 76) * checkerboardP + (401 / 152) * checkerboardP ^ 2
  let l₀ : ℝ := 5 / 76 + (45 / 19) * checkerboardP - (401 / 76) * checkerboardP ^ 2
  have hid :
      (f₀ - checkerboardP) - q₀ * l₀ =
        -((6817 * checkerboardP - 2659) / 69312) * pPoly checkerboardP := by
    dsimp [q₀, f₀, l₀]
    simp [pPoly]
    ring
  rw [checkerboardP_root] at hid
  simp only [mul_zero, neg_zero] at hid
  unfold outerQ
  apply (div_eq_iff outerLength_ne).2
  rw [primalF_reduced, outerLength_reduced]
  exact sub_eq_zero.mp hid

theorem outerH_reduced :
    outerH = -47 / 304 + (4739 / 456) * checkerboardP - (10025 / 912) * checkerboardP ^ 2 := by
  let h₀ : ℝ := -47 / 304 + (4739 / 456) * checkerboardP - (10025 / 912) * checkerboardP ^ 2
  let g₀ : ℝ := 43 / 76 + (71 / 38) * checkerboardP - (401 / 76) * checkerboardP ^ 2
  let l₀ : ℝ := 5 / 76 + (45 / 19) * checkerboardP - (401 / 76) * checkerboardP ^ 2
  have hid :
      (g₀ - checkerboardP) - h₀ * l₀ =
        -((10025 * checkerboardP - 5703) / 69312) * pPoly checkerboardP := by
    dsimp [h₀, g₀, l₀]
    simp [pPoly]
    ring
  rw [checkerboardP_root] at hid
  simp only [mul_zero, neg_zero] at hid
  unfold outerH
  apply (div_eq_iff outerLength_ne).2
  rw [primalG_reduced, outerLength_reduced]
  exact sub_eq_zero.mp hid

/-! ## Exact strict ordering of the eight outer breakpoints -/

private theorem gap0_certificate : 0 < outerQ := by
  rw [outerQ_reduced]
  have h : 0 < evalAtCheckerboardP (-713 / 912 : ℚ) (871 / 152) (-6817 / 912) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

private theorem gap1_certificate : 0 < (1 - outerR) - outerQ := by
  have h : 0 < evalAtCheckerboardP (181 / 152 : ℚ) (-775 / 114) (5213 / 456) := by
    apply evalAtCheckerboardP_pos_of_right
    · norm_num
    · norm_num [pUpper]
    · norm_num [quadraticAt, pUpper]
  rw [outerR_reduced, outerQ_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

private theorem gap2_certificate : 0 < (outerH - 1) - (1 - outerR) := by
  have h : 0 < evalAtCheckerboardP (-713 / 456 : ℚ) (871 / 76) (-6817 / 456) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  rw [outerR_reduced, outerH_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

private theorem gap3_certificate : 0 < outerR - (outerH - 1) := by
  have h : 0 < evalAtCheckerboardP (199 / 114 : ℚ) (-1063 / 114) (401 / 57) := by
    apply evalAtCheckerboardP_pos_of_right
    · norm_num
    · norm_num [pUpper]
    · norm_num [quadraticAt, pUpper]
  rw [outerR_reduced, outerH_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

private theorem gap4_certificate : 0 < (outerH - outerQ) / 2 - outerR := by
  have h : 0 < evalAtCheckerboardP (-253 / 912 : ℚ) (24 / 19) (2005 / 912) := by
    apply evalAtCheckerboardP_pos_of_left
    · norm_num
    · norm_num [pLower]
    · norm_num [quadraticAt, pLower]
  rw [outerR_reduced, outerQ_reduced, outerH_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

private theorem gap6_certificate : 0 < 1 - (outerH + outerQ) / 2 := by
  have h : 0 < evalAtCheckerboardP (1339 / 912 : ℚ) (-919 / 114) (2807 / 304) := by
    apply evalAtCheckerboardP_pos_of_right
    · norm_num
    · norm_num [pUpper]
    · norm_num [quadraticAt, pUpper]
  rw [outerQ_reduced, outerH_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

/-- The exact endpoint list
`0,q,1-r,h-1,r,(h-q)/2,(h+q)/2,1` is strictly increasing. -/
theorem outer_breakpoint_order :
    0 < outerQ ∧
    outerQ < 1 - outerR ∧
    1 - outerR < outerH - 1 ∧
    outerH - 1 < outerR ∧
    outerR < (outerH - outerQ) / 2 ∧
    (outerH - outerQ) / 2 < (outerH + outerQ) / 2 ∧
    (outerH + outerQ) / 2 < 1 := by
  refine ⟨gap0_certificate, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [gap1_certificate]
  · linarith [gap2_certificate]
  · linarith [gap3_certificate]
  · linarith [gap4_certificate]
  · linarith [gap0_certificate]
  · linarith [gap6_certificate]

end

end Checkerboard
