import Checkerboard.LP.PrimalParameterBounds

/-!
# Public algebraic facts for the two-segment middle block

These facts are kept separate from the geometric construction so later
measure-level modules can use them without relying on private declarations.
-/

namespace Checkerboard

noncomputable section

/-- The active middle difference interval starts strictly to the right of zero. -/
theorem primalE_pos_twoSegment : 0 < primalE := by
  rw [primalE_reduced]
  have h : 0 < evalAtCheckerboardP (-33 / 152 : ℚ) (185 / 76) (-401 / 152) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  simpa [evalAtCheckerboardP, quadraticAt] using h

/-- Lower endpoint identity for the active difference projection. -/
theorem middleTwo_diff_lower :
    2 * primalC - 1 + middleLength * (3 / 4) = primalE := by
  simp [middleLength, primalD, primalE]
  ring

/-- Upper endpoint identity for the active difference projection. -/
theorem middleTwo_diff_upper :
    2 * primalC - 1 + middleLength * (5 / 4) = primalF := by
  simp [middleLength, primalD, primalF]
  ring

/-- The bottom of the middle physical strip is the outer length. -/
theorem middleTwo_y_floor :
    1 - primalC - middleLength = outerLength := by
  rw [outerLength_eq_one_sub_primalD]
  simp [middleLength]
  ring

/-- The active middle difference interval has positive length. -/
theorem primalE_lt_primalF_twoSegment : primalE < primalF := by
  have hM := middleLength_pos
  rw [← middleTwo_diff_lower, ← middleTwo_diff_upper]
  nlinarith

/-- The active difference interval ends before the outer upper band ends. -/
theorem primalF_lt_primalG_twoSegment : primalF < primalG := by
  have h : 0 < evalAtCheckerboardP (53 / 152 : ℚ) (175 / 76) (-1203 / 152) := by
    apply evalAtCheckerboardP_pos_of_concave
    · norm_num
    · norm_num [quadraticAt, pLower]
    · norm_num [quadraticAt, pUpper]
  rw [primalF_reduced, primalG_reduced]
  convert h using 1 <;> simp [evalAtCheckerboardP, quadraticAt] <;> ring

/-- The inactive middle sum band begins strictly after all active outer bands. -/
theorem primalG_lt_one_sub_middleLength_twoSegment :
    primalG < 1 - middleLength :=
  primalG_lt_one_sub_middleLength

/-- The inactive middle band starts inside the unit interval. -/
theorem zero_lt_one_sub_middleLength_twoSegment : 0 < 1 - middleLength := by
  have hc : 0 < primalC := by
    rw [primalC_reduced]
    have h : 0 < evalAtCheckerboardP (5 / 76 : ℚ) (64 / 19) (-401 / 76) := by
      apply evalAtCheckerboardP_pos_of_concave
      · norm_num
      · norm_num [quadraticAt, pLower]
      · norm_num [quadraticAt, pUpper]
    simpa [evalAtCheckerboardP, quadraticAt] using h
  rw [show 1 - middleLength = outerLength + primalC by
    rw [outerLength_eq_one_sub_primalD]
    simp [middleLength]
    ring]
  positivity

/-- The inactive middle band starts below one. -/
theorem one_sub_middleLength_lt_one_twoSegment : 1 - middleLength < 1 := by
  linarith [middleLength_pos]

/-- Complete strict ordering used in the combined primal density proof. -/
theorem middleTwo_projection_breakpoint_order :
    0 < primalE ∧ primalE < primalF ∧ primalF < primalG ∧
      primalG < 1 - middleLength ∧ 1 - middleLength < 1 :=
  ⟨primalE_pos_twoSegment, primalE_lt_primalF_twoSegment,
    primalF_lt_primalG_twoSegment,
    primalG_lt_one_sub_middleLength_twoSegment,
    one_sub_middleLength_lt_one_twoSegment⟩

end

end Checkerboard
