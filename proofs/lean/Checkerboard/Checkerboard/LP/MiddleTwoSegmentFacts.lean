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

end

end Checkerboard
