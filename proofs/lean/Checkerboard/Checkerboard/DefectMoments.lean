import Mathlib
import Checkerboard.MasterAlgebra

/-!
# Defect-moment inequalities

This file closes the analytic part of the finite all-`n` argument.  The
remaining geometric layer must supply the exact first- and second-moment
identities for the row, column, and diagonal deficit functions.
-/

namespace Checkerboard

noncomputable section

open scoped BigOperators

/-- Weighted Cauchy for a nonnegative defect function of total mass three. -/
theorem defect_cauchy_mass_three {ι : Type*} [Fintype ι]
    (defect coordinate : ι → ℝ)
    (hdefect : ∀ i, 0 ≤ defect i)
    (hmass : ∑ i, defect i = 3) :
    (∑ i, defect i * coordinate i)^2 ≤
      3 * ∑ i, defect i * coordinate i ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset ι)
    (r := fun i => defect i * coordinate i)
    (f := defect)
    (g := fun i => defect i * coordinate i ^ 2)
    (fun i _ => hdefect i)
    (fun i _ => mul_nonneg (hdefect i) (sq_nonneg (coordinate i)))
    (fun i _ => by ring_nf; positivity)
  simpa [hmass, mul_assoc, mul_left_comm, mul_comm] using h

/-- Applying weighted Cauchy separately to column and row deficits. -/
theorem two_defect_cauchy_mass_three
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (columnDefect columnCoordinate : ι → ℝ)
    (rowDefect rowCoordinate : κ → ℝ)
    (hc : ∀ i, 0 ≤ columnDefect i)
    (hr : ∀ j, 0 ≤ rowDefect j)
    (hcmass : ∑ i, columnDefect i = 3)
    (hrmass : ∑ j, rowDefect j = 3) :
    (∑ i, columnDefect i * columnCoordinate i)^2 +
        (∑ j, rowDefect j * rowCoordinate j)^2 ≤
      3 * ((∑ i, columnDefect i * columnCoordinate i ^ 2) +
        ∑ j, rowDefect j * rowCoordinate j ^ 2) := by
  have hcolumn := defect_cauchy_mass_three
    columnDefect columnCoordinate hc hcmass
  have hrow := defect_cauchy_mass_three rowDefect rowCoordinate hr hrmass
  linarith

/-- Algebraic closure of the `q=1` master-moment argument.

`C₁,R₁` are the first moments of the column and row deficits, while `C₂,R₂`
are their second moments. `a,b` are the unique missing diagonal offsets.
-/
theorem q1_master_lower_bound
    {a b C₁ R₁ C₂ R₂ K : ℝ}
    (hC₁ : C₁ = (a + b) / 2)
    (hR₁ : R₁ = (a - b) / 2)
    (hcauchy : C₁ ^ 2 + R₁ ^ 2 ≤ 3 * (C₂ + R₂))
    (hmaster : C₂ + R₂ = K + (a ^ 2 + b ^ 2) / 2) :
    -3 * K ≤ a ^ 2 + b ^ 2 := by
  rw [hC₁, hR₁] at hcauchy
  nlinarith [sumDiffSquares a b]

/-- Convenient end-to-end form using explicit finite deficit functions. -/
theorem q1_lower_bound_of_defects
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (columnDefect columnCoordinate : ι → ℝ)
    (rowDefect rowCoordinate : κ → ℝ)
    {a b K : ℝ}
    (hc : ∀ i, 0 ≤ columnDefect i)
    (hr : ∀ j, 0 ≤ rowDefect j)
    (hcmass : ∑ i, columnDefect i = 3)
    (hrmass : ∑ j, rowDefect j = 3)
    (hfirstColumn :
      ∑ i, columnDefect i * columnCoordinate i = (a + b) / 2)
    (hfirstRow :
      ∑ j, rowDefect j * rowCoordinate j = (a - b) / 2)
    (hmaster :
      (∑ i, columnDefect i * columnCoordinate i ^ 2) +
          ∑ j, rowDefect j * rowCoordinate j ^ 2 =
        K + (a ^ 2 + b ^ 2) / 2) :
    -3 * K ≤ a ^ 2 + b ^ 2 := by
  apply q1_master_lower_bound hfirstColumn hfirstRow
  · exact two_defect_cauchy_mass_three
      columnDefect columnCoordinate rowDefect rowCoordinate
      hc hr hcmass hrmass
  · exact hmaster

end

end Checkerboard
