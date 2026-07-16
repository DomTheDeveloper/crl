import Checkerboard.LP.FiniteModel

/-!
# Exact finite duality inequality for the four-direction LP

A dual certificate assigns a nonnegative weight to every retained line and
covers every parity point by total incident weight at least one.  The objective
has coefficient two because each primal line has capacity two.
-/

namespace Checkerboard

noncomputable section

/-- Total dual weight covering a parity point. -/
def coverWeight {n ε : ℕ} (w : FourLine n → ℝ) (p : ParityPoint n ε) : ℝ :=
  ∑ l : FourLine n, if FourLine.Incident p.1 l then w l else 0

/-- Feasibility of a finite four-direction dual certificate. -/
def DualFeasible {n ε : ℕ} (w : FourLine n → ℝ) : Prop :=
  (∀ l, 0 ≤ w l) ∧ (∀ p, 1 ≤ coverWeight w p)

/-- Objective of a finite dual certificate. -/
def dualObjective {n : ℕ} (w : FourLine n → ℝ) : ℝ :=
  2 * ∑ l, w l

/-- Exact finite double-counting identity. -/
theorem weighted_cover_sum_eq_line_sum {n ε : ℕ}
    (x : ParityPoint n ε → ℝ) (w : FourLine n → ℝ) :
    (∑ p, x p * coverWeight w p) =
      ∑ l, w l * lineLoad x l := by
  classical
  unfold coverWeight lineLoad
  simp_rw [Finset.mul_sum]
  rw [Fintype.sum_comm]
  apply Fintype.sum_congr
  intro l
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro p
  by_cases h : FourLine.Incident p.1 l
  · simp [h]
    ring
  · simp [h]

/-- Every primal feasible value is bounded by every dual feasible value. -/
theorem finite_weak_duality {n ε : ℕ}
    {x : ParityPoint n ε → ℝ} {w : FourLine n → ℝ}
    (hx : FractionalFeasible x) (hw : DualFeasible w) :
    fractionalObjective x ≤ dualObjective w := by
  calc
    fractionalObjective x = ∑ p, x p := rfl
    _ ≤ ∑ p, x p * coverWeight w p := by
      exact Fintype.sum_le_sum fun p =>
        (le_mul_of_one_le_right (hx.1 p) (hw.2 p))
    _ = ∑ l, w l * lineLoad x l := weighted_cover_sum_eq_line_sum x w
    _ ≤ ∑ l, w l * 2 := by
      exact Fintype.sum_le_sum fun l =>
        mul_le_mul_of_nonneg_left (hx.2 l) (hw.1 l)
    _ = dualObjective w := by
      simp [dualObjective, Finset.mul_sum]
      ring

/-- A finite dual certificate bounds the exact supremum defining `L4`. -/
theorem L4_le_dualObjective {n ε : ℕ} {w : FourLine n → ℝ}
    (hw : DualFeasible w) :
    L4 n ε ≤ dualObjective w := by
  apply csSup_le (fractionalValueSet_nonempty n ε)
  intro v hv
  rcases hv with ⟨x, hx, rfl⟩
  exact finite_weak_duality hx hw

end

end Checkerboard
