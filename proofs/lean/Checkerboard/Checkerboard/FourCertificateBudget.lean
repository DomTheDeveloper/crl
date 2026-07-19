import Checkerboard.FourCertificate

/-!
# Exact slack-deficit identity for four-direction certificates

The ordinary line-cover argument is an inequality.  This file records the
exact remainder: point-cover slack plus unused weighted line capacity.
-/

namespace Checkerboard

open scoped BigOperators

/-- Unused weighted capacity in the four principal line families. -/
def fourDeficit {n : ℕ} (w : FourWeights n) (s : Finset (Point n)) : ℚ :=
  (∑ i : Fin n,
      ((2 - fiberCard s (fun p : Point n => p.1) i : ℕ) : ℚ) * w.row i) +
  (∑ i : Fin n,
      ((2 - fiberCard s (fun p : Point n => p.2) i : ℕ) : ℚ) * w.column i) +
  (∑ i : Fin (2 * n - 1),
      ((2 - fiberCard s sumIndex i : ℕ) : ℚ) * w.sum i) +
  ∑ i : Fin (2 * n - 1),
      ((2 - fiberCard s differenceIndex i : ℕ) : ℚ) * w.difference i

private theorem fiber_capacity_identity
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (s : Finset α) (f : α → β) (weight : β → ℚ)
    (hcard : ∀ i, fiberCard s f i ≤ 2) :
    (∑ i, (fiberCard s f i : ℚ) * weight i) +
        ∑ i, ((2 - fiberCard s f i : ℕ) : ℚ) * weight i =
      2 * ∑ i, weight i := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sub (hcard i)]
  ring

/-- Exact double-counting identity: occupied weighted capacity plus deficit is
exactly twice the total line weight. -/
theorem fourCoverage_add_deficit {n : ℕ} {s : Finset (Point n)}
    (w : FourWeights n) (hntil : NoThreeInLine s) :
    (∑ p ∈ s, fourCoverage w p) + fourDeficit w s = fourCost w := by
  have hr := fiber_capacity_identity s (fun p : Point n => p.1) w.row
    (fun i => rowFiber_le_two hntil i)
  have hc := fiber_capacity_identity s (fun p : Point n => p.2) w.column
    (fun i => columnFiber_le_two hntil i)
  have hs := fiber_capacity_identity s sumIndex w.sum
    (fun i => sumFiber_le_two hntil i)
  have hd := fiber_capacity_identity s differenceIndex w.difference
    (fun i => differenceFiber_le_two hntil i)
  have hcoverage :
      (∑ p ∈ s, fourCoverage w p) =
        (∑ i : Fin n,
          (fiberCard s (fun p : Point n => p.1) i : ℚ) * w.row i) +
        (∑ i : Fin n,
          (fiberCard s (fun p : Point n => p.2) i : ℚ) * w.column i) +
        (∑ i : Fin (2 * n - 1),
          (fiberCard s sumIndex i : ℚ) * w.sum i) +
        ∑ i : Fin (2 * n - 1),
          (fiberCard s differenceIndex i : ℚ) * w.difference i := by
    calc
      (∑ p ∈ s, fourCoverage w p) =
          (∑ p ∈ s, w.row p.1) + (∑ p ∈ s, w.column p.2) +
            (∑ p ∈ s, w.sum (sumIndex p)) +
              ∑ p ∈ s, w.difference (differenceIndex p) := by
                simp [fourCoverage, Finset.sum_add_distrib, add_assoc]
      _ = _ := by
        rw [← sum_fiberCard_mul (R := ℚ) s
              (fun p : Point n => p.1) w.row,
            ← sum_fiberCard_mul (R := ℚ) s
              (fun p : Point n => p.2) w.column,
            ← sum_fiberCard_mul (R := ℚ) s sumIndex w.sum,
            ← sum_fiberCard_mul (R := ℚ) s differenceIndex w.difference]
  rw [hcoverage]
  unfold fourDeficit fourCost
  linarith

/-- Point slack plus line deficit. -/
def fourBudget {n : ℕ} (q : ℚ) (w : FourWeights n)
    (s : Finset (Point n)) : ℚ :=
  (∑ p ∈ s, (fourCoverage w p - q)) + fourDeficit w s

/-- Exact budget formula. -/
theorem fourBudget_eq {n : ℕ} {s : Finset (Point n)}
    (q : ℚ) (w : FourWeights n) (hntil : NoThreeInLine s) :
    fourBudget q w s = fourCost w - q * s.card := by
  have hid := fourCoverage_add_deficit w hntil
  unfold fourBudget
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  push_cast
  linarith

/-- The budget is nonnegative when every selected point is covered and all
weights are nonnegative. -/
theorem fourBudget_nonnegative {n : ℕ} {s : Finset (Point n)}
    (q : ℚ) (w : FourWeights n)
    (hrow : ∀ i, 0 ≤ w.row i)
    (hcolumn : ∀ i, 0 ≤ w.column i)
    (hsum : ∀ i, 0 ≤ w.sum i)
    (hdifference : ∀ i, 0 ≤ w.difference i)
    (hcover : ∀ p : ↥s, q ≤ fourCoverage w p.1)
    (hntil : NoThreeInLine s) : 0 ≤ fourBudget q w s := by
  have hdeficit : 0 ≤ fourDeficit w s := by
    unfold fourDeficit
    positivity
  have hslack : 0 ≤ ∑ p ∈ s, (fourCoverage w p - q) := by
    apply Finset.sum_nonneg
    intro p hp
    exact sub_nonneg.mpr (hcover ⟨p, hp⟩)
  unfold fourBudget
  linarith

/-- Every selected point's slack is bounded by the total budget. -/
theorem point_slack_le_budget {n : ℕ} {s : Finset (Point n)}
    (q : ℚ) (w : FourWeights n)
    (hrow : ∀ i, 0 ≤ w.row i)
    (hcolumn : ∀ i, 0 ≤ w.column i)
    (hsum : ∀ i, 0 ≤ w.sum i)
    (hdifference : ∀ i, 0 ≤ w.difference i)
    (hcover : ∀ p : ↥s, q ≤ fourCoverage w p.1)
    (hntil : NoThreeInLine s) {p : Point n} (hp : p ∈ s) :
    fourCoverage w p - q ≤ fourBudget q w s := by
  have hdeficit : 0 ≤ fourDeficit w s := by
    unfold fourDeficit
    positivity
  have hpoint : fourCoverage w p - q ≤
      ∑ z ∈ s, (fourCoverage w z - q) := by
    apply Finset.single_le_sum
    · intro z hz
      exact sub_nonneg.mpr (hcover ⟨z, hz⟩)
    · exact hp
  unfold fourBudget
  linarith

end Checkerboard
