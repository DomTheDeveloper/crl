import BernsteinObstacle.GreenOddMeshClosedLimit
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Hyperbolic finite sums for the odd-mesh Green interpolant

These are the exact finite-sum identities used to reduce the nodal P1 energy to
the closed mesh-width expression.
-/

/-- Unnormalized positive-half Green node. -/
def oddGreenSinhNode (h : ℝ) (r : ℕ) : ℝ :=
  Real.sinh ((r : ℝ) * h)

/-- Sum of squared positive-half node values `r=1,...,m`. -/
def oddGreenSinhSquareSum (m : ℕ) (h : ℝ) : ℝ :=
  ∑ r ∈ Finset.range m, oddGreenSinhNode h (r + 1) ^ 2

/-- Closed form of the squared-node sum. -/
def oddGreenSinhSquareClosed (m : ℕ) (h : ℝ) : ℝ :=
  (Real.sinh ((m : ℝ) * h) * Real.cosh (((m : ℝ) + 1) * h) /
      Real.sinh h - (m : ℝ)) / 2

/-- Sum of adjacent node products. -/
def oddGreenSinhProductSum (m : ℕ) (h : ℝ) : ℝ :=
  ∑ r ∈ Finset.range m,
    oddGreenSinhNode h (r + 1) * oddGreenSinhNode h r

/-- Closed form of the adjacent-product sum. -/
def oddGreenSinhProductClosed (m : ℕ) (h : ℝ) : ℝ :=
  Real.sinh (2 * (m : ℝ) * h) / (4 * Real.sinh h) -
    (m : ℝ) * Real.cosh h / 2

/-- Hyperbolic identity driving the squared-node induction. -/
theorem oddGreenSinhSquare_step_identity (A h : ℝ) :
    Real.sinh (A + h) * Real.cosh (A + 2 * h) -
        Real.sinh A * Real.cosh (A + h) =
      Real.sinh h * (2 * Real.sinh (A + h) ^ 2 + 1) := by
  rw [show A + 2 * h = (A + h) + h by ring]
  rw [Real.cosh_add, Real.sinh_add, Real.cosh_add]
  nlinarith [Real.cosh_sq_sub_sinh_sq A,
    Real.cosh_sq_sub_sinh_sq h]

/-- Hyperbolic identity driving the adjacent-product induction. -/
theorem oddGreenSinhProduct_step_identity
    (A h : ℝ) (hh : Real.sinh h ≠ 0) :
    Real.sinh (2 * (A + h)) / (4 * Real.sinh h) -
        Real.sinh (2 * A) / (4 * Real.sinh h) - Real.cosh h / 2 =
      Real.sinh (A + h) * Real.sinh A := by
  rw [Real.sinh_two_mul, Real.sinh_two_mul]
  rw [Real.sinh_add, Real.cosh_add]
  field_simp [hh]
  nlinarith [Real.cosh_sq_sub_sinh_sq A,
    Real.cosh_sq_sub_sinh_sq h]

/-- One-step recurrence for the closed squared-node sum. -/
theorem oddGreenSinhSquareClosed_succ
    (m : ℕ) (h : ℝ) (hh : Real.sinh h ≠ 0) :
    oddGreenSinhSquareClosed (m + 1) h =
      oddGreenSinhSquareClosed m h +
        oddGreenSinhNode h (m + 1) ^ 2 := by
  let A : ℝ := (m : ℝ) * h
  have hA : ((m + 1 : ℕ) : ℝ) * h = A + h := by
    simp [A]
    ring
  have hA2 : (((m + 1 : ℕ) : ℝ) + 1) * h = A + 2 * h := by
    push_cast
    simp [A]
    ring
  have hstep := oddGreenSinhSquare_step_identity A h
  unfold oddGreenSinhSquareClosed oddGreenSinhNode
  rw [hA, hA2]
  change
    (Real.sinh (A + h) * Real.cosh (A + 2 * h) / Real.sinh h -
        ((m : ℝ) + 1)) / 2 =
      (Real.sinh A * Real.cosh (A + h) / Real.sinh h - (m : ℝ)) / 2 +
        Real.sinh (A + h) ^ 2
  field_simp [hh] at hstep ⊢
  nlinarith

/-- One-step recurrence for the closed adjacent-product sum. -/
theorem oddGreenSinhProductClosed_succ
    (m : ℕ) (h : ℝ) (hh : Real.sinh h ≠ 0) :
    oddGreenSinhProductClosed (m + 1) h =
      oddGreenSinhProductClosed m h +
        oddGreenSinhNode h (m + 1) * oddGreenSinhNode h m := by
  let A : ℝ := (m : ℝ) * h
  have hA : ((m + 1 : ℕ) : ℝ) * h = A + h := by
    simp [A]
    ring
  have htwo : 2 * ((m + 1 : ℕ) : ℝ) * h = 2 * (A + h) := by
    rw [hA]
  have hstep := oddGreenSinhProduct_step_identity A h hh
  unfold oddGreenSinhProductClosed oddGreenSinhNode
  rw [htwo]
  change
    Real.sinh (2 * (A + h)) / (4 * Real.sinh h) -
        ((m : ℝ) + 1) * Real.cosh h / 2 =
      (Real.sinh (2 * A) / (4 * Real.sinh h) -
          (m : ℝ) * Real.cosh h / 2) +
        Real.sinh (A + h) * Real.sinh A
  nlinarith

/-- Exact finite sum of squared hyperbolic nodes. -/
theorem oddGreenSinhSquareSum_eq_closed
    (m : ℕ) (h : ℝ) (hh : Real.sinh h ≠ 0) :
    oddGreenSinhSquareSum m h = oddGreenSinhSquareClosed m h := by
  induction m with
  | zero =>
      simp [oddGreenSinhSquareSum, oddGreenSinhSquareClosed]
  | succ m ih =>
      rw [show Nat.succ m = m + 1 by omega]
      unfold oddGreenSinhSquareSum
      rw [Finset.sum_range_succ]
      fold oddGreenSinhSquareSum m h
      rw [ih]
      exact (oddGreenSinhSquareClosed_succ m h hh).symm

/-- Exact finite sum of adjacent hyperbolic node products. -/
theorem oddGreenSinhProductSum_eq_closed
    (m : ℕ) (h : ℝ) (hh : Real.sinh h ≠ 0) :
    oddGreenSinhProductSum m h = oddGreenSinhProductClosed m h := by
  induction m with
  | zero =>
      simp [oddGreenSinhProductSum, oddGreenSinhProductClosed]
  | succ m ih =>
      rw [show Nat.succ m = m + 1 by omega]
      unfold oddGreenSinhProductSum
      rw [Finset.sum_range_succ]
      fold oddGreenSinhProductSum m h
      rw [ih]
      exact (oddGreenSinhProductClosed_succ m h hh).symm

/-- Squared difference sum in terms of the two certified primitive sums. -/
theorem oddGreenSinhDifferenceSum_eq
    (m : ℕ) (h : ℝ) :
    (∑ r ∈ Finset.range m,
      (oddGreenSinhNode h (r + 1) - oddGreenSinhNode h r) ^ 2) =
      oddGreenSinhSquareSum m h + oddGreenSinhSquareSum (m - 1) h -
        2 * oddGreenSinhProductSum m h := by
  unfold oddGreenSinhSquareSum oddGreenSinhProductSum
  rw [Finset.sum_sub_distrib]
  · sorry

end

end BernsteinObstacle
