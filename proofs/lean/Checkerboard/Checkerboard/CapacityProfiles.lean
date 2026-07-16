import Checkerboard.FiniteFramework

/-!
# Checkerboard capacity profiles

Exact finite-sum formulae for the centered row/column coordinates and the two
possible active diagonal profiles.  The profiles are written in their natural
step-two parametrizations, which makes every parity issue explicit.
-/

namespace Checkerboard

open scoped BigOperators

/-- Sum of the first `n` natural numbers, cast to `ℝ`. -/
theorem sum_range_cast_id (n : ℕ) :
    (∑ k in Finset.range n, (k : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Sum of squares of the first `n` natural numbers, cast to `ℝ`. -/
theorem sum_range_cast_sq (n : ℕ) :
    (∑ k in Finset.range n, (k : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Closed form for an affine arithmetic progression of squares. -/
theorem sum_range_affine_sq (N : ℕ) (a b : ℝ) :
    (∑ k in Finset.range N, (a * (k : ℝ) + b) ^ 2) =
      a ^ 2 * ((N : ℝ) * ((N : ℝ) - 1) * (2 * (N : ℝ) - 1) / 6) +
      2 * a * b * ((N : ℝ) * ((N : ℝ) - 1) / 2) +
      (N : ℝ) * b ^ 2 := by
  calc
    (∑ k in Finset.range N, (a * (k : ℝ) + b) ^ 2) =
        ∑ k in Finset.range N,
          (a ^ 2 * (k : ℝ) ^ 2 + 2 * a * b * (k : ℝ) + b ^ 2) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = a ^ 2 * (∑ k in Finset.range N, (k : ℝ) ^ 2) +
        2 * a * b * (∑ k in Finset.range N, (k : ℝ)) +
        (N : ℝ) * b ^ 2 := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
          ring
    _ = _ := by rw [sum_range_cast_sq, sum_range_cast_id]

/-- Sum of squares of the doubled centered row coordinates. -/
theorem centered2_square_sum (n : ℕ) :
    (∑ k in Finset.range n,
      ((2 * (k : ℝ) - ((n : ℝ) - 1)) ^ 2)) =
      (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  rw [show (fun k : ℕ => (2 * (k : ℝ) - ((n : ℝ) - 1)) ^ 2) =
      (fun k : ℕ => (2 * (k : ℝ) + (-((n : ℝ) - 1))) ^ 2) by funext k; ring]
  rw [sum_range_affine_sq]
  ring

/-- The endpoint-reduced capacity profile: one unit at each endpoint and two elsewhere. -/
def endpointCap (N k : ℕ) : ℕ :=
  if k = 0 ∨ k + 1 = N then 1 else 2

/-- The all-double capacity profile. -/
def doubleCap (_N _k : ℕ) : ℕ := 2

/-- Endpoint capacity is always positive and at most two. -/
theorem endpointCap_bounds (N k : ℕ) : 1 ≤ endpointCap N k ∧ endpointCap N k ≤ 2 := by
  unfold endpointCap
  split <;> omega

/-- Total capacity of the endpoint profile. -/
theorem endpointCap_sum {N : ℕ} (hN : 2 ≤ N) :
    ∑ k in Finset.range N, endpointCap N k = 2 * N - 2 := by
  have hlast : N - 1 < N := by omega
  have hzero : 0 < N := by omega
  calc
    ∑ k in Finset.range N, endpointCap N k =
        endpointCap N 0 + endpointCap N (N - 1) +
          ∑ k in (Finset.range N).erase 0 |>.erase (N - 1), endpointCap N k := by
            rw [← Finset.sum_erase_add _ _ (by simp [hzero])]
            rw [← Finset.sum_erase_add _ _]
            · ring
            · simp [hlast, hN]
    _ = 1 + 1 + ∑ _k in (Finset.range N).erase 0 |>.erase (N - 1), 2 := by
          congr 1
          · simp [endpointCap, hN]
          · apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_erase, Finset.mem_range] at hk
            simp [endpointCap, hk.1, hk.2.1, hk.2.2]
    _ = 2 * N - 2 := by
          simp [Finset.card_erase_of_mem, hlast, hzero]
          omega

/-- Total capacity of the all-double profile. -/
theorem doubleCap_sum (N : ℕ) :
    ∑ k in Finset.range N, doubleCap N k = 2 * N := by
  simp [doubleCap]

/-- Odd board, fat class: one diagonal-family second moment. -/
theorem oddFat_capacity_second (m : ℕ) :
    (∑ k in Finset.range (2 * m + 1),
      (endpointCap (2 * m + 1) k : ℝ) *
        (2 * (k : ℝ) - 2 * (m : ℝ)) ^ 2) =
      8 * (m : ℝ) * (2 * (m : ℝ) ^ 2 + 1) / 3 := by
  sorry

/-- Odd board, thin class: one diagonal-family second moment. -/
theorem oddThin_capacity_second (m : ℕ) :
    (∑ k in Finset.range (2 * m),
      (doubleCap (2 * m) k : ℝ) *
        (2 * (k : ℝ) + 1 - 2 * (m : ℝ)) ^ 2) =
      4 * (m : ℝ) * (2 * (m : ℝ) - 1) * (2 * (m : ℝ) + 1) / 3 := by
  sorry

/-- Even board: the endpoint-profile diagonal-family second moment. -/
theorem evenEndpoint_capacity_second (m : ℕ) :
    (∑ k in Finset.range (2 * m),
      (endpointCap (2 * m) k : ℝ) *
        (2 * (k : ℝ) - (2 * (m : ℝ) - 1)) ^ 2) =
      2 * (2 * (m : ℝ) - 1) *
        (4 * (m : ℝ) ^ 2 - 4 * (m : ℝ) + 3) / 3 := by
  sorry

/-- Even board: the all-double diagonal-family second moment. -/
theorem evenDouble_capacity_second (m : ℕ) :
    (∑ k in Finset.range (2 * m - 1),
      (doubleCap (2 * m - 1) k : ℝ) *
        (2 * (k : ℝ) + 1 - (2 * (m : ℝ) - 1)) ^ 2) =
      8 * (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 3 := by
  sorry

end Checkerboard
