import Checkerboard.FiniteFramework

/-!
# Checkerboard capacity profiles

Exact finite-sum formulae for the centered row/column coordinates and the two
possible active diagonal profiles. The profiles are written in their natural
step-two parametrizations, which makes every parity issue explicit.
-/

namespace Checkerboard

open scoped BigOperators

theorem sum_range_cast_id (n : ℕ) :
    (∑ k in Finset.range n, (k : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sum_range_cast_sq (n : ℕ) :
    (∑ k in Finset.range n, (k : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

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
    _ = _ := by rw [sum_range_cast_sq, sum_range_cast_id]

theorem centered2_sum (n : ℕ) :
    (∑ k in Finset.range n, centered2Nat n k) = 0 := by
  simp_rw [centered2Nat, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_range_cast_id]
  simp
  ring

theorem centered2_square_sum (n : ℕ) :
    (∑ k in Finset.range n,
      ((2 * (k : ℝ) - ((n : ℝ) - 1)) ^ 2)) =
      (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  rw [show (fun k : ℕ => (2 * (k : ℝ) - ((n : ℝ) - 1)) ^ 2) =
      (fun k : ℕ => (2 * (k : ℝ) + (-((n : ℝ) - 1))) ^ 2) by
        funext k
        ring]
  rw [sum_range_affine_sq]
  ring

def endpointCap (N k : ℕ) : ℕ :=
  if k = 0 ∨ k + 1 = N then 1 else 2

def doubleCap (_N _k : ℕ) : ℕ := 2

theorem endpointCap_bounds (N k : ℕ) : 1 ≤ endpointCap N k ∧ endpointCap N k ≤ 2 := by
  unfold endpointCap
  split <;> omega

theorem endpointCap_cast {N k : ℕ} (hN : 2 ≤ N) (hk : k < N) :
    (endpointCap N k : ℝ) =
      2 - (if k = 0 then 1 else 0) - (if k = N - 1 then 1 else 0) := by
  have hs : k + 1 = N ↔ k = N - 1 := by omega
  by_cases h0 : k = 0
  · subst k
    have hlast : 0 ≠ N - 1 := by omega
    simp [endpointCap, hlast]
    norm_num
  · by_cases hlast : k = N - 1
    · subst k
      have hne0 : N - 1 ≠ 0 := by omega
      have hend : N - 1 + 1 = N := by omega
      simp [endpointCap, hne0, hend]
      norm_num
    · have hend : k + 1 ≠ N := fun h => hlast (hs.mp h)
      simp [endpointCap, h0, hlast, hend]

theorem endpointCap_weighted_sum {N : ℕ} (hN : 2 ≤ N) (f : ℕ → ℝ) :
    (∑ k in Finset.range N, (endpointCap N k : ℝ) * f k) =
      2 * (∑ k in Finset.range N, f k) - f 0 - f (N - 1) := by
  have hzero : 0 < N := by omega
  have hlast : N - 1 < N := by omega
  calc
    (∑ k in Finset.range N, (endpointCap N k : ℝ) * f k) =
        ∑ k in Finset.range N,
          (2 - (if k = 0 then 1 else 0) -
            (if k = N - 1 then 1 else 0)) * f k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [endpointCap_cast hN (Finset.mem_range.mp hk)]
    _ = 2 * (∑ k in Finset.range N, f k) - f 0 - f (N - 1) := by
          simp_rw [sub_mul]
          simp [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, hlast]

theorem endpointCap_sum {N : ℕ} (hN : 2 ≤ N) :
    ∑ k in Finset.range N, endpointCap N k = 2 * N - 2 := by
  have h := endpointCap_weighted_sum hN (fun _ => (1 : ℝ))
  have hsumreal :
      (∑ k in Finset.range N, (endpointCap N k : ℝ)) =
        2 * (N : ℝ) - 2 := by
    calc
      _ = 2 * (N : ℝ) - 1 - 1 := by simpa using h
      _ = 2 * (N : ℝ) - 2 := by ring
  have hle : 2 ≤ 2 * N := by omega
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_sub hle]
  push_cast
  exact hsumreal

theorem doubleCap_sum (N : ℕ) :
    ∑ k in Finset.range N, doubleCap N k = 2 * N := by
  simp [doubleCap, Nat.mul_comm]

theorem oddFat_capacity_second (m : ℕ) (hm : 1 ≤ m) :
    (∑ k in Finset.range (2 * m + 1),
      (endpointCap (2 * m + 1) k : ℝ) *
        (2 * (k : ℝ) - 2 * (m : ℝ)) ^ 2) =
      8 * (m : ℝ) * (2 * (m : ℝ) ^ 2 + 1) / 3 := by
  rw [endpointCap_weighted_sum (by omega)]
  have hs := sum_range_affine_sq (2 * m + 1) (2 : ℝ) (-2 * (m : ℝ))
  have hlast : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hlast]
  rw [show (∑ k in Finset.range (2 * m + 1),
      (2 * (k : ℝ) - 2 * (m : ℝ)) ^ 2) =
      2 ^ 2 * (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) - 1) *
        (2 * (((2 * m + 1 : ℕ) : ℝ)) - 1) / 6) +
      2 * 2 * (-2 * (m : ℝ)) *
        ((((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) - 1)) / 2) +
      (((2 * m + 1 : ℕ) : ℝ)) * (-2 * (m : ℝ)) ^ 2 by
        simpa [sub_eq_add_neg] using hs]
  push_cast
  ring

theorem oddThin_capacity_second (m : ℕ) :
    (∑ k in Finset.range (2 * m),
      (doubleCap (2 * m) k : ℝ) *
        (2 * (k : ℝ) + 1 - 2 * (m : ℝ)) ^ 2) =
      4 * (m : ℝ) * (2 * (m : ℝ) - 1) * (2 * (m : ℝ) + 1) / 3 := by
  simp_rw [doubleCap, Nat.cast_ofNat, ← Finset.mul_sum]
  have hs := sum_range_affine_sq (2 * m) (2 : ℝ) (1 - 2 * (m : ℝ))
  have hsum : (∑ k in Finset.range (2 * m),
      (2 * (k : ℝ) + 1 - 2 * (m : ℝ)) ^ 2) =
      2 ^ 2 * (((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1) *
        (2 * (((2 * m : ℕ) : ℝ)) - 1) / 6) +
      2 * 2 * (1 - 2 * (m : ℝ)) *
        ((((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1)) / 2) +
      (((2 * m : ℕ) : ℝ)) * (1 - 2 * (m : ℝ)) ^ 2 := by
    calc
      _ = ∑ k in Finset.range (2 * m),
          (2 * (k : ℝ) + (1 - 2 * (m : ℝ))) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = _ := hs
  rw [hsum]
  push_cast
  ring

theorem evenEndpoint_capacity_second (m : ℕ) (hm : 1 ≤ m) :
    (∑ k in Finset.range (2 * m),
      (endpointCap (2 * m) k : ℝ) *
        (2 * (k : ℝ) - (2 * (m : ℝ) - 1)) ^ 2) =
      2 * (2 * (m : ℝ) - 1) *
        (4 * (m : ℝ) ^ 2 - 4 * (m : ℝ) + 3) / 3 := by
  rw [endpointCap_weighted_sum (by omega)]
  have hs := sum_range_affine_sq (2 * m) (2 : ℝ) (-(2 * (m : ℝ) - 1))
  have hlast : 2 * m - 1 < 2 * m := by omega
  rw [show (∑ k in Finset.range (2 * m),
      (2 * (k : ℝ) - (2 * (m : ℝ) - 1)) ^ 2) =
      2 ^ 2 * (((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1) *
        (2 * (((2 * m : ℕ) : ℝ)) - 1) / 6) +
      2 * 2 * (-(2 * (m : ℝ) - 1)) *
        ((((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1)) / 2) +
      (((2 * m : ℕ) : ℝ)) * (-(2 * (m : ℝ) - 1)) ^ 2 by
        simpa [sub_eq_add_neg] using hs]
  push_cast
  have hmcast : (((2 * m - 1 : ℕ) : ℝ)) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [hmcast]
  ring

theorem evenDouble_capacity_second (m : ℕ) (hm : 1 ≤ m) :
    (∑ k in Finset.range (2 * m - 1),
      (doubleCap (2 * m - 1) k : ℝ) *
        (2 * (k : ℝ) + 1 - (2 * (m : ℝ) - 1)) ^ 2) =
      8 * (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 3 := by
  simp_rw [doubleCap, Nat.cast_ofNat, ← Finset.mul_sum]
  have hs := sum_range_affine_sq (2 * m - 1) (2 : ℝ) (2 - 2 * (m : ℝ))
  have hcast : (((2 * m - 1 : ℕ) : ℝ)) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hsum : (∑ k in Finset.range (2 * m - 1),
      (2 * (k : ℝ) + 1 - (2 * (m : ℝ) - 1)) ^ 2) =
      2 ^ 2 * (((2 * m - 1 : ℕ) : ℝ) * (((2 * m - 1 : ℕ) : ℝ) - 1) *
        (2 * (((2 * m - 1 : ℕ) : ℝ)) - 1) / 6) +
      2 * 2 * (2 - 2 * (m : ℝ)) *
        ((((2 * m - 1 : ℕ) : ℝ) * (((2 * m - 1 : ℕ) : ℝ) - 1)) / 2) +
      (((2 * m - 1 : ℕ) : ℝ)) * (2 - 2 * (m : ℝ)) ^ 2 := by
    calc
      _ = ∑ k in Finset.range (2 * m - 1),
          (2 * (k : ℝ) + (2 - 2 * (m : ℝ))) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = _ := hs
  rw [hsum]
  rw [hcast]
  ring

end Checkerboard
