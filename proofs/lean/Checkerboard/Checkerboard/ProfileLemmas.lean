import Checkerboard.CapacityProfiles

/-!
# First moments and geometric radii of checkerboard profiles
-/

namespace Checkerboard

open scoped BigOperators

/-- Closed form for an affine arithmetic progression. -/
theorem sum_range_affine (N : ℕ) (a b : ℝ) :
    (∑ k in Finset.range N, (a * (k : ℝ) + b)) =
      a * ((N : ℝ) * ((N : ℝ) - 1) / 2) + (N : ℝ) * b := by
  calc
    (∑ k in Finset.range N, (a * (k : ℝ) + b)) =
        a * (∑ k in Finset.range N, (k : ℝ)) + (N : ℝ) * b := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
    _ = _ := by rw [sum_range_cast_id]

/-- Odd-fat endpoint profile has zero centered first moment. -/
theorem oddFat_capacity_first (m : ℕ) (hm : 1 ≤ m) :
    (∑ k in Finset.range (2 * m + 1),
      (endpointCap (2 * m + 1) k : ℝ) *
        (2 * (k : ℝ) - 2 * (m : ℝ))) = 0 := by
  rw [endpointCap_weighted_sum (by omega)]
  have hs := sum_range_affine (2 * m + 1) (2 : ℝ) (-2 * (m : ℝ))
  have hlast : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hlast]
  rw [show (∑ k in Finset.range (2 * m + 1),
      (2 * (k : ℝ) - 2 * (m : ℝ))) =
      2 * ((((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) - 1)) / 2) +
        (((2 * m + 1 : ℕ) : ℝ)) * (-2 * (m : ℝ)) by
          simpa [sub_eq_add_neg] using hs]
  push_cast
  ring

/-- Odd-thin all-double profile has zero centered first moment. -/
theorem oddThin_capacity_first (m : ℕ) :
    (∑ k in Finset.range (2 * m),
      (doubleCap (2 * m) k : ℝ) *
        (2 * (k : ℝ) + 1 - 2 * (m : ℝ))) = 0 := by
  simp_rw [doubleCap, Nat.cast_ofNat, ← Finset.mul_sum]
  have hs := sum_range_affine (2 * m) (2 : ℝ) (1 - 2 * (m : ℝ))
  rw [show (∑ k in Finset.range (2 * m),
      (2 * (k : ℝ) + 1 - 2 * (m : ℝ))) =
      2 * ((((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1)) / 2) +
        (((2 * m : ℕ) : ℝ)) * (1 - 2 * (m : ℝ)) by
          simpa [sub_eq_add_neg] using hs]
  push_cast
  ring

/-- Even endpoint profile has zero centered first moment. -/
theorem evenEndpoint_capacity_first (m : ℕ) (hm : 1 ≤ m) :
    (∑ k in Finset.range (2 * m),
      (endpointCap (2 * m) k : ℝ) *
        (2 * (k : ℝ) - (2 * (m : ℝ) - 1))) = 0 := by
  rw [endpointCap_weighted_sum (by omega)]
  have hs := sum_range_affine (2 * m) (2 : ℝ) (-(2 * (m : ℝ) - 1))
  have hcast : (((2 * m - 1 : ℕ) : ℝ)) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
  rw [show (∑ k in Finset.range (2 * m),
      (2 * (k : ℝ) - (2 * (m : ℝ) - 1))) =
      2 * ((((2 * m : ℕ) : ℝ) * (((2 * m : ℕ) : ℝ) - 1)) / 2) +
        (((2 * m : ℕ) : ℝ)) * (-(2 * (m : ℝ) - 1)) by
          simpa [sub_eq_add_neg] using hs]
  rw [hcast]
  push_cast
  ring

/-- Even all-double profile has zero centered first moment. -/
theorem evenDouble_capacity_first (m : ℕ) (hm : 1 ≤ m) :
    (∑ k in Finset.range (2 * m - 1),
      (doubleCap (2 * m - 1) k : ℝ) *
        (2 * (k : ℝ) + 1 - (2 * (m : ℝ) - 1))) = 0 := by
  simp_rw [doubleCap, Nat.cast_ofNat, ← Finset.mul_sum]
  have hs := sum_range_affine (2 * m - 1) (2 : ℝ) (2 - 2 * (m : ℝ))
  have hcast : (((2 * m - 1 : ℕ) : ℝ)) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
  rw [show (∑ k in Finset.range (2 * m - 1),
      (2 * (k : ℝ) + 1 - (2 * (m : ℝ) - 1))) =
      2 * ((((2 * m - 1 : ℕ) : ℝ) * (((2 * m - 1 : ℕ) : ℝ) - 1)) / 2) +
        (((2 * m - 1 : ℕ) : ℝ)) * (2 - 2 * (m : ℝ)) by
          simpa [sub_eq_add_neg] using hs]
  rw [hcast]
  ring

/-- Radius of the odd-fat profile. -/
theorem oddFat_offset_sq_le {m k : ℕ} (hk : k < 2 * m + 1) :
    (2 * (k : ℝ) - 2 * (m : ℝ)) ^ 2 ≤ (2 * (m : ℝ)) ^ 2 := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkm : (k : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast (by omega : k ≤ 2 * m)
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hkm)]

/-- Radius of the odd-thin profile. -/
theorem oddThin_offset_sq_le {m k : ℕ} (hk : k < 2 * m) :
    (2 * (k : ℝ) + 1 - 2 * (m : ℝ)) ^ 2 ≤
      (2 * (m : ℝ) - 1) ^ 2 := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkmNat : k ≤ 2 * m - 1 := by omega
  have hkm : (k : ℝ) ≤ 2 * (m : ℝ) - 1 := by
    calc
      (k : ℝ) ≤ ((2 * m - 1 : ℕ) : ℝ) := by exact_mod_cast hkmNat
      _ = 2 * (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
        push_cast
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hkm)]

/-- Radius of the even endpoint profile. -/
theorem evenEndpoint_offset_sq_le {m k : ℕ} (hk : k < 2 * m) :
    (2 * (k : ℝ) - (2 * (m : ℝ) - 1)) ^ 2 ≤
      (2 * (m : ℝ) - 1) ^ 2 := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkmNat : k ≤ 2 * m - 1 := by omega
  have hkm : (k : ℝ) ≤ 2 * (m : ℝ) - 1 := by
    calc
      (k : ℝ) ≤ ((2 * m - 1 : ℕ) : ℝ) := by exact_mod_cast hkmNat
      _ = 2 * (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
        push_cast
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hkm)]

/-- Radius of the even all-double profile. -/
theorem evenDouble_offset_sq_le {m k : ℕ} (hm : 1 ≤ m) (hk : k < 2 * m - 1) :
    (2 * (k : ℝ) + 1 - (2 * (m : ℝ) - 1)) ^ 2 ≤
      (2 * (m : ℝ) - 2) ^ 2 := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkmNat : k ≤ 2 * m - 2 := by omega
  have hkm : (k : ℝ) ≤ 2 * (m : ℝ) - 2 := by
    calc
      (k : ℝ) ≤ ((2 * m - 2 : ℕ) : ℝ) := by exact_mod_cast hkmNat
      _ = 2 * (m : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ 2 * m)]
        push_cast
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hkm)]

end Checkerboard
