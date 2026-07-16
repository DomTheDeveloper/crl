import Checkerboard.CapacityProfiles

/-!
# Uniform active-diagonal profiles

A monochromatic checkerboard diagonal has one fixed parity.  Writing its raw
index as `2k + r`, with `r ∈ {0,1}`, gives a single uniform interface for all
four parity cases.  Parity zero includes the two corner diagonals and therefore
uses `endpointCap`; parity one contains only nontrivial diagonals and uses the
all-double profile.
-/

namespace Checkerboard

open scoped BigOperators

/-- Number of active raw indices of parity `r` in `0, ..., 2n-2`. -/
def activeCount (n r : ℕ) : ℕ := if r = 0 then n else n - 1

/-- Centered coordinate of the active raw index `2k+r`. -/
def activeCoord (n r k : ℕ) : ℝ :=
  2 * (k : ℝ) + (r : ℝ) - ((n : ℝ) - 1)

/-- Capacity profile on active diagonals of parity `r`. -/
def activeCap (n r k : ℕ) : ℕ :=
  if r = 0 then endpointCap n k else doubleCap (n - 1) k

@[simp] theorem activeCount_zero (n : ℕ) : activeCount n 0 = n := by
  simp [activeCount]

@[simp] theorem activeCount_one (n : ℕ) : activeCount n 1 = n - 1 := by
  simp [activeCount]

@[simp] theorem activeCoord_zero (n k : ℕ) :
    activeCoord n 0 k = centered2Nat n k := by
  simp [activeCoord, centered2Nat]

/-- Both active profiles have total capacity `2n-2`. -/
theorem activeCap_sum {n r : ℕ} (hn : 2 ≤ n) (hr : r ≤ 1) :
    ∑ k in Finset.range (activeCount n r), activeCap n r k = 2 * n - 2 := by
  by_cases h0 : r = 0
  · subst r
    simpa [activeCap] using endpointCap_sum hn
  · have h1 : r = 1 := by omega
    subst r
    rw [activeCount_one]
    simp [activeCap, doubleCap_sum]
    omega

/-- The active centered coordinates have zero unweighted first moment. -/
theorem activeCoord_sum {n r : ℕ} (hn : 2 ≤ n) (hr : r ≤ 1) :
    (∑ k in Finset.range (activeCount n r), activeCoord n r k) = 0 := by
  by_cases h0 : r = 0
  · subst r
    simpa using centered2_sum n
  · have h1 : r = 1 := by omega
    subst r
    rw [activeCount_one]
    have hn1 : 1 ≤ n := by omega
    calc
      (∑ k in Finset.range (n - 1), activeCoord n 1 k) =
          2 * (∑ k in Finset.range (n - 1), (k : ℝ)) +
            ((n - 1 : ℕ) : ℝ) * (2 - (n : ℝ)) := by
              simp_rw [activeCoord, Finset.sum_sub_distrib,
                Finset.sum_add_distrib, ← Finset.mul_sum]
              simp
              ring
      _ = 0 := by
        rw [sum_range_cast_id]
        rw [Nat.cast_sub hn1]
        push_cast
        ring

/-- The active capacity profile has zero first moment. -/
theorem activeCap_first {n r : ℕ} (hn : 2 ≤ n) (hr : r ≤ 1) :
    (∑ k in Finset.range (activeCount n r),
      (activeCap n r k : ℝ) * activeCoord n r k) = 0 := by
  by_cases h0 : r = 0
  · subst r
    rw [activeCount_zero]
    simp only [activeCap, if_pos rfl]
    rw [endpointCap_weighted_sum hn]
    rw [activeCoord_sum hn (by omega : 0 ≤ 1)]
    have hn1 : 1 ≤ n := by omega
    rw [Nat.cast_sub hn1]
    simp [activeCoord]
    ring
  · have h1 : r = 1 := by omega
    subst r
    rw [activeCount_one]
    simp_rw [activeCap, if_neg (by decide : (1 : ℕ) ≠ 0), doubleCap,
      Nat.cast_ofNat, ← Finset.mul_sum]
    rw [show (∑ k in Finset.range (n - 1), activeCoord n 1 k) = 0 by
      simpa [activeCount] using activeCoord_sum hn (by omega : (1 : ℕ) ≤ 1)]
    ring

/-- Second moment of the endpoint-reduced active profile. -/
theorem activeCap_second_zero {n : ℕ} (hn : 2 ≤ n) :
    (∑ k in Finset.range (activeCount n 0),
      (activeCap n 0 k : ℝ) * activeCoord n 0 k ^ 2) =
      2 * ((n : ℝ) - 1) *
        ((n : ℝ) ^ 2 - 2 * (n : ℝ) + 3) / 3 := by
  rw [activeCount_zero]
  simp only [activeCap, if_pos rfl]
  rw [endpointCap_weighted_sum hn]
  rw [show (∑ k in Finset.range n, activeCoord n 0 k ^ 2) =
      (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 by
        simpa using centered2_square_sum n]
  have hn1 : 1 ≤ n := by omega
  rw [Nat.cast_sub hn1]
  simp [activeCoord]
  ring

/-- Second moment of the all-double active profile. -/
theorem activeCap_second_one {n : ℕ} (hn : 2 ≤ n) :
    (∑ k in Finset.range (activeCount n 1),
      (activeCap n 1 k : ℝ) * activeCoord n 1 k ^ 2) =
      2 * (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 3 := by
  rw [activeCount_one]
  simp_rw [activeCap, if_neg (by decide : (1 : ℕ) ≠ 0), doubleCap,
    Nat.cast_ofNat, ← Finset.mul_sum]
  have hn1 : 1 ≤ n := by omega
  have hs := sum_range_affine_sq (n - 1) (2 : ℝ) (2 - (n : ℝ))
  rw [show (∑ k in Finset.range (n - 1), activeCoord n 1 k ^ 2) =
      2 ^ 2 * (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) - 1) *
        (2 * (((n - 1 : ℕ) : ℝ)) - 1) / 6) +
      2 * 2 * (2 - (n : ℝ)) *
        ((((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) - 1)) / 2) +
      (((n - 1 : ℕ) : ℝ)) * (2 - (n : ℝ)) ^ 2 by
        simpa [activeCoord] using hs]
  rw [Nat.cast_sub hn1]
  push_cast
  ring

end Checkerboard
