import Mathlib

/-!
# The three all-n contradiction inequalities for the `2n-4` theorem

The geometric part of the paper bounds `a²+b²` above by a parity-dependent
radius expression. The defect-moment identity bounds it below. The lemmas
below formally prove that those two bounds are incompatible in the stated
ranges.
-/

namespace Checkerboard

noncomputable section

/-- Odd side length, fat checkerboard class. -/
theorem oddFat_radius_gap {n : ℝ} (hn : 7 ≤ n) :
    2 * (n - 1)^2 < (n - 1) * (n - 2) * (n - 3) := by
  have hn0 : 0 ≤ n := by linarith
  have hnm7 : 0 ≤ n - 7 := by linarith
  have hprod : 0 ≤ n * (n - 7) := mul_nonneg hn0 hnm7
  have hfactor : 0 < n^2 - 7 * n + 8 := by
    nlinarith
  have hn1 : 0 < n - 1 := by linarith
  have hpos : 0 < (n - 1) * (n^2 - 7 * n + 8) :=
    mul_pos hn1 hfactor
  nlinarith

/-- Odd side length, thin checkerboard class. -/
theorem oddThin_radius_gap {n : ℝ} (hn : 7 ≤ n) :
    2 * (n - 2)^2 < n * (n - 1) * (n - 5) := by
  let t : ℝ := n - 7
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht2 : 0 ≤ t^2 := sq_nonneg t
  have ht3 : 0 ≤ t^3 := by
    exact mul_nonneg ht2 ht
  have hpos : 0 < t^3 + 13 * t^2 + 48 * t + 34 := by
    nlinarith
  dsimp [t] at hpos
  nlinarith

/-- Even side length. -/
theorem even_radius_gap {n : ℝ} (hn : 6 ≤ n) :
    (n - 1)^2 + (n - 2)^2 < (n - 1) * (n^2 - 5 * n + 3) := by
  let t : ℝ := n - 6
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht2 : 0 ≤ t^2 := sq_nonneg t
  have ht3 : 0 ≤ t^3 := by
    exact mul_nonneg ht2 ht
  have hpos : 0 < t^3 + 10 * t^2 + 26 * t + 4 := by
    nlinarith
  dsimp [t] at hpos
  nlinarith

/-- Abstract closure of the odd-fat `q=1` contradiction. -/
theorem oddFat_q1_impossible {n a b : ℝ} (hn : 7 ≤ n)
    (hupper : a^2 + b^2 ≤ 2 * (n - 1)^2)
    (hlower : (n - 1) * (n - 2) * (n - 3) ≤ a^2 + b^2) : False := by
  have hgap := oddFat_radius_gap hn
  linarith

/-- Abstract closure of the odd-thin `q=1` contradiction. -/
theorem oddThin_q1_impossible {n a b : ℝ} (hn : 7 ≤ n)
    (hupper : a^2 + b^2 ≤ 2 * (n - 2)^2)
    (hlower : n * (n - 1) * (n - 5) ≤ a^2 + b^2) : False := by
  have hgap := oddThin_radius_gap hn
  linarith

/-- Abstract closure of the even `q=1` contradiction. -/
theorem even_q1_impossible {n a b : ℝ} (hn : 6 ≤ n)
    (hupper : a^2 + b^2 ≤ (n - 1)^2 + (n - 2)^2)
    (hlower : (n - 1) * (n^2 - 5 * n + 3) ≤ a^2 + b^2) : False := by
  have hgap := even_radius_gap hn
  linarith

end

end Checkerboard
