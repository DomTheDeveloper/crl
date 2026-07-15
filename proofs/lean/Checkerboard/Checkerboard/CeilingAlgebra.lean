import Mathlib

/-!
# Algebraic certificates for the strengthened finite ceiling bound

This file checks the exact cubic reductions and positivity estimates used in
the finite ceiling-bound computation. It formalizes the algebraic core of the
claimed bound `|S| ≤ ⌈2^(2/3)n⌉`; the separate combinatorial majorization of
diagonal capacity units remains in the paper/Python certificate.
-/

namespace Checkerboard

noncomputable section

/-- Universal polynomial majorant for the `q` largest squared offsets. -/
def offsetMajorant (n q : ℝ) : ℝ :=
  q * n^2 - (1 / 2 : ℝ) * n * q * (q + 1) +
    q * (q + 1) * (2 * q + 1) / 24

def kOddFat (n : ℝ) : ℝ := -((n - 1) * (n - 2) * (n - 3)) / 3
def kOddThin (n : ℝ) : ℝ := -(n * (n - 1) * (n - 5)) / 3
def kEven (n : ℝ) : ℝ := -((n - 1) * (n^2 - 5 * n + 3)) / 3

def contradictionDeficit (c n : ℝ) : ℝ := (2 - c) * n - 3

/-- Exact odd-fat reduction modulo `c³=4`. -/
theorem oddFat_gap_identity {c n : ℝ} (hc : c^3 = 4) :
    -kOddFat n - offsetMajorant n (contradictionDeficit c n) =
      ((15 * c^2 - 36) * n^2 + (37 * c + 86) * n - 18) / 24 := by
  simp [kOddFat, offsetMajorant, contradictionDeficit]
  nlinarith [hc]

/-- Exact odd-thin reduction modulo `c³=4`. -/
theorem oddThin_gap_identity {c n : ℝ} (hc : c^3 = 4) :
    -kOddThin n - offsetMajorant n (contradictionDeficit c n) =
      ((15 * c^2 - 36) * n^2 + (37 * c + 38) * n + 30) / 24 := by
  simp [kOddThin, offsetMajorant, contradictionDeficit]
  nlinarith [hc]

/-- Exact even reduction modulo `c³=4`. -/
theorem even_gap_identity {c n : ℝ} (hc : c^3 = 4) :
    -kEven n - offsetMajorant n (contradictionDeficit c n) =
      ((15 * c^2 - 36) * n^2 + (37 * c + 62) * n + 6) / 24 := by
  simp [kEven, offsetMajorant, contradictionDeficit]
  nlinarith [hc]

/-- A positive real cube root of four has square strictly larger than `5/2`. -/
theorem square_gt_five_halves {c : ℝ} (hcpos : 0 < c) (hc : c^3 = 4) :
    (5 / 2 : ℝ) < c^2 := by
  by_contra h
  have hle : c^2 ≤ (5 / 2 : ℝ) := le_of_not_gt h
  have hc2nonneg : 0 ≤ c^2 := sq_nonneg c
  have hsq : (c^2)^2 ≤ ((5 / 2 : ℝ))^2 :=
    mul_self_le_mul_self hc2nonneg hle
  have hcube : (c^2)^3 ≤ ((5 / 2 : ℝ))^3 := by
    calc
      (c^2)^3 = (c^2)^2 * c^2 := by ring
      _ ≤ ((5 / 2 : ℝ))^2 * c^2 :=
        mul_le_mul_of_nonneg_right hsq hc2nonneg
      _ ≤ ((5 / 2 : ℝ))^2 * (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hle (sq_nonneg (5 / 2 : ℝ))
      _ = ((5 / 2 : ℝ))^3 := by ring
  have hc6 : (c^2)^3 = 16 := by
    calc
      (c^2)^3 = (c^3)^2 := by ring
      _ = 16 := by rw [hc]; norm_num
  rw [hc6] at hcube
  norm_num at hcube

private theorem n_sq_ge_36 {n : ℝ} (hn : 6 ≤ n) : 36 ≤ n^2 := by
  nlinarith [sq_nonneg (n - 6)]

/-- Positivity of the odd-fat contradiction gap. -/
theorem oddFat_gap_positive {c n : ℝ} (hcpos : 0 < c)
    (hc2 : (5 / 2 : ℝ) < c^2) (hn : 6 ≤ n) :
    0 < ((15 * c^2 - 36) * n^2 + (37 * c + 86) * n - 18) / 24 := by
  have hcoef : (3 / 2 : ℝ) < 15 * c^2 - 36 := by nlinarith
  have hnpos : 0 < n := by linarith
  have hn2pos : 0 < n^2 := sq_pos_of_pos hnpos
  have hn2 := n_sq_ge_36 hn
  have hmul : (3 / 2 : ℝ) * n^2 < (15 * c^2 - 36) * n^2 :=
    mul_lt_mul_of_pos_right hcoef hn2pos
  have h54 : (54 : ℝ) ≤ (3 / 2 : ℝ) * n^2 := by nlinarith
  have hquad : (54 : ℝ) < (15 * c^2 - 36) * n^2 :=
    lt_of_le_of_lt h54 hmul
  have hlin : 0 < (37 * c + 86) * n := by
    exact mul_pos (by nlinarith) hnpos
  nlinarith

/-- Positivity of the odd-thin contradiction gap. -/
theorem oddThin_gap_positive {c n : ℝ} (hcpos : 0 < c)
    (hc2 : (5 / 2 : ℝ) < c^2) (hn : 6 ≤ n) :
    0 < ((15 * c^2 - 36) * n^2 + (37 * c + 38) * n + 30) / 24 := by
  have hcoef : (3 / 2 : ℝ) < 15 * c^2 - 36 := by nlinarith
  have hnpos : 0 < n := by linarith
  have hn2pos : 0 < n^2 := sq_pos_of_pos hnpos
  have hn2 := n_sq_ge_36 hn
  have hmul : (3 / 2 : ℝ) * n^2 < (15 * c^2 - 36) * n^2 :=
    mul_lt_mul_of_pos_right hcoef hn2pos
  have h54 : (54 : ℝ) ≤ (3 / 2 : ℝ) * n^2 := by nlinarith
  have hquad : (54 : ℝ) < (15 * c^2 - 36) * n^2 :=
    lt_of_le_of_lt h54 hmul
  have hlin : 0 < (37 * c + 38) * n := by
    exact mul_pos (by nlinarith) hnpos
  nlinarith

/-- Positivity of the even contradiction gap. -/
theorem even_gap_positive {c n : ℝ} (hcpos : 0 < c)
    (hc2 : (5 / 2 : ℝ) < c^2) (hn : 6 ≤ n) :
    0 < ((15 * c^2 - 36) * n^2 + (37 * c + 62) * n + 6) / 24 := by
  have hcoef : (3 / 2 : ℝ) < 15 * c^2 - 36 := by nlinarith
  have hnpos : 0 < n := by linarith
  have hn2pos : 0 < n^2 := sq_pos_of_pos hnpos
  have hn2 := n_sq_ge_36 hn
  have hmul : (3 / 2 : ℝ) * n^2 < (15 * c^2 - 36) * n^2 :=
    mul_lt_mul_of_pos_right hcoef hn2pos
  have h54 : (54 : ℝ) ≤ (3 / 2 : ℝ) * n^2 := by nlinarith
  have hquad : (54 : ℝ) < (15 * c^2 - 36) * n^2 :=
    lt_of_le_of_lt h54 hmul
  have hlin : 0 < (37 * c + 62) * n := by
    exact mul_pos (by nlinarith) hnpos
  nlinarith

/-- Combined odd-fat algebraic contradiction certificate. -/
theorem oddFat_certificate {c n : ℝ} (hcpos : 0 < c) (hc : c^3 = 4)
    (hn : 6 ≤ n) :
    0 < -kOddFat n - offsetMajorant n (contradictionDeficit c n) := by
  rw [oddFat_gap_identity hc]
  exact oddFat_gap_positive hcpos (square_gt_five_halves hcpos hc) hn

/-- Combined odd-thin algebraic contradiction certificate. -/
theorem oddThin_certificate {c n : ℝ} (hcpos : 0 < c) (hc : c^3 = 4)
    (hn : 6 ≤ n) :
    0 < -kOddThin n - offsetMajorant n (contradictionDeficit c n) := by
  rw [oddThin_gap_identity hc]
  exact oddThin_gap_positive hcpos (square_gt_five_halves hcpos hc) hn

/-- Combined even algebraic contradiction certificate. -/
theorem even_certificate {c n : ℝ} (hcpos : 0 < c) (hc : c^3 = 4)
    (hn : 6 ≤ n) :
    0 < -kEven n - offsetMajorant n (contradictionDeficit c n) := by
  rw [even_gap_identity hc]
  exact even_gap_positive hcpos (square_gt_five_halves hcpos hc) hn

end

end Checkerboard
