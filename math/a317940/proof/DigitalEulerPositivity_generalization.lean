import Mathlib
import Mathlib.Data.Nat.EvenOddRec

open Nat Finset

namespace DigitalEulerPositivity

/-- Coefficients of the logarithmic derivative of
`∏ r, (1 + q * X^(2^r))`, characterized by its binary functional equation. -/
noncomputable def logDerivCoeff (q : ℚ) : ℕ → ℚ :=
  Nat.evenOddRec q
    (fun r _ => q ^ (2 * r + 1))
    (fun r x => 2 * x - q ^ (2 * r + 2))

@[simp] theorem logDerivCoeff_zero (q : ℚ) : logDerivCoeff q 0 = q := by
  simp [logDerivCoeff]

@[simp] theorem logDerivCoeff_even (q : ℚ) (r : ℕ) :
    logDerivCoeff q (2 * r) = q ^ (2 * r + 1) := by
  simp [logDerivCoeff, Nat.evenOddRec_even]

@[simp] theorem logDerivCoeff_odd (q : ℚ) (r : ℕ) :
    logDerivCoeff q (2 * r + 1) =
      2 * logDerivCoeff q r - q ^ (2 * r + 2) := by
  simp [logDerivCoeff, Nat.evenOddRec_odd]

/-- For `0 < q ≤ 1`, all logarithmic-derivative coefficients admit the
strictly positive lower bound `q^(n+1)`. -/
theorem logDerivCoeff_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∀ n : ℕ, q ^ (n + 1) ≤ logDerivCoeff q n := by
  have hp_le_one : ∀ k : ℕ, q ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hk0 : 0 ≤ q ^ k := pow_nonneg hq.le k
        nlinarith
  intro n
  induction n using Nat.evenOddRec with
  | h0 => simp [logDerivCoeff]
  | h_even r ih => simp [logDerivCoeff_even]
  | h_odd r ih =>
      rw [logDerivCoeff_odd]
      have hx0 : 0 ≤ q ^ (r + 1) := pow_nonneg hq.le _
      have hx1 : q ^ (r + 1) ≤ 1 := hp_le_one (r + 1)
      have hsq : q ^ (2 * r + 2) ≤ q ^ (r + 1) := by
        rw [show 2 * r + 2 = (r + 1) + (r + 1) by omega, pow_add]
        nlinarith
      have hle : q ^ (2 * r + 2) ≤ logDerivCoeff q r := hsq.trans ih
      linarith

/-- Strict positivity of the logarithmic-derivative coefficients. -/
theorem logDerivCoeff_pos (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (n : ℕ) :
    0 < logDerivCoeff q n := by
  have hp : 0 < q ^ (n + 1) := pow_pos hq _
  exact hp.trans_le (logDerivCoeff_lower q hq hq1 n)

/-- The coefficient sequence of the canonical formal solution of
`F' = α D_q F`, `F(0)=1`.  This is the formal `α`-power of the binary
Euler product associated to `q`. -/
noncomputable def coeff (q α : ℚ) : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    match n with
    | 0 => 1
    | m + 1 =>
        α * Finset.sum (range (m + 1))
            (fun i => logDerivCoeff q i *
              IH (m - i) (Nat.lt_succ_of_le (Nat.sub_le m i))) /
          (m + 1)

@[simp] theorem coeff_zero (q α : ℚ) : coeff q α 0 = 1 := by
  unfold coeff
  rw [WellFounded.fix_eq]

 theorem coeff_succ (q α : ℚ) (m : ℕ) :
    coeff q α (m + 1) =
      α * Finset.sum (range (m + 1))
          (fun i => logDerivCoeff q i * coeff q α (m - i)) /
        (m + 1) := by
  unfold coeff
  rw [WellFounded.fix_eq]

/-- Every coefficient of the canonical formal `α`-power is strictly positive
when `0 < q ≤ 1` and `α > 0`. -/
theorem coeff_pos (q α : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hα : 0 < α) (n : ℕ) : 0 < coeff q α n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ m =>
          rw [coeff_succ]
          have hnonneg :
              ∀ i ∈ range (m + 1),
                0 ≤ logDerivCoeff q i * coeff q α (m - i) := by
            intro i hi
            exact mul_nonneg (logDerivCoeff_pos q hq hq1 i).le
              (ih (m - i) (Nat.lt_succ_of_le (Nat.sub_le m i))).le
          have hsum :
              0 < Finset.sum (range (m + 1))
                (fun i => logDerivCoeff q i * coeff q α (m - i)) := by
            rw [sum_pos_iff_of_nonneg hnonneg]
            refine ⟨0, by simp, ?_⟩
            simpa using mul_pos (logDerivCoeff_pos q hq hq1 0)
              (ih m (Nat.lt_succ_self m))
          have hden : 0 < (m + 1 : ℚ) := by positivity
          exact div_pos (mul_pos hα hsum) hden

noncomputable def series (q α : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (coeff q α)

noncomputable def logDerivSeries (q : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (logDerivCoeff q)

/-- The parameterized positive series satisfies its defining logarithmic
first-order differential equation. -/
theorem series_derivative (q α : ℚ) :
    PowerSeries.derivative ℚ (series q α) =
      PowerSeries.C α * (logDerivSeries q * series q α) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [series, logDerivSeries, PowerSeries.coeff_mk]
  rw [coeff_succ]
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  field_simp

/-- Publication-facing form of the parameterized positivity theorem. -/
theorem digitalEulerPower_coeff_pos
    (q α : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (hα : 0 < α) (n : ℕ) :
    0 < PowerSeries.coeff n (series q α) := by
  simp only [series, PowerSeries.coeff_mk]
  exact coeff_pos q α hq hq1 hα n

end DigitalEulerPositivity
