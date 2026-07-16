import Mathlib
import Mathlib.Data.Nat.EvenOddRec

open Nat Finset

noncomputable def A005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2^k)

noncomputable def A046644 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ (2 : ℚ) ^ (A005187 e)

noncomputable def A317940_f : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if n = 0 then 0
    else if n = 1 then 1
    else
      let A_n : ℚ := A046644 n
      let sum_of_products : ℚ := Finset.sum (divisors n) fun d ↦
        if h_prop : d > 1 ∧ d < n then
          have d_lt_n : d < n := h_prop.2
          let q := n / d
          have q_lt_n : q < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h_prop.1
          IH d d_lt_n * IH q q_lt_n
        else 0
      (A_n - sum_of_products) / 2

namespace A317940Verified

def ExactSpec : Prop := ∀ n : ℕ, n > 0 → A317940_f n ≥ 0

noncomputable def d : ℕ → ℚ :=
  Nat.evenOddRec (1 / 2)
    (fun r _ => 1 / (2 : ℚ) ^ (2 * r + 1))
    (fun r x => 2 * x - 1 / (2 : ℚ) ^ (2 * r + 2))

@[simp] theorem d_zero : d 0 = 1 / 2 := by sorry

@[simp] theorem d_even (r : ℕ) :
    d (2 * r) = 1 / (2 : ℚ) ^ (2 * r + 1) := by sorry

@[simp] theorem d_odd (r : ℕ) :
    d (2 * r + 1) = 2 * d r - 1 / (2 : ℚ) ^ (2 * r + 2) := by sorry

theorem d_lower : ∀ n : ℕ, 1 / (2 : ℚ) ^ (n + 1) ≤ d n := by sorry

theorem d_pos (n : ℕ) : 0 < d n := by sorry

noncomputable def a : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    match n with
    | 0 => 1
    | m + 1 =>
        Finset.sum (range (m + 1))
            (fun i => d i * IH (m - i) (Nat.lt_succ_of_le (Nat.sub_le m i))) /
          (2 * (m + 1))

@[simp] theorem a_zero : a 0 = 1 := by sorry

theorem a_succ (m : ℕ) :
    a (m + 1) =
      Finset.sum (range (m + 1)) (fun i => d i * a (m - i)) /
        (2 * (m + 1)) := by sorry

theorem a_pos (n : ℕ) : 0 < a n := by sorry

noncomputable def b : ℕ → ℚ :=
  Nat.evenOddRec 1
    (fun _ x => x)
    (fun _ x => x / 2)

@[simp] theorem b_zero : b 0 = 1 := by sorry

@[simp] theorem b_even (r : ℕ) : b (2 * r) = b r := by sorry

@[simp] theorem b_odd (r : ℕ) : b (2 * r + 1) = b r / 2 := by sorry

theorem b_pos (n : ℕ) : 0 < b n := by sorry

theorem sum_range_even_odd_even (f : ℕ → ℚ) (m : ℕ) :
    Finset.sum (range (2 * m + 1)) f =
      Finset.sum (range (m + 1)) (fun r => f (2 * r)) +
      Finset.sum (range m) (fun r => f (2 * r + 1)) := by sorry

theorem sum_range_even_odd_odd (f : ℕ → ℚ) (m : ℕ) :
    Finset.sum (range (2 * m + 2)) f =
      Finset.sum (range (m + 1)) (fun r => f (2 * r)) +
      Finset.sum (range (m + 1)) (fun r => f (2 * r + 1)) := by sorry

theorem geometric_shift (m : ℕ) :
    Finset.sum (range (m + 1))
        (fun r => 1 / (2 : ℚ) ^ (2 * r + 1) * b (m - r)) =
      b m / 2 +
        Finset.sum (range m)
          (fun r => 1 / (2 : ℚ) ^ (2 * r + 3) * b (m - r - 1)) := by sorry

theorem b_derivative_coeff (n : ℕ) :
    (n + 1 : ℚ) * b (n + 1) =
      Finset.sum (range (n + 1)) (fun i => d i * b (n - i)) := by sorry

noncomputable def Aseries : PowerSeries ℚ := PowerSeries.mk a
noncomputable def Dseries : PowerSeries ℚ := PowerSeries.mk d
noncomputable def Qseries : PowerSeries ℚ := Aseries * Aseries

theorem Aseries_derivative :
    PowerSeries.derivative ℚ Aseries =
      PowerSeries.C (1 / 2 : ℚ) * (Dseries * Aseries) := by sorry

theorem Qseries_derivative :
    PowerSeries.derivative ℚ Qseries = Dseries * Qseries := by sorry

end A317940Verified
