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

@[simp] theorem d_zero : d 0 = 1 / 2 := by
  simp [d]

@[simp] theorem d_even (r : ℕ) :
    d (2 * r) = 1 / (2 : ℚ) ^ (2 * r + 1) := by
  simp [d, Nat.evenOddRec_even]

@[simp] theorem d_odd (r : ℕ) :
    d (2 * r + 1) = 2 * d r - 1 / (2 : ℚ) ^ (2 * r + 2) := by
  simp [d, Nat.evenOddRec_odd]

theorem d_lower : ∀ n : ℕ, 1 / (2 : ℚ) ^ (n + 1) ≤ d n := by
  intro n
  induction n using Nat.evenOddRec with
  | h0 => norm_num [d]
  | h_even r ih =>
      simp [d_even]
  | h_odd r ih =>
      rw [d_odd]
      have hexp : r + 1 ≤ 2 * r + 2 := by omega
      have hbase :
          1 / (2 : ℚ) ^ (2 * r + 2) ≤ 1 / (2 : ℚ) ^ (r + 1) := by
        exact one_div_pow_le_one_div_pow_of_le (by norm_num) hexp
      have hle : 1 / (2 : ℚ) ^ (2 * r + 2) ≤ d r := hbase.trans ih
      linarith

theorem d_pos (n : ℕ) : 0 < d n := by
  have hpow : 0 < 1 / (2 : ℚ) ^ (n + 1) := by positivity
  exact lt_of_lt_of_le hpow (d_lower n)

noncomputable def a : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    match n with
    | 0 => 1
    | m + 1 =>
        Finset.sum (range (m + 1))
            (fun i => d i * IH (m - i) (Nat.lt_succ_of_le (Nat.sub_le m i))) /
          (2 * (m + 1))

@[simp] theorem a_zero : a 0 = 1 := by
  unfold a
  rw [WellFounded.fix_eq]

theorem a_succ (m : ℕ) :
    a (m + 1) =
      Finset.sum (range (m + 1)) (fun i => d i * a (m - i)) /
        (2 * (m + 1)) := by
  unfold a
  rw [WellFounded.fix_eq]

theorem a_pos (n : ℕ) : 0 < a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ m =>
          rw [a_succ]
          have hnonneg :
              ∀ i ∈ range (m + 1), 0 ≤ d i * a (m - i) := by
            intro i hi
            exact mul_nonneg (le_of_lt (d_pos i))
              (le_of_lt (ih (m - i) (Nat.lt_succ_of_le (Nat.sub_le m i))))
          have hsum :
              0 < Finset.sum (range (m + 1)) (fun i => d i * a (m - i)) := by
            rw [sum_pos_iff_of_nonneg hnonneg]
            refine ⟨0, by simp, ?_⟩
            simpa using mul_pos (d_pos 0) (ih m (Nat.lt_succ_self m))
          have hden : 0 < (2 * (m + 1) : ℚ) := by positivity
          exact div_pos hsum hden

noncomputable def b : ℕ → ℚ :=
  Nat.evenOddRec 1
    (fun _ x => x)
    (fun _ x => x / 2)

@[simp] theorem b_zero : b 0 = 1 := by
  simp [b]

@[simp] theorem b_even (r : ℕ) : b (2 * r) = b r := by
  simp [b, Nat.evenOddRec_even]

@[simp] theorem b_odd (r : ℕ) : b (2 * r + 1) = b r / 2 := by
  simp [b, Nat.evenOddRec_odd]

theorem b_pos (n : ℕ) : 0 < b n := by
  induction n using Nat.evenOddRec with
  | h0 => norm_num [b]
  | h_even r ih => simpa using ih
  | h_odd r ih =>
      rw [b_odd]
      positivity

theorem sum_range_even_odd_even (f : ℕ → ℚ) (m : ℕ) :
    Finset.sum (range (2 * m + 1)) f =
      Finset.sum (range (m + 1)) (fun r => f (2 * r)) +
      Finset.sum (range m) (fun r => f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        Finset.sum (range (2 * (m + 1) + 1)) f =
            Finset.sum (range (2 * m + 1)) f + f (2 * m + 1) + f (2 * m + 2) := by
              rw [show 2 * (m + 1) + 1 = ((2 * m + 1) + 1) + 1 by omega,
                Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (Finset.sum (range (m + 1)) (fun r => f (2 * r)) +
              Finset.sum (range m) (fun r => f (2 * r + 1))) +
              f (2 * m + 1) + f (2 * m + 2) := by rw [ih]
        _ = Finset.sum (range (m + 2)) (fun r => f (2 * r)) +
              Finset.sum (range (m + 1)) (fun r => f (2 * r + 1)) := by
              simp only [Finset.sum_range_succ]
              rw [show 2 * (m + 1) = 2 * m + 2 by omega]
              ring

theorem sum_range_even_odd_odd (f : ℕ → ℚ) (m : ℕ) :
    Finset.sum (range (2 * m + 2)) f =
      Finset.sum (range (m + 1)) (fun r => f (2 * r)) +
      Finset.sum (range (m + 1)) (fun r => f (2 * r + 1)) := by
  have hodd :
      Finset.sum (range (m + 1)) (fun r => f (2 * r + 1)) =
        Finset.sum (range m) (fun r => f (2 * r + 1)) + f (2 * m + 1) := by
    simpa using Finset.sum_range_succ (fun r => f (2 * r + 1)) m
  calc
    Finset.sum (range (2 * m + 2)) f =
        Finset.sum (range (2 * m + 1)) f + f (2 * m + 1) := by
          rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
            Finset.sum_range_succ]
    _ = (Finset.sum (range (m + 1)) (fun r => f (2 * r)) +
          Finset.sum (range m) (fun r => f (2 * r + 1))) + f (2 * m + 1) := by
          rw [sum_range_even_odd_even]
    _ = Finset.sum (range (m + 1)) (fun r => f (2 * r)) +
          Finset.sum (range (m + 1)) (fun r => f (2 * r + 1)) := by
          rw [hodd]
          ring

theorem geometric_shift (m : ℕ) :
    Finset.sum (range (m + 1))
        (fun r => 1 / (2 : ℚ) ^ (2 * r + 1) * b (m - r)) =
      b m / 2 +
        Finset.sum (range m)
          (fun r => 1 / (2 : ℚ) ^ (2 * r + 3) * b (m - r - 1)) := by
  rw [Finset.sum_range_succ']
  congr 1
  · norm_num
  · apply Finset.sum_congr rfl
    intro r hr
    rw [show 2 * (r + 1) + 1 = 2 * r + 3 by omega,
      show m - (r + 1) = m - r - 1 by omega]

theorem b_derivative_coeff (n : ℕ) :
    (n + 1 : ℚ) * b (n + 1) =
      Finset.sum (range (n + 1)) (fun i => d i * b (n - i)) := by
  induction n using Nat.evenOddStrongRec with
  | h_odd m ih =>
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, b_even]
      rw [sum_range_even_odd_odd]
      have heven :
          Finset.sum (range (m + 1))
              (fun r => d (2 * r) * b ((2 * m + 1) - 2 * r)) =
            Finset.sum (range (m + 1))
              (fun r => 1 / (2 : ℚ) ^ (2 * r + 2) * b (m - r)) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrle : r ≤ m := by
          have := Finset.mem_range.mp hr
          omega
        rw [d_even, show 2 * m + 1 - 2 * r = 2 * (m - r) + 1 by omega,
          b_odd, show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ]
        ring
      have hodd :
          Finset.sum (range (m + 1))
              (fun r => d (2 * r + 1) * b ((2 * m + 1) - (2 * r + 1))) =
            Finset.sum (range (m + 1))
              (fun r => (2 * d r - 1 / (2 : ℚ) ^ (2 * r + 2)) * b (m - r)) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrle : r ≤ m := by
          have := Finset.mem_range.mp hr
          omega
        rw [d_odd, show 2 * m + 1 - (2 * r + 1) = 2 * (m - r) by omega,
          b_even]
      rw [heven, hodd]
      have hcancel :
          Finset.sum (range (m + 1))
              (fun r => 1 / (2 : ℚ) ^ (2 * r + 2) * b (m - r)) +
            Finset.sum (range (m + 1))
              (fun r => (2 * d r - 1 / (2 : ℚ) ^ (2 * r + 2)) * b (m - r)) =
            2 * Finset.sum (range (m + 1)) (fun r => d r * b (m - r)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hcancel]
      have him := ih m (by omega)
      rw [← him]
      ring
  | h_even M ih =>
      cases M with
      | zero => norm_num [b, d]
      | succ m =>
          rw [b_odd]
          rw [sum_range_even_odd_even]
          have heven :
              Finset.sum (range (m + 2))
                  (fun r => d (2 * r) * b (2 * (m + 1) - 2 * r)) =
                Finset.sum (range (m + 2))
                  (fun r => 1 / (2 : ℚ) ^ (2 * r + 1) * b (m + 1 - r)) := by
            apply Finset.sum_congr rfl
            intro r hr
            have hrle : r ≤ m + 1 := by
              have := Finset.mem_range.mp hr
              omega
            rw [d_even, show 2 * (m + 1) - 2 * r = 2 * (m + 1 - r) by omega,
              b_even]
          have hodd :
              Finset.sum (range (m + 1))
                  (fun r => d (2 * r + 1) * b (2 * (m + 1) - (2 * r + 1))) =
                Finset.sum (range (m + 1))
                  (fun r => d r * b (m - r) -
                    1 / (2 : ℚ) ^ (2 * r + 3) * b (m - r)) := by
            apply Finset.sum_congr rfl
            intro r hr
            have hrle : r ≤ m := by
              have := Finset.mem_range.mp hr
              omega
            rw [d_odd, show 2 * (m + 1) - (2 * r + 1) = 2 * (m - r) + 1 by omega,
              b_odd, show 2 * r + 3 = (2 * r + 2) + 1 by omega, pow_succ]
            ring
          rw [heven, hodd, geometric_shift, Finset.sum_sub_distrib]
          have him := ih m (by omega)
          rw [← him]
          ring

noncomputable def Aseries : PowerSeries ℚ := PowerSeries.mk a
noncomputable def Dseries : PowerSeries ℚ := PowerSeries.mk d
noncomputable def Qseries : PowerSeries ℚ := Aseries * Aseries

theorem Aseries_derivative :
    PowerSeries.derivative ℚ Aseries =
      PowerSeries.C (1 / 2 : ℚ) * (Dseries * Aseries) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Aseries, Dseries, PowerSeries.coeff_mk]
  rw [a_succ]
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  field_simp

theorem Qseries_derivative :
    PowerSeries.derivative ℚ Qseries = Dseries * Qseries := by
  unfold Qseries
  change PowerSeries.derivativeFun (Aseries * Aseries) =
    Dseries * (Aseries * Aseries)
  rw [PowerSeries.derivativeFun_mul]
  simp only [smul_eq_mul]
  have hA := Aseries_derivative
  change PowerSeries.derivativeFun Aseries =
    PowerSeries.C (1 / 2 : ℚ) * (Dseries * Aseries) at hA
  rw [hA]
  have hC :
      (PowerSeries.C (1 / 2 : ℚ) : PowerSeries ℚ) +
        PowerSeries.C (1 / 2 : ℚ) = 1 := by
    ext n
    cases n <;> simp <;> norm_num
  calc
    Aseries * (PowerSeries.C (1 / 2 : ℚ) * (Dseries * Aseries)) +
        Aseries * (PowerSeries.C (1 / 2 : ℚ) * (Dseries * Aseries)) =
      ((PowerSeries.C (1 / 2 : ℚ) : PowerSeries ℚ) +
        PowerSeries.C (1 / 2 : ℚ)) * (Dseries * (Aseries * Aseries)) := by ring
    _ = Dseries * (Aseries * Aseries) := by rw [hC, one_mul]

end A317940Verified
