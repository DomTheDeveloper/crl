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
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  simp only [Nat.sub_zero]
  rw [div_eq_mul_inv]
  ring

theorem b_derivative_coeff (n : ℕ) :
    (n + 1 : ℚ) * b (n + 1) =
      Finset.sum (range (n + 1)) (fun i => d i * b (n - i)) := by
  induction n using Nat.evenOddStrongRec with
  | h_odd m ih =>
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, b_even]
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, sum_range_even_odd_odd]
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
      push_cast
      ring
  | h_even M ih =>
      cases M with
      | zero =>
          have hb1 : b 1 = 1 / 2 := by simpa using b_odd 0
          norm_num [hb1, d_zero, b_zero]
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
          have hshift :
              Finset.sum (range (m + 1))
                  (fun r => 1 / (2 : ℚ) ^ (2 * r + 3) * b (m + 1 - r - 1)) =
                Finset.sum (range (m + 1))
                  (fun r => 1 / (2 : ℚ) ^ (2 * r + 3) * b (m - r)) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [show m + 1 - r - 1 = m - r by omega]
          rw [hshift]
          have him := ih m (by omega)
          rw [← him]
          push_cast
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
    cases n with
    | zero => norm_num
    | succ n => simp
  calc
    Aseries * (PowerSeries.C (1 / 2 : ℚ) * (Dseries * Aseries)) +
        Aseries * (PowerSeries.C (1 / 2 : ℚ) * (Dseries * Aseries)) =
      ((PowerSeries.C (1 / 2 : ℚ) : PowerSeries ℚ) +
        PowerSeries.C (1 / 2 : ℚ)) * (Dseries * (Aseries * Aseries)) := by ring
    _ = Dseries * (Aseries * Aseries) := by rw [hC, one_mul]

noncomputable def Bseries : PowerSeries ℚ := PowerSeries.mk b

theorem Bseries_derivative :
    PowerSeries.derivative ℚ Bseries = Dseries * Bseries := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Bseries, Dseries, PowerSeries.coeff_mk]
  simpa [mul_comm] using b_derivative_coeff n

theorem Qseries_constant : PowerSeries.constantCoeff Qseries = 1 := by
  simp [Qseries, Aseries, a_zero]

theorem Bseries_constant : PowerSeries.constantCoeff Bseries = 1 := by
  simp [Bseries, b_zero]

theorem ode_unique (F G : PowerSeries ℚ)
    (hF : PowerSeries.derivative ℚ F = Dseries * F)
    (hG : PowerSeries.derivative ℚ G = Dseries * G)
    (h0 : PowerSeries.constantCoeff F = PowerSeries.constantCoeff G) :
    F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
      | succ m =>
          have hFc := congrArg (PowerSeries.coeff m) hF
          have hGc := congrArg (PowerSeries.coeff m) hG
          rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hFc hGc
          have hs :
              Finset.sum (range (m + 1))
                  (fun i => PowerSeries.coeff i Dseries *
                    PowerSeries.coeff (m - i) F) =
                Finset.sum (range (m + 1))
                  (fun i => PowerSeries.coeff i Dseries *
                    PowerSeries.coeff (m - i) G) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            exact ih (m - i) (Nat.lt_succ_of_le (Nat.sub_le m i))
          rw [hs] at hFc
          have hmul :
              PowerSeries.coeff (m + 1) F * (m + 1 : ℚ) =
                PowerSeries.coeff (m + 1) G * (m + 1 : ℚ) :=
            hFc.trans hGc.symm
          exact mul_right_cancel₀ (by positivity) hmul

theorem Qseries_eq_Bseries : Qseries = Bseries := by
  apply ode_unique Qseries Bseries Qseries_derivative Bseries_derivative
  rw [Qseries_constant, Bseries_constant]

theorem A005187_rec (n : ℕ) :
    A005187 n = n + A005187 (n / 2) := by
  cases n with
  | zero => simp [A005187]
  | succ n =>
      unfold A005187
      rw [Finset.sum_range_succ', add_comm]
      simp only [pow_zero, Nat.div_one]
      congr 1
      have hterm (k : ℕ) :
          (n + 1) / 2 ^ (k + 1) = ((n + 1) / 2) / 2 ^ k := by
        symm
        rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]
      simp_rw [hterm]
      let q := (n + 1) / 2
      have hq_lt : q < n + 1 := by
        dsimp [q]
        exact Nat.div_lt_self (by omega) (by omega)
      have hsubset : range (q + 1) ⊆ range (n + 1) := by
        intro k hk
        simp only [Finset.mem_range] at hk ⊢
        omega
      symm
      apply Finset.sum_subset hsubset
      intro k hk_big hk_small
      have hk_lt : k < n + 1 := Finset.mem_range.mp hk_big
      have hk_ge : q + 1 ≤ k := by
        by_contra h
        have : k < q + 1 := by omega
        exact hk_small (Finset.mem_range.mpr this)
      have hqk : q < k := by omega
      have hkpow : k < 2 ^ k := Nat.lt_two_pow_self
      have hqpow : q < 2 ^ k := lt_trans hqk hkpow
      exact Nat.div_eq_of_lt hqpow

theorem four_pow_mul_b (n : ℕ) :
    (4 : ℚ) ^ n * b n = (2 : ℚ) ^ (A005187 n) := by
  have h4 (r : ℕ) : (4 : ℚ) ^ r = (2 : ℚ) ^ (2 * r) := by
    calc
      (4 : ℚ) ^ r = ((2 : ℚ) ^ 2) ^ r := by norm_num
      _ = (2 : ℚ) ^ (2 * r) := by rw [pow_mul]
  induction n using Nat.evenOddRec with
  | h0 => norm_num [A005187, b_zero]
  | h_even r ih =>
      rw [b_even, A005187_rec, show 2 * r / 2 = r by omega]
      calc
        (4 : ℚ) ^ (2 * r) * b r =
            (4 : ℚ) ^ r * ((4 : ℚ) ^ r * b r) := by
              rw [show 2 * r = r + r by omega, pow_add]
              ring
        _ = (4 : ℚ) ^ r * (2 : ℚ) ^ (A005187 r) := by rw [ih]
        _ = (2 : ℚ) ^ (2 * r) * (2 : ℚ) ^ (A005187 r) := by rw [h4]
        _ = (2 : ℚ) ^ (2 * r + A005187 r) :=
          (pow_add (2 : ℚ) (2 * r) (A005187 r)).symm
  | h_odd r ih =>
      rw [b_odd, A005187_rec, show (2 * r + 1) / 2 = r by omega]
      calc
        (4 : ℚ) ^ (2 * r + 1) * (b r / 2) =
            (2 : ℚ) ^ (2 * r + 1) * ((4 : ℚ) ^ r * b r) := by
              rw [show 2 * r + 1 = r + r + 1 by omega,
                pow_add, pow_add, h4]
              ring
        _ = (2 : ℚ) ^ (2 * r + 1) * (2 : ℚ) ^ (A005187 r) := by rw [ih]
        _ = (2 : ℚ) ^ (2 * r + 1 + A005187 r) :=
          (pow_add (2 : ℚ) (2 * r + 1) (A005187 r)).symm

noncomputable def c (n : ℕ) : ℚ := (4 : ℚ) ^ n * a n

theorem c_pos (n : ℕ) : 0 < c n := by
  exact mul_pos (pow_pos (by norm_num) n) (a_pos n)

noncomputable def Cseries : PowerSeries ℚ := PowerSeries.rescale 4 Aseries

theorem Cseries_sq_eq :
    Cseries * Cseries = PowerSeries.rescale 4 Bseries := by
  unfold Cseries
  rw [← map_mul]
  change PowerSeries.rescale 4 Qseries = PowerSeries.rescale 4 Bseries
  rw [Qseries_eq_Bseries]

theorem c_convolution (n : ℕ) :
    Finset.sum (range (n + 1)) (fun i => c i * c (n - i)) =
      (2 : ℚ) ^ (A005187 n) := by
  have h := congrArg (PowerSeries.coeff n) Cseries_sq_eq
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_rescale] at h
  simp only [Cseries, Aseries, Bseries, PowerSeries.coeff_rescale,
    PowerSeries.coeff_mk] at h
  exact h.trans (four_pow_mul_b n)

@[simp] theorem c_zero : c 0 = 1 := by
  simp [c]

noncomputable def rootAF : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod fun _ e => c e, by simp⟩

noncomputable def targetAF : ArithmeticFunction ℚ :=
  ⟨A046644, by simp [A046644]⟩

@[simp] theorem targetAF_apply (n : ℕ) : targetAF n = A046644 n := rfl

@[simp] theorem rootAF_prime_pow {p e : ℕ} (hp : p.Prime) :
    rootAF (p ^ e) = c e := by
  simp [rootAF, hp.ne_zero, hp.factorization_pow, c_zero]

@[simp] theorem targetAF_prime_pow {p e : ℕ} (hp : p.Prime) :
    targetAF (p ^ e) = (2 : ℚ) ^ (A005187 e) := by
  have hzero : (2 : ℚ) ^ (A005187 0) = 1 := by simp [A005187]
  simp [targetAF, A046644, hp.ne_zero, hp.factorization_pow,
    Finsupp.prod_single_index, hzero]

theorem rootAF_multiplicative : rootAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [rootAF]
  · intro m n hm hn hcop
    change (if m * n = 0 then 0 else
        (m * n).factorization.prod fun _ e => c e) =
      (if m = 0 then 0 else m.factorization.prod fun _ e => c e) *
        (if n = 0 then 0 else n.factorization.prod fun _ e => c e)
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn,
      Nat.factorization_mul_of_coprime hcop,
      ← Finsupp.prod_add_index_of_disjoint]
    exact hcop.disjoint_primeFactors

theorem targetAF_multiplicative : targetAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [targetAF, A046644]
  · intro m n hm hn hcop
    change (if m * n = 0 then 0 else
        (m * n).factorization.prod fun _ e => (2 : ℚ) ^ (A005187 e)) =
      (if m = 0 then 0 else
          m.factorization.prod fun _ e => (2 : ℚ) ^ (A005187 e)) *
        (if n = 0 then 0 else
          n.factorization.prod fun _ e => (2 : ℚ) ^ (A005187 e))
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn,
      Nat.factorization_mul_of_coprime hcop,
      ← Finsupp.prod_add_index_of_disjoint]
    exact hcop.disjoint_primeFactors

theorem mul_apply_divisors (f g : ArithmeticFunction ℚ) (n : ℕ) :
    (f * g) n =
      Finset.sum (divisors n) (fun d => f d * g (n / d)) := by
  rw [ArithmeticFunction.mul_apply, ← Nat.map_div_right_divisors,
    Finset.sum_map, Function.Embedding.coeFn_mk]

theorem rootAF_sq_prime_pow {p e : ℕ} (hp : p.Prime) :
    (rootAF * rootAF) (p ^ e) = (2 : ℚ) ^ (A005187 e) := by
  rw [mul_apply_divisors, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  calc
    Finset.sum (range (e + 1))
        (fun j => rootAF (p ^ j) * rootAF (p ^ e / p ^ j)) =
      Finset.sum (range (e + 1))
        (fun j => c j * c (e - j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hje : j ≤ e := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hdiv : p ^ e / p ^ j = p ^ (e - j) := by
            apply Nat.div_eq_of_eq_mul_left
            · exact pow_pos hp.pos j
            · rw [← pow_add]
              congr 1
              omega
          rw [rootAF_prime_pow hp, hdiv, rootAF_prime_pow hp]
    _ = (2 : ℚ) ^ (A005187 e) := c_convolution e

theorem rootAF_sq_eq_target : rootAF * rootAF = targetAF := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      (rootAF * rootAF)
      (rootAF_multiplicative.mul rootAF_multiplicative)
      targetAF targetAF_multiplicative).2
  intro p e hp
  rw [rootAF_sq_prime_pow hp, targetAF_prime_pow hp]

noncomputable def interiorSum (f : ArithmeticFunction ℚ) (n : ℕ) : ℚ :=
  Finset.sum (divisors n) fun d =>
    if d > 1 ∧ d < n then f d * f (n / d) else 0

theorem square_decomp (f : ArithmeticFunction ℚ)
    (hf1 : f 1 = 1) {n : ℕ} (hn : 1 < n) :
    (f * f) n = 2 * f n + interiorSum f n := by
  rw [mul_apply_divisors]
  have hn0 : n ≠ 0 := by omega
  calc
    Finset.sum (divisors n) (fun d => f d * f (n / d)) =
        Finset.sum (divisors n) (fun d =>
          (if d = 1 then f n else 0) +
          (if d = n then f n else 0) +
          (if d > 1 ∧ d < n then f d * f (n / d) else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hdle : d ≤ n := Nat.divisor_le hd
      by_cases h1 : d = 1
      · subst d
        have hne : (1 : ℕ) ≠ n := _root_.ne_of_lt hn
        simp [hf1, hne]
      by_cases hdn : d = n
      · subst d
        rw [Nat.div_self (by omega), hf1]
        simp [h1]
      have hgt : 1 < d := by omega
      have hlt : d < n := lt_of_le_of_ne hdle hdn
      simp [h1, hdn, hgt, hlt]
    _ = 2 * f n + interiorSum f n := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp [interiorSum, hn0]
      ring

theorem rootAF_rec {n : ℕ} (hn : 1 < n) :
    rootAF n = (A046644 n - interiorSum rootAF n) / 2 := by
  have hsquare := congrArg (fun F : ArithmeticFunction ℚ => F n) rootAF_sq_eq_target
  change (rootAF * rootAF) n = A046644 n at hsquare
  rw [square_decomp rootAF rootAF_multiplicative.map_one hn] at hsquare
  linarith

theorem A317940_f_unfold (n : ℕ) :
    A317940_f n =
      if n = 0 then 0
      else if n = 1 then 1
      else
        let A_n : ℚ := A046644 n
        let sum_of_products : ℚ := Finset.sum (divisors n) fun d =>
          if _h_prop : d > 1 ∧ d < n then
            A317940_f d * A317940_f (n / d)
          else 0
        (A_n - sum_of_products) / 2 := by
  unfold A317940_f
  rw [WellFounded.fix_eq]

theorem A317940_f_eq_rootAF (n : ℕ) : A317940_f n = rootAF n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [A317940_f_unfold]
      by_cases h0 : n = 0
      · subst n
        simp [rootAF]
      by_cases h1 : n = 1
      · subst n
        rw [if_neg (by omega), if_pos rfl]
        exact rootAF_multiplicative.map_one.symm
      have hn : 1 < n := by omega
      rw [if_neg h0, if_neg h1]
      have hsum :
          Finset.sum (divisors n) (fun d =>
            if _h_prop : d > 1 ∧ d < n then
              A317940_f d * A317940_f (n / d)
            else 0) = interiorSum rootAF n := by
        unfold interiorSum
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hp : d > 1 ∧ d < n
        · rw [dif_pos hp, if_pos hp, ih d hp.2]
          have hq : n / d < n :=
            Nat.div_lt_self (Nat.pos_of_ne_zero h0) hp.1
          rw [ih (n / d) hq]
        · rw [dif_neg hp, if_neg hp]
      rw [hsum]
      exact (rootAF_rec hn).symm

theorem rootAF_pos {n : ℕ} (hn : 0 < n) : 0 < rootAF n := by
  change 0 < (if n = 0 then 0 else
    n.factorization.prod fun _ e => c e)
  rw [if_neg hn.ne']
  unfold Finsupp.prod
  apply Finset.prod_pos
  intro p hp
  exact c_pos _

theorem A317940_nonnegative (n : ℕ) (hn : n > 0) :
    A317940_f n ≥ 0 := by
  rw [A317940_f_eq_rootAF]
  exact le_of_lt (rootAF_pos hn)

theorem exact_spec_verified : ExactSpec := by
  intro n hn
  exact A317940_nonnegative n hn

end A317940Verified


theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) :
    A317940_f n ≥ 0 :=
  A317940Verified.A317940_nonnegative n h

-- CI axiom audit: this prints the axiom dependencies during `lake build`.
-- A clean result is exactly [propext, Classical.choice, Quot.sound] — i.e. the
-- three standard Mathlib axioms and no proof-placeholder axiom.
#print axioms A317940_f_nonnegative
