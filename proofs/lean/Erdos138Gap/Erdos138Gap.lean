import APNOutputs.ErdosProblems.erdos_138.variants.difference

open Nat Filter

namespace Erdos138

/--
The one-step greedy extension remains valid at the endpoint `i = k`.
The upstream proof assumes `i < k`; inspecting its arithmetic shows that
`i ≤ k` is sufficient.
-/
lemma extend_one_step_le (k i N : ℕ) (c : ℕ → Fin 2)
    (hk : k > 0)
    (hi : i ≤ k)
    (h_no_ap_k : ¬ HasMonoAP c N k)
    (h_no_ap_k1 : ¬ HasMonoAP c (N + i) (k + 1)) :
    ∃ color : Fin 2,
      ¬ HasMonoAP (fun x => if x = N + i + 1 then color else c x)
        (N + i + 1) (k + 1) := by
  by_contra h_contra
  push_neg at h_contra
  have h0 := h_contra 0
  have h1 := h_contra 1
  have h_ap0 := ap_must_end k i N c 0 h_no_ap_k1 h0
  have h_ap1 := ap_must_end k i N c 1 h_no_ap_k1 h1
  rcases h_ap0 with ⟨a0, d0, hd0, ha0_1, ha0_eq, h_mono0⟩
  rcases h_ap1 with ⟨a1, d1, hd1, ha1_1, ha1_eq, h_mono1⟩

  have hd0_bound : d0 ≤ i := by
    by_contra h_gt
    push_neg at h_gt
    have h_mul : (k - 1) * d0 = k * d0 - d0 := by
      have h1 : (k - 1) * d0 = k * d0 - 1 * d0 := Nat.sub_mul k 1 d0
      have h2 : 1 * d0 = d0 := Nat.one_mul d0
      rw [h2] at h1
      exact h1
    have h_le : a0 + (k - 1) * d0 ≤ N := by
      rw [h_mul]
      have h_k_d0 : d0 ≤ k * d0 := by
        have : 1 * d0 ≤ k * d0 := Nat.mul_le_mul_right d0 hk
        omega
      have h_add : a0 + (k * d0 - d0) = a0 + k * d0 - d0 := by omega
      rw [h_add, ha0_eq]
      omega
    have h_ap : HasMonoAP c N k := by
      use a0, d0
      have h_c_a0 : c a0 = 0 := by
        have h0_lt : 0 < k := hk
        have h_eval := h_mono0 0 h0_lt
        have h_zero : a0 + 0 * d0 = a0 := by omega
        rwa [h_zero] at h_eval
      have h_mono_ap : ∀ m < k, c (a0 + m * d0) = c a0 := by
        intro m hm
        have h1 := h_mono0 m hm
        rw [h1, h_c_a0]
      exact ⟨hd0, ha0_1, h_le, h_mono_ap⟩
    exact h_no_ap_k h_ap

  have hd1_bound : d1 ≤ i := by
    by_contra h_gt
    push_neg at h_gt
    have h_mul : (k - 1) * d1 = k * d1 - d1 := by
      have h1 : (k - 1) * d1 = k * d1 - 1 * d1 := Nat.sub_mul k 1 d1
      have h2 : 1 * d1 = d1 := Nat.one_mul d1
      rw [h2] at h1
      exact h1
    have h_le : a1 + (k - 1) * d1 ≤ N := by
      rw [h_mul]
      have h_k_d1 : d1 ≤ k * d1 := by
        have : 1 * d1 ≤ k * d1 := Nat.mul_le_mul_right d1 hk
        omega
      have h_add : a1 + (k * d1 - d1) = a1 + k * d1 - d1 := by omega
      rw [h_add, ha1_eq]
      omega
    have h_ap : HasMonoAP c N k := by
      use a1, d1
      have h_c_a1 : c a1 = 1 := by
        have h0_lt : 0 < k := hk
        have h_eval := h_mono1 0 h0_lt
        have h_zero : a1 + 0 * d1 = a1 := by omega
        rwa [h_zero] at h_eval
      have h_mono_ap : ∀ m < k, c (a1 + m * d1) = c a1 := by
        intro m hm
        have h1_eval := h_mono1 m hm
        rw [h1_eval, h_c_a1]
      exact ⟨hd1, ha1_1, h_le, h_mono_ap⟩
    exact h_no_ap_k h_ap

  have hd0_le_k : d0 ≤ k := hd0_bound.trans hi
  have hd1_le_k : d1 ≤ k := hd1_bound.trans hi
  have h_m0 : k - d1 < k := by omega
  have h_m1 : k - d0 < k := by omega

  have h_z0 : c (a0 + (k - d1) * d0) = 0 := h_mono0 (k - d1) h_m0
  have h_z1 : c (a1 + (k - d0) * d1) = 1 := h_mono1 (k - d0) h_m1

  have h_eq_z : a0 + (k - d1) * d0 = a1 + (k - d0) * d1 := by
    have h_sub0 : a0 + (k - d1) * d0 = a0 + k * d0 - d1 * d0 := by
      have hsub : (k - d1) * d0 = k * d0 - d1 * d0 := Nat.sub_mul k d1 d0
      rw [hsub]
      have : d1 * d0 ≤ k * d0 := Nat.mul_le_mul_right d0 hd1_le_k
      omega
    have h_sub1 : a1 + (k - d0) * d1 = a1 + k * d1 - d0 * d1 := by
      have hsub : (k - d0) * d1 = k * d1 - d0 * d1 := Nat.sub_mul k d0 d1
      rw [hsub]
      have : d0 * d1 ≤ k * d1 := Nat.mul_le_mul_right d1 hd0_le_k
      omega
    have h_comm : d1 * d0 = d0 * d1 := Nat.mul_comm d1 d0
    rw [h_sub0, h_sub1, ha0_eq, ha1_eq, h_comm]

  rw [h_eq_z] at h_z0
  rw [h_z0] at h_z1
  contradiction

/-- Extend an extremal `k`-AP-free coloring by `k+1` positions. -/
lemma extend_j_steps_plus_one (k N j : ℕ) (c : ℕ → Fin 2) (hk : k > 0)
    (hj : j ≤ k + 1)
    (h_no_ap_k : ¬ HasMonoAP c N k) :
    ∃ c' : ℕ → Fin 2,
      (∀ x ≤ N, c' x = c x) ∧ ¬ HasMonoAP c' (N + j) (k + 1) := by
  induction j with
  | zero =>
      use c
      refine ⟨fun x hx => rfl, ?_⟩
      by_contra h_ap
      rcases h_ap with ⟨a, d, hd, ha1, had, h_mono⟩
      have h_ap_k : HasMonoAP c N k := by
        use a, d
        have h_k_eq : k + 1 - 1 = k := by omega
        rw [h_k_eq] at had
        have h_zero : N + 0 = N := by omega
        rw [h_zero] at had
        have h_le : a + (k - 1) * d ≤ N := by
          have : a + (k - 1) * d ≤ a + k * d := by
            have : (k - 1) * d ≤ k * d := Nat.mul_le_mul_right d (by omega)
            omega
          omega
        refine ⟨hd, ha1, h_le, ?_⟩
        intro m hm
        have h_m_lt : m < k + 1 := by omega
        exact h_mono m h_m_lt
      exact h_no_ap_k h_ap_k
  | succ j ih =>
      have hj_prev : j ≤ k + 1 := by omega
      rcases ih hj_prev with ⟨cj, h_eq_cj, h_no_ap_cj⟩
      have hj_step : j ≤ k := by omega
      have h_no_ap_k_cj : ¬ HasMonoAP cj N k := by
        intro h_ap
        have h_ap_c : HasMonoAP c N k := by
          have h_eq : ∀ x ≤ N, x ≥ 1 → cj x = c x := fun x hx _ => h_eq_cj x hx
          rw [← has_mono_ap_ext cj c N k h_eq]
          exact h_ap
        exact h_no_ap_k h_ap_c
      have h_ext := extend_one_step_le k j N cj hk hj_step h_no_ap_k_cj h_no_ap_cj
      rcases h_ext with ⟨color, h_no_ap_cj1⟩
      use fun x => if x = N + j + 1 then color else cj x
      refine ⟨?_, ?_⟩
      · intro x hx
        have hx_neq : x ≠ N + j + 1 := by omega
        change (if x = N + j + 1 then color else cj x) = c x
        rw [if_neg hx_neq]
        exact h_eq_cj x hx
      · exact h_no_ap_cj1

/-- A coloring avoiding `k` terms extends by `k+1` points while avoiding `k+1` terms. -/
lemma not_guarantee_extend_plus_one (k N : ℕ) (hk : k > 0) :
    N ∉ monoAP_guarantee_set 2 k →
      (N + (k + 1)) ∉ monoAP_guarantee_set 2 (k + 1) := by
  intro hN
  unfold monoAP_guarantee_set at hN
  simp only [Set.mem_setOf_eq, not_forall] at hN
  rcases hN with ⟨c, hc⟩
  have h_no_ap : ¬ HasMonoAP (extend_coloring N c) N k := by
    intro h_ap
    have h_c_ap := imp_contains_mono_ap N k hk (extend_coloring N c) h_ap
    have h_eq_c : (fun (x : Finset.Icc 1 N) => extend_coloring N c x.1) = c := by
      ext x
      unfold extend_coloring
      have h_in : x.1 ∈ Finset.Icc 1 N := x.2
      rw [dif_pos h_in]
    rw [h_eq_c] at h_c_ap
    exact hc h_c_ap
  have h_ext :=
    extend_j_steps_plus_one k N (k + 1) (extend_coloring N c) hk (by omega) h_no_ap
  rcases h_ext with ⟨c', hc'eq, hc'no⟩
  unfold monoAP_guarantee_set
  simp only [Set.mem_setOf_eq, not_forall]
  use (fun x => c' x.1)
  intro h_cont
  have h_has := contains_mono_ap_imp (N + (k + 1)) (k + 1) (by omega)
    (fun x => c' x.1) h_cont
  have h_ext_eq : ∀ x ≤ N + (k + 1), x ≥ 1 →
      extend_coloring (N + (k + 1)) (fun x => c' x.1) x = c' x := by
    intro x hx h_ge
    unfold extend_coloring
    have h_in : x ∈ Finset.Icc 1 (N + (k + 1)) := by
      rw [Finset.mem_Icc]
      exact ⟨h_ge, hx⟩
    rw [dif_pos h_in]
  have h_has_c' : HasMonoAP c' (N + (k + 1)) (k + 1) := by
    rw [← has_mono_ap_ext
      (extend_coloring (N + (k + 1)) (fun x => c' x.1))
      c' (N + (k + 1)) (k + 1) h_ext_eq]
    exact h_has
  exact hc'no h_has_c'

/-- Strengthened two-color consecutive-gap estimate. -/
theorem W_diff_ge_k_plus_one (k : ℕ) (hk : k > 0) :
    W (k + 1) - W k ≥ k + 1 := by
  by_cases hW : W k = 0
  · have h_not : 0 ∉ monoAP_guarantee_set 2 k := by
      intro h_in
      unfold monoAP_guarantee_set at h_in
      simp only [Set.mem_setOf_eq] at h_in
      have c0 : Finset.Icc 1 0 → Fin 2 := fun _ => 0
      have h_ap := h_in c0
      unfold ContainsMonoAPofLength at h_ap
      rcases h_ap with ⟨color, ap, h_ap_len, _⟩
      unfold Set.IsAPOfLength at h_ap_len
      rcases h_ap_len with ⟨a, d, h_with⟩
      unfold Set.IsAPOfLengthWith at h_with
      rcases h_with with ⟨h_card, h_set⟩
      have h_0_in : a + 0 • d ∈
          {x : ℕ | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} := by
        use 0
        exact ⟨ENat.coe_lt_coe.mpr hk, rfl⟩
      rw [← h_set] at h_0_in
      rcases h_0_in with ⟨x, hx_mem, hx_eq⟩
      have hx_prop := x.property
      rw [Finset.mem_coe, Finset.mem_Icc] at hx_prop
      omega
    have h_ext := not_guarantee_extend_plus_one k 0 hk h_not
    have h_W_gt : 0 + (k + 1) < W (k + 1) :=
      not_in_guarantee_lt_sInf (k + 1) (0 + (k + 1)) h_ext
    omega
  · have h_not := W_not_guarantee k hW
    have h_ext := not_guarantee_extend_plus_one k (W k - 1) hk h_not
    have h_W_gt : W k - 1 + (k + 1) < W (k + 1) :=
      not_in_guarantee_lt_sInf (k + 1) (W k - 1 + (k + 1)) h_ext
    omega

#print axioms Erdos138.W_diff_ge_k_plus_one

end Erdos138
