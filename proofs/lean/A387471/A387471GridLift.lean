import A387471FiniteBridge
import A387471Ratio

/-!
# Lifting Mann divisibility to the finite angle grid
-/

namespace A387471

/-- Encode an integer in `[-14,14]` as a member of `Fin 29`. -/
def fin29OfInt (q : ℤ) (hlo : -14 ≤ q) (hhi : q ≤ 14) : Fin 29 :=
  ⟨(q + 14).toNat, by omega⟩

@[simp] lemma angleInt_fin29OfInt (q : ℤ) (hlo : -14 ≤ q) (hhi : q ≤ 14) :
    angleInt (fin29OfInt q hlo hhi) = q := by
  simp [angleInt, fin29OfInt, Int.toNat_of_nonneg (by omega : 0 ≤ q + 14)]

/-- The coefficient bound `|A|<3n` makes the quotient `5A/n` lie in `[-14,14]`. -/
lemma quotient_bounds {n : ℕ} (hn : 0 < n) {A q : ℤ}
    (hlo : -3 * (n : ℤ) < A) (hhi : A < 3 * (n : ℤ))
    (hq : 5 * A = (n : ℤ) * q) : -14 ≤ q ∧ q ≤ 14 := by
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  constructor <;> nlinarith

/-- Pair-sum bounds descend to the strict finite-grid bound. -/
lemma quotient_pair_bound {n : ℕ} (hn : 0 < n) {A B qA qB : ℤ}
    (hlo : -2 * (n : ℤ) < A + B) (hhi : A + B < 2 * (n : ℤ))
    (hA : 5 * A = (n : ℤ) * qA) (hB : 5 * B = (n : ℤ) * qB) :
    |qA + qB| < 10 := by
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  rw [abs_lt]
  constructor <;> nlinarith

/-- The quotient equation identifies the original lattice angle with the
corresponding `π/30` grid angle. -/
lemma latticeAngle_eq_angleReal {n : ℕ} (hn : 0 < n) {A q : ℤ}
    (hq : 5 * A = (n : ℤ) * q)
    (hlo : -14 ≤ q) (hhi : q ≤ 14) :
    latticeAngle n A = angleReal (fin29OfInt q hlo hhi) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hqR : 5 * (A : ℝ) = (n : ℝ) * (q : ℝ) := by exact_mod_cast hq
  simp [latticeAngle, angleReal]
  field_simp [hn0]
  nlinarith

/-- An ordinary finite-grid pattern lifts back to a permutation of `(0,s,-s)`. -/
lemma ordinaryGrid_to_ABC {n A B C qA qB qC : ℤ} (hn : n ≠ 0)
    (hA : 5 * A = n * qA) (hB : 5 * B = n * qB) (hC : 5 * C = n * qC)
    (hord : ordinaryGrid qA qB qC) :
    ∃ s : ℤ, Perm3 A B C 0 s (-s) := by
  rcases hord with ⟨hqA, hqBC⟩ | ⟨hqB, hqAC⟩ | ⟨hqC, hqAB⟩
  · subst qA
    have hAz : A = 0 := by nlinarith
    have h5BC : 5 * (B + C) = 0 := by
      calc
        5 * (B + C) = 5 * B + 5 * C := by ring
        _ = n * qB + n * qC := by rw [hB, hC]
        _ = 0 := by rw [hqBC]; ring
    have hBC : B = -C := by nlinarith
    refine ⟨B, ?_⟩
    simp [Perm3, hAz, hBC]
  · subst qB
    have hBz : B = 0 := by nlinarith
    have h5AC : 5 * (A + C) = 0 := by
      calc
        5 * (A + C) = 5 * A + 5 * C := by ring
        _ = n * qA + n * qC := by rw [hA, hC]
        _ = 0 := by rw [hqAC]; ring
    have hAC : A = -C := by nlinarith
    refine ⟨A, ?_⟩
    simp [Perm3, hBz, hAC]
  · subst qC
    have hCz : C = 0 := by nlinarith
    have h5AB : 5 * (A + B) = 0 := by
      calc
        5 * (A + B) = 5 * A + 5 * B := by ring
        _ = n * qA + n * qB := by rw [hA, hB]
        _ = 0 := by rw [hqAB]; ring
    have hAB : A = -B := by nlinarith
    refine ⟨A, ?_⟩
    simp [Perm3, hCz, hAB]

lemma five_dvd_of_five_mul_eq_three_mul {x n : ℤ} (h : 5 * x = 3 * n) :
    (5 : ℤ) ∣ n := by
  have hd : (5 : ℤ) ∣ 3 * n := ⟨x, h.symm⟩
  rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp hd with h53 | h5n
  · norm_num at h53
  · exact h5n

lemma five_dvd_of_five_mul_eq_neg_three_mul {x n : ℤ} (h : 5 * x = -3 * n) :
    (5 : ℤ) ∣ n := by
  have hd : (5 : ℤ) ∣ 3 * n := ⟨-x, by nlinarith⟩
  rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp hd with h53 | h5n
  · norm_num at h53
  · exact h5n

set_option maxHeartbeats 0 in
/-- Either exceptional finite-grid pattern lifts to the exact exceptional ABC family. -/
lemma exceptionalGrid_to_ABC {n A B C qA qB qC : ℤ}
    (hA : 5 * A = n * qA) (hB : 5 * B = n * qB) (hC : 5 * C = n * qC)
    (hexc : exceptionalGrid qA qB qC) : ExceptionalABC n A B C := by
  rcases hexc with hexc | hexc
  · rcases hexc with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_neg_three_mul (by nlinarith : 5 * B = -3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inl ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_neg_three_mul (by nlinarith : 5 * C = -3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inl ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_neg_three_mul (by nlinarith : 5 * A = -3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inl ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_neg_three_mul (by nlinarith : 5 * A = -3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inl ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_neg_three_mul (by nlinarith : 5 * B = -3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inl ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_neg_three_mul (by nlinarith : 5 * C = -3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inl ?_⟩
      simp only [Perm3]
      omega
  · rcases hexc with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_three_mul (by nlinarith : 5 * B = 3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inr ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_three_mul (by nlinarith : 5 * C = 3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inr ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_three_mul (by nlinarith : 5 * A = 3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inr ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_three_mul (by nlinarith : 5 * A = 3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inr ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_three_mul (by nlinarith : 5 * B = 3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inr ?_⟩
      simp only [Perm3]
      omega
    · have h5n : (5 : ℤ) ∣ n := five_dvd_of_five_mul_eq_three_mul (by nlinarith : 5 * C = 3 * n)
      rcases h5n with ⟨q, hq⟩
      refine ⟨q, by omega, Or.inr ?_⟩
      simp only [Perm3]
      omega

/-- The finite classification lifts uniformly to `ABCClassified`. -/
lemma classifiedGrid_to_ABC {n A B C qA qB qC : ℤ} (hn : n ≠ 0)
    (hA : 5 * A = n * qA) (hB : 5 * B = n * qB) (hC : 5 * C = n * qC)
    (hclass : classifiedGrid qA qB qC) : ABCClassified n A B C := by
  rcases hclass with hord | hexc
  · exact Or.inl (ordinaryGrid_to_ABC hn hA hB hC hord)
  · exact Or.inr (exceptionalGrid_to_ABC hA hB hC hexc)

#print axioms quotient_bounds
#print axioms quotient_pair_bound
#print axioms classifiedGrid_to_ABC

end A387471