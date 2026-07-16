import A387471Pairs
import A387471SineCancel

/-!
# Complete labeled pair classification
-/

namespace A387471

lemma positive_angular_pair_impossible {n : ℕ} (hn : 0 < n) {A B : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (h : Complex.exp ((latticeAngle n A : ℂ) * Complex.I) +
      Complex.exp ((latticeAngle n B : ℂ) * Complex.I) = 0) : False := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply same_side_pair_impossible hn hA hB
  simpa only [canonical_positive_root] using h

lemma negative_angular_pair_impossible {n : ℕ} (hn : 0 < n) {A B : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (h : -Complex.exp (-(latticeAngle n A : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n B : ℂ) * Complex.I) = 0) : False := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hnegA : -3 * (n : ℤ) < -A ∧ -A < 3 * (n : ℤ) := by omega
  have hnegB : -3 * (n : ℤ) < -B ∧ -B < 3 * (n : ℤ) := by omega
  apply same_side_pair_impossible hn hnegA hnegB
  rw [canonical_positive_root (-A), canonical_positive_root (-B)]
  have hangA : latticeAngle n (-A) = -latticeAngle n A := by simp [latticeAngle]
  have hangB : latticeAngle n (-B) = -latticeAngle n B := by simp [latticeAngle]
  rw [hangA, hangB]
  linear_combination -h

lemma mixed_angular_pair_sum_eq_zero {n : ℕ} (hn : 0 < n) {A B : ℤ}
    (hbound : -2 * (n : ℤ) < A + B ∧ A + B < 2 * (n : ℤ))
    (h : Complex.exp ((latticeAngle n A : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n B : ℂ) * Complex.I) = 0) : A + B = 0 := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply mixed_pair_sum_eq_zero hn hbound
  rw [canonical_positive_root A, canonical_negative_root B]
  exact h

lemma ordinary_of_self_pair_A {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0)
    (hpair : Complex.exp ((latticeAngle n A : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n A : ℂ) * Complex.I) = 0) :
    ∃ s : ℤ, Perm3 A B C 0 s (-s) := by
  have hAz := coefficient_eq_zero_of_self_pair hn hA hpair
  subst A
  have hBC : Real.sin (latticeAngle n B) + Real.sin (latticeAngle n C) = 0 := by
    simpa [latticeAngle] using hsin
  have hneg := coefficients_eq_neg_of_sine_add_eq_zero hn hB hC hBC
  refine ⟨B, ?_⟩
  simp [Perm3, hneg]

lemma ordinary_of_self_pair_B {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0)
    (hpair : Complex.exp ((latticeAngle n B : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n B : ℂ) * Complex.I) = 0) :
    ∃ s : ℤ, Perm3 A B C 0 s (-s) := by
  have hBz := coefficient_eq_zero_of_self_pair hn hB hpair
  subst B
  have hAC : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n C) = 0 := by
    simpa [latticeAngle] using hsin
  have hneg := coefficients_eq_neg_of_sine_add_eq_zero hn hA hC hAC
  refine ⟨A, ?_⟩
  simp [Perm3, hneg]

lemma ordinary_of_self_pair_C {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0)
    (hpair : Complex.exp ((latticeAngle n C : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n C : ℂ) * Complex.I) = 0) :
    ∃ s : ℤ, Perm3 A B C 0 s (-s) := by
  have hCz := coefficient_eq_zero_of_self_pair hn hC hpair
  subst C
  have hABs : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) = 0 := by
    simpa [latticeAngle] using hsin
  have hneg := coefficients_eq_neg_of_sine_add_eq_zero hn hA hB hABs
  refine ⟨A, ?_⟩
  simp [Perm3, hneg]

/-- Every vanishing pair of distinct labeled roots forces the ordinary ABC family. -/
theorem labeled_pair_implies_ordinary {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (hAB : -2 * (n : ℤ) < A + B ∧ A + B < 2 * (n : ℤ))
    (hAC : -2 * (n : ℤ) < A + C ∧ A + C < 2 * (n : ℤ))
    (hBC : -2 * (n : ℤ) < B + C ∧ B + C < 2 * (n : ℤ))
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0)
    (r s : Fin 6) (hrs : r ≠ s)
    (hpair : sixRoot n A B C r + sixRoot n A B C s = 0) :
    ∃ t : ℤ, Perm3 A B C 0 t (-t) := by
  fin_cases r <;> fin_cases s
  all_goals simp only [sixRoot] at hpair
  all_goals try {simp at hrs}
  all_goals first
    | exact (positive_angular_pair_impossible hn hA hB hpair).elim
    | exact (positive_angular_pair_impossible hn hA hC hpair).elim
    | exact (positive_angular_pair_impossible hn hB hA hpair).elim
    | exact (positive_angular_pair_impossible hn hB hC hpair).elim
    | exact (positive_angular_pair_impossible hn hC hA hpair).elim
    | exact (positive_angular_pair_impossible hn hC hB hpair).elim
    | exact (negative_angular_pair_impossible hn hA hB hpair).elim
    | exact (negative_angular_pair_impossible hn hA hC hpair).elim
    | exact (negative_angular_pair_impossible hn hB hA hpair).elim
    | exact (negative_angular_pair_impossible hn hB hC hpair).elim
    | exact (negative_angular_pair_impossible hn hC hA hpair).elim
    | exact (negative_angular_pair_impossible hn hC hB hpair).elim
    | exact ordinary_of_self_pair_A hn hA hB hC hsin hpair
    | exact ordinary_of_self_pair_A hn hA hB hC hsin (by simpa [add_comm] using hpair)
    | exact ordinary_of_self_pair_B hn hA hB hC hsin hpair
    | exact ordinary_of_self_pair_B hn hA hB hC hsin (by simpa [add_comm] using hpair)
    | exact ordinary_of_self_pair_C hn hA hB hC hsin hpair
    | exact ordinary_of_self_pair_C hn hA hB hC hsin (by simpa [add_comm] using hpair)
    | exact ordinary_of_AB_cancel hn hC
        (mixed_angular_pair_sum_eq_zero hn hAB hpair) hsin
    | exact ordinary_of_AB_cancel hn hC
        (mixed_angular_pair_sum_eq_zero hn hAB (by simpa [add_comm] using hpair)) hsin
    | exact ordinary_of_AC_cancel hn hB
        (mixed_angular_pair_sum_eq_zero hn hAC hpair) hsin
    | exact ordinary_of_AC_cancel hn hB
        (mixed_angular_pair_sum_eq_zero hn hAC (by simpa [add_comm] using hpair)) hsin
    | exact ordinary_of_BC_cancel hn hA
        (mixed_angular_pair_sum_eq_zero hn hBC hpair) hsin
    | exact ordinary_of_BC_cancel hn hA
        (mixed_angular_pair_sum_eq_zero hn hBC (by simpa [add_comm] using hpair)) hsin

#print axioms labeled_pair_implies_ordinary

end A387471
