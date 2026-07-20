import A387471AngleBounds
import A387471Ratio
import A387471SixRoots

/-!
# Vanishing pairs in the A387471 six-root relation
-/

namespace A387471

lemma ratio_square_eq_one_of_add_eq_zero {x y : ℂ} (hy : y ≠ 0)
    (h : x + y = 0) : (x / y) ^ 2 = 1 := by
  have hxy : x = -y := by linear_combination h
  rw [hxy, neg_div, div_self hy]
  norm_num

/-- Two roots from the same open half of the six-root relation cannot cancel. -/
theorem same_side_pair_impossible {n : ℕ} [NeZero (12 * n)] (hn : 0 < n) {A B : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hpair : canonicalRoot (12 * n) ^ (intResidue (12 * n) A).val +
      canonicalRoot (12 * n) ^ (intResidue (12 * n) B).val = 0) : False := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hroot0 : canonicalRoot (12 * n) ≠ 0 :=
    (canonicalRoot_isPrimitive (mul_ne_zero (by norm_num) hn.ne')).ne_zero
      (mul_ne_zero (by norm_num) hn.ne')
  have hsquare := ratio_square_eq_one_of_add_eq_zero
    (pow_ne_zero _ hroot0) hpair
  have hd := order_dvd_of_canonical_ratio_pow_eq_one
    (N := 12 * n) A B 2 hsquare
  rcases hd with ⟨q, hq⟩
  push_cast at hq
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hdifflo : -6 * (n : ℤ) < A - B := by omega
  have hdiffhi : A - B < 6 * (n : ℤ) := by omega
  have hqlo : -1 < q := by nlinarith
  have hqhi : q < 1 := by nlinarith
  have hqz : q = 0 := by omega
  have hAB : A = B := by nlinarith
  rw [hAB] at hpair
  let z : ℂ := canonicalRoot (12 * n) ^ (intResidue (12 * n) B).val
  have htwoz : (2 : ℂ) * z = 0 := by
    dsimp [z]
    linear_combination hpair
  have hz : z = 0 := (mul_eq_zero.mp htwoz).resolve_left (by norm_num)
  exact (pow_ne_zero _ hroot0) (by simpa [z] using hz)

/-- A mixed positive/negative cancelling pair forces the two angle coefficients
to sum to zero. -/
theorem mixed_pair_sum_eq_zero {n : ℕ} [NeZero (12 * n)] (hn : 0 < n) {A B : ℤ}
    (hpairBound : -2 * (n : ℤ) < A + B ∧ A + B < 2 * (n : ℤ))
    (hpair : canonicalRoot (12 * n) ^ (intResidue (12 * n) A).val +
      canonicalRoot (12 * n) ^
        (intResidue (12 * n) (6 * (n : ℤ) - B)).val = 0) : A + B = 0 := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hroot0 : canonicalRoot (12 * n) ≠ 0 :=
    (canonicalRoot_isPrimitive (mul_ne_zero (by norm_num) hn.ne')).ne_zero
      (mul_ne_zero (by norm_num) hn.ne')
  have hsquare := ratio_square_eq_one_of_add_eq_zero
    (pow_ne_zero _ hroot0) hpair
  have hd := order_dvd_of_canonical_ratio_pow_eq_one
    (N := 12 * n) A (6 * (n : ℤ) - B) 2 hsquare
  rcases hd with ⟨q, hq⟩
  push_cast at hq
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hrlo : -1 < q + 1 := by nlinarith
  have hrhi : q + 1 < 1 := by nlinarith
  have : q + 1 = 0 := by omega
  nlinarith

lemma ordinary_of_AB_cancel {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (hAB : A + B = 0)
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0) :
    ∃ s : ℤ, Perm3 A B C 0 s (-s) := by
  have hB : B = -A := by omega
  rw [hB] at hsin
  have hang : latticeAngle n (-A) = -latticeAngle n A := by
    simp [latticeAngle]
  rw [hang, Real.sin_neg] at hsin
  have hsinC : Real.sin (latticeAngle n C) = 0 := by linarith
  have hCz := coefficient_eq_zero_of_sine hn hC hsinC
  refine ⟨A, ?_⟩
  simp [Perm3, hB, hCz]

lemma ordinary_of_AC_cancel {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hAC : A + C = 0)
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0) :
    ∃ s : ℤ, Perm3 A B C 0 s (-s) := by
  have hC : C = -A := by omega
  rw [hC] at hsin
  have hang : latticeAngle n (-A) = -latticeAngle n A := by simp [latticeAngle]
  rw [hang, Real.sin_neg] at hsin
  have hsinB : Real.sin (latticeAngle n B) = 0 := by linarith
  have hBz := coefficient_eq_zero_of_sine hn hB hsinB
  refine ⟨A, ?_⟩
  simp [Perm3, hBz, hC]

lemma ordinary_of_BC_cancel {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hBC : B + C = 0)
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0) :
    ∃ s : ℤ, Perm3 A B C 0 s (-s) := by
  have hC : C = -B := by omega
  rw [hC] at hsin
  have hang : latticeAngle n (-B) = -latticeAngle n B := by simp [latticeAngle]
  rw [hang, Real.sin_neg] at hsin
  have hsinA : Real.sin (latticeAngle n A) = 0 := by linarith
  have hAz := coefficient_eq_zero_of_sine hn hA hsinA
  refine ⟨B, ?_⟩
  simp [Perm3, hAz, hC]

#print axioms same_side_pair_impossible
#print axioms mixed_pair_sum_eq_zero
#print axioms ordinary_of_AB_cancel

end A387471
