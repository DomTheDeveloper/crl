import A387471ThreeRoots
import A387471SixRoots

/-!
# Complete labeled triple obstruction
-/

open Complex

namespace A387471

lemma two_unit_add_unit_ne_zero {x z : ℂ} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) :
    2 * x + z ≠ 0 := by
  intro h
  have heq : 2 * x = -z := by linear_combination h
  have hnorm := congrArg norm heq
  simp [Complex.norm_mul, hx, hz] at hnorm

lemma canonical_power_norm_one {N : ℕ} (hN : N ≠ 0) (a : ℕ) :
    ‖canonicalRoot N ^ a‖ = 1 := by
  rw [Complex.norm_pow, (canonicalRoot_isPrimitive hN).norm'_eq_one hN, one_pow]

lemma equal_first_two_impossible {x z : ℂ} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    (h : x + x + z = 0) : False := by
  exact two_unit_add_unit_ne_zero hx hz (by linear_combination h)

/-- Three positive-side angular roots cannot vanish under the coefficient bounds. -/
theorem positive_angular_triple_impossible {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (h : Complex.exp ((latticeAngle n A : ℂ) * Complex.I) +
      Complex.exp ((latticeAngle n B : ℂ) * Complex.I) +
      Complex.exp ((latticeAngle n C : ℂ) * Complex.I) = 0) : False := by
  letI : NeZero n := ⟨hn.ne'⟩
  let a : Fin (12 * n) := intResidue (12 * n) A
  let b : Fin (12 * n) := intResidue (12 * n) B
  let c : Fin (12 * n) := intResidue (12 * n) C
  have hcan : canonicalRoot (12 * n) ^ a.val + canonicalRoot (12 * n) ^ b.val +
      canonicalRoot (12 * n) ^ c.val = 0 := by
    simpa [a, b, c, canonical_positive_root] using h
  have hcubeA := canonical_three_ratio_cube
    (mul_ne_zero (by norm_num) hn.ne') a b c hcan
  have hcanB : canonicalRoot (12 * n) ^ b.val + canonicalRoot (12 * n) ^ a.val +
      canonicalRoot (12 * n) ^ c.val = 0 := by
    linear_combination hcan
  have hcubeB := canonical_three_ratio_cube
    (mul_ne_zero (by norm_num) hn.ne') b a c hcanB
  have hdA := order_dvd_of_canonical_ratio_pow_eq_one
    (N := 12 * n) A C 3 (by simpa [a, c] using hcubeA)
  have hdB := order_dvd_of_canonical_ratio_pow_eq_one
    (N := 12 * n) B C 3 (by simpa [b, c] using hcubeB)
  rcases hdA with ⟨qA, hqA⟩
  rcases hdB with ⟨qB, hqB⟩
  push_cast at hqA hqB
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hqAlo : -1 ≤ qA := by nlinarith
  have hqAhi : qA ≤ 1 := by nlinarith
  have hqBlo : -1 ≤ qB := by nlinarith
  have hqBhi : qB ≤ 1 := by nlinarith
  by_cases hqAz : qA = 0
  · have hAC : A = C := by nlinarith
    subst A
    have hnormC := canonical_power_norm_one (mul_ne_zero (by norm_num) hn.ne') c.val
    have hnormB := canonical_power_norm_one (mul_ne_zero (by norm_num) hn.ne') b.val
    exact equal_first_two_impossible hnormC hnormB
      (by simpa [a, c, add_assoc, add_left_comm, add_comm] using hcan)
  by_cases hqBz : qB = 0
  · have hBC : B = C := by nlinarith
    subst B
    have hnormC := canonical_power_norm_one (mul_ne_zero (by norm_num) hn.ne') c.val
    have hnormA := canonical_power_norm_one (mul_ne_zero (by norm_num) hn.ne') a.val
    exact equal_first_two_impossible hnormC hnormA
      (by simpa [b, c, add_assoc, add_left_comm, add_comm] using hcan)
  by_cases hqeq : qA = qB
  · have hABeq : A = B := by nlinarith
    subst B
    have hnormA := canonical_power_norm_one (mul_ne_zero (by norm_num) hn.ne') a.val
    have hnormC := canonical_power_norm_one (mul_ne_zero (by norm_num) hn.ne') c.val
    exact equal_first_two_impossible hnormA hnormC
      (by simpa [a, b] using hcan)
  have hqopp : qA = -qB := by omega
  have hdiff : A - B = 4 * (n : ℤ) * (qA - qB) := by nlinarith
  have hdifflo : -6 * (n : ℤ) < A - B := by omega
  have hdiffhi : A - B < 6 * (n : ℤ) := by omega
  omega

/-- Three negative-side angular roots cannot vanish. -/
theorem negative_angular_triple_impossible {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (h : -Complex.exp (-(latticeAngle n A : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n B : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n C : ℂ) * Complex.I) = 0) : False := by
  have hpos : Complex.exp ((latticeAngle n (-A) : ℂ) * Complex.I) +
      Complex.exp ((latticeAngle n (-B) : ℂ) * Complex.I) +
      Complex.exp ((latticeAngle n (-C) : ℂ) * Complex.I) = 0 := by
    have hnegA : latticeAngle n (-A) = -latticeAngle n A := by simp [latticeAngle]
    have hnegB : latticeAngle n (-B) = -latticeAngle n B := by simp [latticeAngle]
    have hnegC : latticeAngle n (-C) = -latticeAngle n C := by simp [latticeAngle]
    rw [hnegA, hnegB, hnegC]
    push_cast
    linear_combination -h
  exact positive_angular_triple_impossible hn (by omega) (by omega) (by omega) hpos

/-- A triple containing both sides of the six-root relation cannot vanish. -/
theorem two_positive_one_negative_impossible {n : ℕ} (hn : 0 < n)
    {A B C : ℤ}
    (hAC : -2 * (n : ℤ) < A + C ∧ A + C < 2 * (n : ℤ))
    (h : Complex.exp ((latticeAngle n A : ℂ) * Complex.I) +
      Complex.exp ((latticeAngle n B : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n C : ℂ) * Complex.I) = 0) : False := by
  letI : NeZero n := ⟨hn.ne'⟩
  let a : Fin (12 * n) := intResidue (12 * n) A
  let b : Fin (12 * n) := intResidue (12 * n) B
  let c : Fin (12 * n) := intResidue (12 * n) (6 * (n : ℤ) - C)
  have hcan : canonicalRoot (12 * n) ^ a.val + canonicalRoot (12 * n) ^ b.val +
      canonicalRoot (12 * n) ^ c.val = 0 := by
    dsimp [a, b, c]
    rw [canonical_positive_root A, canonical_positive_root B, canonical_negative_root C]
    exact h
  have hcube := canonical_three_ratio_cube
    (mul_ne_zero (by norm_num) hn.ne') a b c hcan
  exact mixed_cube_ratio_impossible hn hAC.1 hAC.2 (by simpa [a, c] using hcube)

/-- One positive and two negative roots cannot vanish. -/
theorem one_positive_two_negative_impossible {n : ℕ} (hn : 0 < n)
    {A B C : ℤ}
    (hAB : -2 * (n : ℤ) < A + B ∧ A + B < 2 * (n : ℤ))
    (h : Complex.exp ((latticeAngle n A : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n B : ℂ) * Complex.I) +
      -Complex.exp (-(latticeAngle n C : ℂ) * Complex.I) = 0) : False := by
  letI : NeZero n := ⟨hn.ne'⟩
  let a : Fin (12 * n) := intResidue (12 * n) A
  let b : Fin (12 * n) := intResidue (12 * n) (6 * (n : ℤ) - B)
  let c : Fin (12 * n) := intResidue (12 * n) (6 * (n : ℤ) - C)
  have hcan : canonicalRoot (12 * n) ^ a.val + canonicalRoot (12 * n) ^ b.val +
      canonicalRoot (12 * n) ^ c.val = 0 := by
    dsimp [a, b, c]
    rw [canonical_positive_root A, canonical_negative_root B, canonical_negative_root C]
    exact h
  have hperm : canonicalRoot (12 * n) ^ a.val + canonicalRoot (12 * n) ^ c.val +
      canonicalRoot (12 * n) ^ b.val = 0 := by
    linear_combination hcan
  have hcube := canonical_three_ratio_cube
    (mul_ne_zero (by norm_num) hn.ne') a c b hperm
  exact mixed_cube_ratio_impossible hn hAB.1 hAB.2 (by simpa [a, b] using hcube)

set_option maxHeartbeats 0 in
/-- No three distinct labeled roots form a vanishing triple. -/
theorem labeled_triple_impossible {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (hAB : -2 * (n : ℤ) < A + B ∧ A + B < 2 * (n : ℤ))
    (hAC : -2 * (n : ℤ) < A + C ∧ A + C < 2 * (n : ℤ))
    (hBC : -2 * (n : ℤ) < B + C ∧ B + C < 2 * (n : ℤ))
    (r s t : Fin 6) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (h : sixRoot n A B C r + sixRoot n A B C s + sixRoot n A B C t = 0) : False := by
  fin_cases r <;> fin_cases s <;> fin_cases t
  all_goals simp only [sixRoot] at h
  all_goals try {simp at hrs}
  all_goals try {simp at hrt}
  all_goals try {simp at hst}
  all_goals first
    | exact positive_angular_triple_impossible (A := A) (B := B) (C := C)
        hn hA hB hC (by simpa [add_comm, add_left_comm] using h)
    | exact negative_angular_triple_impossible (A := A) (B := B) (C := C)
        hn hA hB hC (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := B) (B := A) (C := A)
        hn (by omega) (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := A) (B := B) (C := B)
        hn (by omega) (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := A) (B := B) (C := C)
        hn hAC (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := C) (B := A) (C := A)
        hn (by omega) (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := A) (B := C) (C := B)
        hn hAB (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := A) (B := C) (C := C)
        hn hAC (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := B) (B := C) (C := A)
        hn (by omega) (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := C) (B := B) (C := B)
        hn (by omega) (by simpa [add_comm, add_left_comm] using h)
    | exact two_positive_one_negative_impossible (A := B) (B := C) (C := C)
        hn hBC (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := A) (B := B) (C := A)
        hn hAB (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := A) (B := C) (C := A)
        hn hAC (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := A) (B := B) (C := C)
        hn hAB (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := B) (B := A) (C := B)
        hn (by omega) (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := B) (B := A) (C := C)
        hn (by omega) (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := B) (B := C) (C := B)
        hn hBC (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := C) (B := A) (C := B)
        hn (by omega) (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := C) (B := A) (C := C)
        hn hAC (by simpa [add_comm, add_left_comm] using h)
    | exact one_positive_two_negative_impossible (A := C) (B := B) (C := C)
        hn hBC (by simpa [add_comm, add_left_comm] using h)

#print axioms labeled_triple_impossible

end A387471
