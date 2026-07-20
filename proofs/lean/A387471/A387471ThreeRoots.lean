import A387471Ratio

/-!
# Vanishing triples of canonical roots
-/

open Complex
open scoped ComplexConjugate

namespace A387471

/-- Conjugation of the canonical root is inversion. -/
lemma conj_canonicalRoot {N : ℕ} (hN : N ≠ 0) :
    conj (canonicalRoot N) = (canonicalRoot N)⁻¹ := by
  rw [canonicalRoot, ← Complex.exp_neg, ← Complex.exp_conj]
  congr 1
  push_cast
  simp
  ring

/-- The same fact for every canonical-root power. -/
lemma conj_canonicalRoot_pow {N : ℕ} (hN : N ≠ 0) (a : ℕ) :
    conj (canonicalRoot N ^ a) = (canonicalRoot N ^ a)⁻¹ := by
  rw [map_pow, conj_canonicalRoot hN, inv_pow]

/-- Three nonzero complex numbers whose sum and inverse sum vanish have equal
cubes. -/
lemma ratio_cube_eq_one_of_sum_inv_sum {x y z : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0)
    (hinv : x⁻¹ + y⁻¹ + z⁻¹ = 0) : (x / z) ^ 3 = 1 := by
  have hpair : x * y + x * z + y * z = 0 := by
    field_simp [hx, hy, hz] at hinv
    linear_combination hinv
  have hquad : x ^ 2 + x * z + z ^ 2 = 0 := by
    linear_combination (x + z) * hsum - hpair
  have hcubes : x ^ 3 = z ^ 3 := by
    apply sub_eq_zero.mp
    calc
      x ^ 3 - z ^ 3 = (x - z) * (x ^ 2 + x * z + z ^ 2) := by ring
      _ = 0 := by rw [hquad, mul_zero]
  rw [div_pow, hcubes, div_self (pow_ne_zero 3 hz)]

/-- In every vanishing triple of powers of one canonical root, each quotient
is a cube root of unity. -/
theorem canonical_three_ratio_cube {N : ℕ} (hN : N ≠ 0)
    (a b c : Fin N)
    (hvan : canonicalRoot N ^ a.val + canonicalRoot N ^ b.val +
      canonicalRoot N ^ c.val = 0) :
    (canonicalRoot N ^ a.val / canonicalRoot N ^ c.val) ^ 3 = 1 := by
  have hroot0 : canonicalRoot N ≠ 0 :=
    (canonicalRoot_isPrimitive hN).ne_zero hN
  have hconj := congrArg conj hvan
  simp only [map_add, map_zero, conj_canonicalRoot_pow hN] at hconj
  exact ratio_cube_eq_one_of_sum_inv_sum
    (pow_ne_zero _ hroot0) (pow_ne_zero _ hroot0) (pow_ne_zero _ hroot0)
    hvan hconj

/-- A cube-root quotient between a positive `A` label and a negative `B` label
contradicts the strict pair-sum bounds. -/
theorem mixed_cube_ratio_impossible {n : ℕ} [NeZero (12 * n)] (hn : 0 < n) {A B : ℤ}
    (hlo : -2 * (n : ℤ) < A + B) (hhi : A + B < 2 * (n : ℤ))
    (hcube : (canonicalRoot (12 * n) ^ (intResidue (12 * n) A).val /
      canonicalRoot (12 * n) ^
        (intResidue (12 * n) (6 * (n : ℤ) - B)).val) ^ 3 = 1) : False := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hd := order_dvd_of_canonical_ratio_pow_eq_one
    (N := 12 * n) A (6 * (n : ℤ) - B) 3 hcube
  rcases hd with ⟨q, hq⟩
  push_cast at hq
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hqlo : -2 < 4 * q + 6 := by nlinarith
  have hqhi : 4 * q + 6 < 2 := by nlinarith
  omega

#print axioms canonical_three_ratio_cube
#print axioms mixed_cube_ratio_impossible

end A387471
