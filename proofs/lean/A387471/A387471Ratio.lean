import A387471IntResidue

/-!
# Arithmetic consequences of canonical-root ratio relations
-/

open Complex
open scoped ZMod

namespace A387471

/-- A quotient of two canonical powers is the standard character of the
exponent difference. -/
lemma canonical_ratio_eq_stdAddChar {N : ℕ} [NeZero N] (a b : ℤ) :
    canonicalRoot N ^ (intResidue N a).val /
        canonicalRoot N ^ (intResidue N b).val =
      ZMod.stdAddChar ((a - b : ℤ) : ZMod N) := by
  rw [canonicalRoot_pow_nat_eq_stdAddChar,
    canonicalRoot_pow_nat_eq_stdAddChar, intResidue_cast, intResidue_cast]
  simp [sub_eq_add_neg, div_eq_mul_inv, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv]

/-- If the `k`th power of a ratio is one, the root order divides `k(a-b)`. -/
theorem order_dvd_of_canonical_ratio_pow_eq_one {N : ℕ} [NeZero N]
    (a b : ℤ) (k : ℕ)
    (h : (canonicalRoot N ^ (intResidue N a).val /
      canonicalRoot N ^ (intResidue N b).val) ^ k = 1) :
    (N : ℤ) ∣ (k : ℤ) * (a - b) := by
  rw [canonical_ratio_eq_stdAddChar] at h
  have hchar :
      ZMod.stdAddChar (k • (((a - b : ℤ) : ZMod N))) = 1 := by
    rw [AddChar.map_nsmul_eq_pow]
    exact h
  have hz : k • (((a - b : ℤ) : ZMod N)) = 0 := by
    apply ZMod.injective_stdAddChar
    simpa using hchar
  have hcast : (((k : ℤ) * (a - b) : ℤ) : ZMod N) = 0 := by
    simpa [nsmul_eq_mul] using hz
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast

/-- The paired positive/negative labels in the A387471 relation force `n ∣ 5A`. -/
set_option maxHeartbeats 0 in
theorem n_dvd_five_mul_of_paired_ratio {n : ℕ} (hn : 0 < n) (A : ℤ)
    (h : (canonicalRoot (12 * n) ^ (intResidue (12 * n) A).val /
      canonicalRoot (12 * n) ^
        (intResidue (12 * n) (6 * (n : ℤ) - A)).val) ^ 30 = 1) :
    (n : ℤ) ∣ 5 * A := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : NeZero (12 * n) := ⟨mul_ne_zero (by norm_num) hn.ne'⟩
  have hd := order_dvd_of_canonical_ratio_pow_eq_one
    (N := 12 * n) A (6 * (n : ℤ) - A) 30 h
  rcases hd with ⟨q, hq⟩
  refine ⟨q + 15, ?_⟩
  ring_nf at hq ⊢
  omega

#print axioms order_dvd_of_canonical_ratio_pow_eq_one
#print axioms n_dvd_five_mul_of_paired_ratio

end A387471
