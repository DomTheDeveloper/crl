import Mathlib.Analysis.Fourier.ZMod
import Mathlib.RingTheory.RootsOfUnity.Complex
import A387471Arithmetic

/-!
# Canonical complex roots of unity for A387471

The roots in the trigonometric reduction are powers of the canonical root
`exp (2πi/N)`. This module records its compatibility with Mathlib's standard
additive character on `ZMod N` and with division of the conductor.
-/

open Complex
open scoped Real ZMod

namespace A387471

/-- The canonical `N`-th complex root of unity. -/
noncomputable def canonicalRoot (N : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / N)

/-- The canonical root is primitive whenever the order is nonzero. -/
theorem canonicalRoot_isPrimitive {N : ℕ} (hN : N ≠ 0) :
    IsPrimitiveRoot (canonicalRoot N) N := by
  simpa [canonicalRoot] using Complex.isPrimitiveRoot_exp N hN

/-- Mathlib's standard additive character is exactly exponentiation of the
canonical root. -/
theorem canonicalRoot_pow_eq_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) :
    canonicalRoot N ^ x.val = ZMod.stdAddChar x := by
  calc
    canonicalRoot N ^ x.val = (ZMod.stdAddChar (1 : ZMod N)) ^ x.val := by
      congr 1
      simpa [canonicalRoot] using (ZMod.stdAddChar_coe (N := N) (1 : ℤ)).symm
    _ = ZMod.stdAddChar (x.val • (1 : ZMod N)) := by
      symm
      exact AddChar.map_nsmul_eq_pow _ _ _
    _ = ZMod.stdAddChar x := by
      congr 1
      simpa [nsmul_eq_mul] using (ZMod.natCast_zmod_val x)

/-- Arbitrary natural powers of the canonical root agree with the standard
additive character after reduction modulo `N`. -/
theorem canonicalRoot_pow_nat_eq_stdAddChar {N : ℕ} [NeZero N] (a : ℕ) :
    canonicalRoot N ^ a = ZMod.stdAddChar (a : ZMod N) := by
  calc
    canonicalRoot N ^ a = (ZMod.stdAddChar (1 : ZMod N)) ^ a := by
      congr 1
      simpa [canonicalRoot] using (ZMod.stdAddChar_coe (N := N) (1 : ℤ)).symm
    _ = ZMod.stdAddChar (a • (1 : ZMod N)) := by
      symm
      exact AddChar.map_nsmul_eq_pow _ _ _
    _ = ZMod.stdAddChar (a : ZMod N) := by simp [nsmul_eq_mul]

/-- Raising the canonical `N`-th root to a divisor `p` gives the canonical
`(N / p)`-th root. -/
theorem canonicalRoot_pow_divisor {N p : ℕ} (hN : N ≠ 0) (hp : p ≠ 0)
    (hdiv : p ∣ N) :
    canonicalRoot N ^ p = canonicalRoot (N / p) := by
  obtain ⟨m, rfl⟩ := hdiv
  have hm : m ≠ 0 := by
    intro hm
    subst m
    simp at hN
  simp only [canonicalRoot, Nat.mul_div_left m (Nat.pos_of_ne_zero hp)]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [hp, hm]
  ring

/-- The quotient root appearing in the prime-residue decomposition is the
canonical `p`-th root. -/
theorem canonicalRoot_pow_quotient {N p : ℕ} (hN : N ≠ 0) (hp : p ≠ 0)
    (hdiv : p ∣ N) :
    canonicalRoot N ^ (N / p) = canonicalRoot p := by
  obtain ⟨m, rfl⟩ := hdiv
  have hm : m ≠ 0 := by
    intro hm
    subst m
    simp at hN
  simp only [canonicalRoot, Nat.mul_div_left m (Nat.pos_of_ne_zero hp)]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [hp, hm]
  ring

/-- The character factor in the DFT is the extra factor introduced by the
conjugating exponent `1 + (p-t)m`. -/
theorem canonicalRoot_conjugatingExponent {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (a : ℕ) (t : ZMod p) :
    canonicalRoot (p * m) ^ (conjugatingExponent p m t * a) =
      ZMod.stdAddChar (-((a : ZMod p) * t)) * canonicalRoot (p * m) ^ a := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hN : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm
  have hrootm : canonicalRoot (p * m) ^ m = canonicalRoot p := by
    have h := canonicalRoot_pow_quotient (N := p * m) (p := p)
      hN hp.ne_zero (dvd_mul_right p m)
    simpa [Nat.mul_div_left m hp.pos] using h
  have hcast :
      (((p - t.val) * a : ℕ) : ZMod p) = -((a : ZMod p) * t) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt t.val_lt)]
    simp [ZMod.natCast_zmod_val]
    ring
  have hfactor : canonicalRoot p ^ ((p - t.val) * a) =
      ZMod.stdAddChar (-((a : ZMod p) * t)) := by
    calc
      canonicalRoot p ^ ((p - t.val) * a) =
          ZMod.stdAddChar ((((p - t.val) * a : ℕ) : ZMod p)) :=
            canonicalRoot_pow_nat_eq_stdAddChar _
      _ = ZMod.stdAddChar (-((a : ZMod p) * t)) := by rw [hcast]
  calc
    canonicalRoot (p * m) ^ (conjugatingExponent p m t * a) =
        canonicalRoot (p * m) ^ (a + m * ((p - t.val) * a)) := by
          congr 1
          simp [conjugatingExponent]
          ring
    _ = canonicalRoot (p * m) ^ a *
          (canonicalRoot (p * m) ^ m) ^ ((p - t.val) * a) := by
          rw [pow_add, pow_mul]
    _ = canonicalRoot (p * m) ^ a *
          canonicalRoot p ^ ((p - t.val) * a) := by rw [hrootm]
    _ = ZMod.stdAddChar (-((a : ZMod p) * t)) * canonicalRoot (p * m) ^ a := by
          rw [hfactor]
          ring

/-- Equal exponent residues modulo `p` imply that the quotient of the two
corresponding `(p*m)`-th roots is an `m`-th root of unity. -/
theorem canonical_ratio_pow_quotient_eq_one {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (x y : Fin (p * m))
    (hres : (x.val : ZMod p) = (y.val : ZMod p)) :
    (canonicalRoot (p * m) ^ x.val /
      canonicalRoot (p * m) ^ y.val) ^ m = 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hN : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm
  have hrootm : canonicalRoot (p * m) ^ m = canonicalRoot p := by
    have h := canonicalRoot_pow_quotient (N := p * m) (p := p)
      hN hp.ne_zero (dvd_mul_right p m)
    simpa [Nat.mul_div_left m hp.pos] using h
  have hx : (canonicalRoot (p * m) ^ x.val) ^ m =
      ZMod.stdAddChar (x.val : ZMod p) := by
    calc
      (canonicalRoot (p * m) ^ x.val) ^ m =
          (canonicalRoot (p * m) ^ m) ^ x.val := by
            rw [← pow_mul, ← pow_mul]
            congr 1
            exact Nat.mul_comm _ _
      _ = canonicalRoot p ^ x.val := by rw [hrootm]
      _ = ZMod.stdAddChar (x.val : ZMod p) :=
        canonicalRoot_pow_nat_eq_stdAddChar _
  have hy : (canonicalRoot (p * m) ^ y.val) ^ m =
      ZMod.stdAddChar (y.val : ZMod p) := by
    calc
      (canonicalRoot (p * m) ^ y.val) ^ m =
          (canonicalRoot (p * m) ^ m) ^ y.val := by
            rw [← pow_mul, ← pow_mul]
            congr 1
            exact Nat.mul_comm _ _
      _ = canonicalRoot p ^ y.val := by rw [hrootm]
      _ = ZMod.stdAddChar (y.val : ZMod p) :=
        canonicalRoot_pow_nat_eq_stdAddChar _
  rw [div_pow, hx, hy, hres]
  exact div_self (Circle.coe_ne_zero _)

/-- Every quotient in one residue class has a canonical exponent modulo the
smaller conductor. -/
theorem exists_canonical_ratio_exponent {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (x y : Fin (p * m))
    (hres : (x.val : ZMod p) = (y.val : ZMod p)) :
    ∃ d : Fin m,
      canonicalRoot m ^ d.val =
        canonicalRoot (p * m) ^ x.val /
          canonicalRoot (p * m) ^ y.val := by
  letI : NeZero m := ⟨hm⟩
  have hpow := canonical_ratio_pow_quotient_eq_one hp hm x y hres
  obtain ⟨d, hd, heq⟩ :=
    (canonicalRoot_isPrimitive hm).eq_pow_of_pow_eq_one hpow
  exact ⟨⟨d, hd⟩, heq⟩

#print axioms canonicalRoot_isPrimitive
#print axioms canonicalRoot_pow_eq_stdAddChar
#print axioms canonicalRoot_pow_nat_eq_stdAddChar
#print axioms canonicalRoot_pow_divisor
#print axioms canonicalRoot_pow_quotient
#print axioms canonicalRoot_conjugatingExponent
#print axioms canonical_ratio_pow_quotient_eq_one
#print axioms exists_canonical_ratio_exponent

end A387471
