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

/-- Raising the canonical `N`-th root to a divisor `p` gives the canonical
`(N / p)`-th root. -/
theorem canonicalRoot_pow_divisor {N p : ℕ} (hN : N ≠ 0) (hp : p ≠ 0)
    (hdiv : p ∣ N) :
    canonicalRoot N ^ p = canonicalRoot (N / p) := by
  obtain ⟨m, rfl⟩ := hdiv
  simp only [canonicalRoot, Nat.mul_div_left _ hp]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp
  ring

/-- The quotient root appearing in the prime-residue decomposition is the
canonical `p`-th root. -/
theorem canonicalRoot_pow_quotient {N p : ℕ} (hN : N ≠ 0) (hp : p ≠ 0)
    (hdiv : p ∣ N) :
    canonicalRoot N ^ (N / p) = canonicalRoot p := by
  obtain ⟨m, rfl⟩ := hdiv
  simp only [canonicalRoot, Nat.mul_div_left _ hp]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp
  ring

/-- The character factor in the DFT is the extra factor introduced by the
conjugating exponent `1 + (p-t)m`. -/
theorem canonicalRoot_conjugatingExponent {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (a : ℕ) (t : ZMod p) :
    canonicalRoot (p * m) ^ (conjugatingExponent p m t * a) =
      ZMod.stdAddChar (-(a * t)) * canonicalRoot (p * m) ^ a := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hN : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm
  have hrootm : canonicalRoot (p * m) ^ m = canonicalRoot p := by
    have h := canonicalRoot_pow_quotient (N := p * m) (p := p)
      hN hp.ne_zero (dvd_mul_right p m)
    simpa [Nat.mul_div_left _ hp.ne_zero] using h
  have hcast :
      (((p - t.val) * a : ℕ) : ZMod p) = -(a * t) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt t.val_lt)]
    simp [ZMod.natCast_zmod_val]
    ring
  have hfactor : canonicalRoot p ^ ((p - t.val) * a) =
      ZMod.stdAddChar (-(a * t)) := by
    calc
      canonicalRoot p ^ ((p - t.val) * a) =
          (ZMod.stdAddChar (1 : ZMod p)) ^ ((p - t.val) * a) := by
            congr 1
            simpa using (canonicalRoot_pow_eq_stdAddChar (N := p) (1 : ZMod p)).symm
      _ = ZMod.stdAddChar ((((p - t.val) * a : ℕ) : ZMod p)) := by
            symm
            simpa [nsmul_eq_mul] using
              (AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := p))
                (((p - t.val) * a)) (1 : ZMod p))
      _ = ZMod.stdAddChar (-(a * t)) := by rw [hcast]
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
    _ = ZMod.stdAddChar (-(a * t)) * canonicalRoot (p * m) ^ a := by
          rw [hfactor]
          ring

#print axioms canonicalRoot_isPrimitive
#print axioms canonicalRoot_pow_eq_stdAddChar
#print axioms canonicalRoot_pow_divisor
#print axioms canonicalRoot_pow_quotient
#print axioms canonicalRoot_conjugatingExponent

end A387471
