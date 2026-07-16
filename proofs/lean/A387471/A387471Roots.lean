import Mathlib.Analysis.Fourier.ZMod
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Canonical complex roots of unity for A387471

The roots in the trigonometric reduction are powers of the canonical root
`exp (2πi/N)`.  This module records its compatibility with Mathlib's standard
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

#print axioms canonicalRoot_isPrimitive
#print axioms canonicalRoot_pow_eq_stdAddChar
#print axioms canonicalRoot_pow_divisor
#print axioms canonicalRoot_pow_quotient

end A387471
