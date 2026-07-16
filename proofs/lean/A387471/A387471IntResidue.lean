import A387471Roots

/-!
# Integer exponents modulo a root order

The trigonometric six-term relation naturally has signed integer exponents.
This module packages their canonical residues as `Fin N` values without losing
the direct connection to Mathlib's standard additive character.
-/

open Complex
open scoped Real ZMod

namespace A387471

/-- Canonical representative of an integer modulo a nonzero natural order. -/
def intResidue (N : ℕ) [NeZero N] (a : ℤ) : Fin N :=
  ⟨(a % N).toNat, by
    have hnonneg : 0 ≤ a % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast NeZero.ne N)
    have hlt : a % (N : ℤ) < N := Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos N)
    omega⟩

/-- The canonical representative has the expected class in `ZMod N`. -/
theorem intResidue_cast (N : ℕ) [NeZero N] (a : ℤ) :
    ((intResidue N a).val : ZMod N) = (a : ZMod N) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N =>
      apply Fin.ext
      change (a % (N + 1 : ℕ)).toNat = (a : ZMod (N + 1)).val
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
      exact (ZMod.val_intCast a).symm

/-- A canonical-root power with signed exponent is the standard exponential. -/
theorem canonicalRoot_pow_intResidue (N : ℕ) [NeZero N] (a : ℤ) :
    canonicalRoot N ^ (intResidue N a).val =
      Complex.exp (2 * Real.pi * Complex.I * a / N) := by
  rw [canonicalRoot_pow_eq_stdAddChar, intResidue_cast]
  exact ZMod.stdAddChar_coe a

/-- Canonical residues respect congruence modulo the order. -/
theorem intResidue_eq_of_modEq {N : ℕ} [NeZero N] {a b : ℤ}
    (h : a ≡ b [ZMOD N]) : intResidue N a = intResidue N b := by
  apply Fin.ext
  have hz : (a : ZMod N) = (b : ZMod N) :=
    (ZMod.intCast_eq_intCast_iff a b N).2 h
  have := congrArg ZMod.val hz
  simpa [intResidue, ZMod.val_intCast] using this

#print axioms intResidue_cast
#print axioms canonicalRoot_pow_intResidue
#print axioms intResidue_eq_of_modEq

end A387471
