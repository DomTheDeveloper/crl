import FormalConjectures.ErdosProblems.«1150»
import Mathlib.Analysis.Fourier.ZMod

open Complex Finset MeasureTheory
open scoped BigOperators ComplexConjugate Polynomial ZMod

namespace Erdos1150Proof

variable {N : ℕ} [NeZero N]

/-- Orthogonality of the standard additive characters on `ZMod N`. -/
lemma sum_stdAddChar_mul (t : ZMod N) :
    ∑ i : ZMod N, ZMod.stdAddChar (t * i) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · subst t
    simp
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

#print axioms sum_stdAddChar_mul

end Erdos1150Proof
