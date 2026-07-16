import Mathlib
import A387471Families
import A387471Fourier

/-!
# Weight-six roots-of-unity classification for OEIS A387471

This module contains the algebraic primitives used by the specialized Mann
reduction and the final finite classification. No classification statement is
introduced as an axiom or hypothesis.
-/

open scoped BigOperators
open Polynomial

namespace A387471

/-- A finite vanishing sum indexed by a finite set. -/
def Vanishes {ι : Type*} (s : Finset ι) (z : ι → ℂ) : Prop :=
  ∑ i ∈ s, z i = 0

/-- Minimality means that the sum is nonempty and no nonempty proper
subcollection vanishes. -/
def MinimallyVanishes {ι : Type*} (s : Finset ι) (z : ι → ℂ) : Prop :=
  s.Nonempty ∧ Vanishes s z ∧
    ∀ t : Finset ι, t ⊂ s → t.Nonempty → ¬ Vanishes t z

@[simp] theorem vanishes_empty {ι : Type*} (z : ι → ℂ) : Vanishes ∅ z := by
  simp [Vanishes]

/-- The integer-coefficient polynomial attached to a multiset of exponents. -/
noncomputable def exponentPolynomial {ι : Type*} (s : Finset ι) (a : ι → ℕ) : ℚ[X] :=
  ∑ i ∈ s, X ^ a i

@[simp] theorem aeval_exponentPolynomial {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (z : ℂ) :
    Polynomial.aeval z (exponentPolynomial s a) = ∑ i ∈ s, z ^ a i := by
  simp [exponentPolynomial]

/-- An integer-coefficient relation among powers of a primitive root remains
valid after replacing the root by any coprime power. This is the elementary
Galois-conjugacy input in the specialized Mann argument. -/
theorem vanishing_relation_coprime_power {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (hvan : ∑ i ∈ s, ζ ^ a i = 0) (u : ℕ) (hu : u.Coprime N) :
    ∑ i ∈ s, ζ ^ (u * a i) = 0 := by
  have hp0 : Polynomial.aeval ζ (exponentPolynomial s a) = 0 := by
    simpa using hvan
  obtain ⟨q, hq⟩ := minpoly.dvd ℚ ζ hp0
  have hroot : Polynomial.aeval (ζ ^ u) (minpoly ℚ ζ) = 0 := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hN]
    exact (hζ.pow_of_coprime u hu).isRoot_cyclotomic hN
  have heval : Polynomial.aeval (ζ ^ u) (exponentPolynomial s a) = 0 := by
    rw [hq, map_mul, hroot, zero_mul]
  simpa [pow_mul] using heval

/-- Regrouping a finite weighted sum by a finite-valued tag. -/
theorem sum_weighted_fibers {ι κ R : Type*} [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [CommSemiring R] (s : Finset ι) (tag : ι → κ)
    (w : κ → R) (g : ι → R) :
    ∑ r : κ, w r * ∑ i ∈ s with tag i = r, g i =
      ∑ i ∈ s, w (tag i) * g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, ih]

#print axioms vanishes_empty
#print axioms aeval_exponentPolynomial
#print axioms vanishing_relation_coprime_power
#print axioms sum_weighted_fibers

end A387471
