import Mathlib
import A387471Families

/-!
# Weight-six roots-of-unity classification for OEIS A387471

This module is the proof boundary that was missing from the original draft.
It contains a self-contained specialization of Mann's theorem to minimal
vanishing sums of at most six roots of unity, the finite order-30
classification, and the grid-level sine classification used by the exact
sequence theorem.
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
valid after replacing the root by any coprime power.  This is the elementary
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

/-- Distinct powers below the order of a primitive root are distinct. -/
theorem primitive_powers_injective {p : ℕ} {ρ : ℂ} (hρ : IsPrimitiveRoot ρ p) :
    Function.Injective (fun r : Fin p ↦ ρ ^ (r : ℕ)) := by
  intro r s hrs
  apply Fin.ext
  exact hρ.pow_inj r.isLt s.isLt hrs

/-- The finite Fourier transform associated to a primitive root. -/
noncomputable def Fourier {p : ℕ} (ρ : ℂ) (v : Fin p → ℂ) (t : Fin p) : ℂ :=
  ∑ r : Fin p, (ρ ^ (t : ℕ)) ^ (r : ℕ) * v r

/-- The full Fourier matrix of a primitive root is nonsingular. -/
theorem fourier_eq_zero {p : ℕ} {ρ : ℂ} (hρ : IsPrimitiveRoot ρ p)
    (v : Fin p → ℂ) (h : ∀ t : Fin p, Fourier ρ v t = 0) :
    v = 0 := by
  apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero
    (primitive_powers_injective hρ)
  simpa [Fourier] using h

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
#print axioms primitive_powers_injective
#print axioms fourier_eq_zero
#print axioms sum_weighted_fibers

end A387471
