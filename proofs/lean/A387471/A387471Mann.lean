import A387471Arithmetic
import A387471Classification
import A387471Roots

/-!
# A weight-six specialization of Mann's theorem

The final theorem in this module will show that every ratio in a minimal
vanishing sum of at most six powers of a canonical root is a 30th root of
unity. The proof is by conductor descent using prime-residue Fourier
coefficients. Terms are indexed by labels, so repeated roots retain their
multiplicity.
-/

open Complex Finset
open scoped BigOperators ZMod

namespace A387471

/-- The exponent of a term, viewed modulo a prime divisor of the conductor. -/
def exponentResidue {N p : ℕ} (a : Fin N) : ZMod p := a.val

/-- The sum of all labeled terms whose exponents lie in one residue class
modulo `p`. -/
noncomputable def residueVector {ι : Type*} {N p : ℕ}
    (s : Finset ι) (a : ι → Fin N) (r : ZMod p) : ℂ :=
  ∑ i ∈ s with exponentResidue (p := p) (a i) = r,
    canonicalRoot N ^ (a i).val

/-- The DFT of the residue vector is the original labeled sum weighted by the
standard character of each exponent residue. -/
theorem dft_residueVector {ι : Type*} {N p : ℕ} [NeZero p]
    (s : Finset ι) (a : ι → Fin N) (t : ZMod p) :
    ZMod.dft (residueVector (N := N) (p := p) s a) t =
      ∑ i ∈ s,
        ZMod.stdAddChar (-(exponentResidue (p := p) (a i) * t)) *
          canonicalRoot N ^ (a i).val := by
  classical
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, residueVector]
  exact sum_weighted_fibers s
    (fun i ↦ exponentResidue (p := p) (a i))
    (fun r : ZMod p ↦ ZMod.stdAddChar (-(r * t)))
    (fun i ↦ canonicalRoot N ^ (a i).val)

/-- In a minimal vanishing sum, if every residue-class subsum vanishes, all
labeled terms have the same residue. -/
theorem residue_constant_of_minimal {ι : Type*} {N p : ℕ}
    (s : Finset ι) (a : ι → Fin N)
    (hmin : MinimallyVanishes s (fun i ↦ canonicalRoot N ^ (a i).val))
    (hzero : residueVector (N := N) (p := p) s a = 0) :
    ∃ r : ZMod p, ∀ i ∈ s, exponentResidue (p := p) (a i) = r := by
  classical
  obtain ⟨i₀, hi₀⟩ := hmin.1
  let r₀ : ZMod p := exponentResidue (p := p) (a i₀)
  let fiber : Finset ι :=
    s.filter fun i ↦ exponentResidue (p := p) (a i) = r₀
  have hfiber_nonempty : fiber.Nonempty := by
    exact ⟨i₀, by simp [fiber, r₀, hi₀]⟩
  have hfiber_vanish :
      Vanishes fiber (fun i ↦ canonicalRoot N ^ (a i).val) := by
    have hr := congrFun hzero r₀
    simpa [residueVector, fiber, Vanishes] using hr
  have hfiber_eq : fiber = s := by
    by_contra hne
    have hproper : fiber ⊂ s :=
      (Finset.ssubset_iff_subset_ne).2 ⟨Finset.filter_subset _ _, hne⟩
    exact hmin.2.2 fiber hproper hfiber_nonempty hfiber_vanish
  refine ⟨r₀, ?_⟩
  intro i hi
  have : i ∈ fiber := hfiber_eq.symm ▸ hi
  simpa [fiber] using this

/-- If `p²` divides the conductor, every prime-residue Fourier coefficient is
obtained from a coprime Galois conjugate of the original relation. -/
theorem residueVector_eq_zero_squareful {ι : Type*} {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) (hpm : p ∣ m)
    (s : Finset ι) (a : ι → Fin (p * m))
    (hvan : Vanishes s (fun i ↦ canonicalRoot (p * m) ^ (a i).val)) :
    residueVector (N := p * m) (p := p) s a = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply ZMod.dft.injective
  funext t
  rw [map_zero, dft_residueVector]
  have hconj := vanishing_relation_coprime_power
    (N := p * m) (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hm))
    (canonicalRoot_isPrimitive (mul_ne_zero hp.ne_zero hm))
    s (fun i ↦ (a i).val)
    (by simpa [Vanishes] using hvan)
    (conjugatingExponent p m t)
    (conjugatingExponent_coprime_squareful hp hpm t)
  simpa [exponentResidue, canonicalRoot_conjugatingExponent hp hm] using hconj

/-- If `p > 6` occurs only once in the conductor, the at-most-six terms miss a
residue class. All Fourier coefficients except one are Galois conjugates, and
one-missing Fourier inversion forces every residue-class subsum to vanish. -/
theorem residueVector_eq_zero_large_prime {ι : Type*} {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) (hpm : ¬ p ∣ m) (hp6 : 6 < p)
    (s : Finset ι) (a : ι → Fin (p * m)) (hcard : s.card ≤ 6)
    (hvan : Vanishes s (fun i ↦ canonicalRoot (p * m) ^ (a i).val)) :
    residueVector (N := p * m) (p := p) s a = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let tag : ι → ZMod p := fun i ↦ exponentResidue (p := p) (a i)
  obtain ⟨r₀, hr₀⟩ := exists_missing_residue hp s tag hcard hp6
  have hv₀ : residueVector (N := p * m) (p := p) s a r₀ = 0 := by
    simp [residueVector, tag, hr₀]
  apply dft_eq_zero_of_one_missing
    (residueVector (N := p * m) (p := p) s a)
    ((m : ZMod p)⁻¹) r₀ hv₀
  intro t ht
  rw [dft_residueVector]
  have hconj := vanishing_relation_coprime_power
    (N := p * m) (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hm))
    (canonicalRoot_isPrimitive (mul_ne_zero hp.ne_zero hm))
    s (fun i ↦ (a i).val)
    (by simpa [Vanishes] using hvan)
    (conjugatingExponent p m t)
    (conjugatingExponent_coprime_squarefree hp hpm t ht)
  simpa [exponentResidue, canonicalRoot_conjugatingExponent hp hm] using hconj

/-- A bad prime factor of the conductor forces all exponents in a minimal
weight-at-most-six relation into one residue class. -/
theorem residue_constant_bad_prime {ι : Type*} {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0)
    (s : Finset ι) (a : ι → Fin (p * m)) (hcard : s.card ≤ 6)
    (hmin : MinimallyVanishes s
      (fun i ↦ canonicalRoot (p * m) ^ (a i).val))
    (hbad : p ∣ m ∨ 6 < p) :
    ∃ r : ZMod p, ∀ i ∈ s, exponentResidue (p := p) (a i) = r := by
  rcases hbad with hpm | hp6
  · exact residue_constant_of_minimal s a hmin
      (residueVector_eq_zero_squareful hp hm hpm s a hmin.2.1)
  · by_cases hpm : p ∣ m
    · exact residue_constant_of_minimal s a hmin
        (residueVector_eq_zero_squareful hp hm hpm s a hmin.2.1)
    · exact residue_constant_of_minimal s a hmin
        (residueVector_eq_zero_large_prime hp hm hpm hp6 s a hcard hmin.2.1)

#print axioms dft_residueVector
#print axioms residue_constant_of_minimal
#print axioms residueVector_eq_zero_squareful
#print axioms residueVector_eq_zero_large_prime
#print axioms residue_constant_bad_prime

end A387471
