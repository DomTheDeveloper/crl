import A387471Arithmetic
import A387471Classification
import A387471Roots

/-!
# A weight-six specialization of Mann's theorem

The final theorem in this module will show that every ratio in a minimal
vanishing sum of at most six powers of a canonical root is a 30th root of
unity. The proof is by conductor descent using prime-residue Fourier
coefficients.
-/

open Complex Finset
open scoped BigOperators ZMod

namespace A387471

/-- The exponent of a term, viewed modulo a prime divisor of the conductor. -/
def exponentResidue {N p : ℕ} (a : Fin N) : ZMod p := a.val

/-- The sum of all terms whose exponents lie in one residue class modulo `p`. -/
noncomputable def residueVector {N p : ℕ} (s : Finset (Fin N)) (r : ZMod p) : ℂ :=
  ∑ a ∈ s with exponentResidue (p := p) a = r, canonicalRoot N ^ a.val

/-- The DFT of the residue vector is the original sum weighted by the standard
character of each exponent residue. -/
theorem dft_residueVector {N p : ℕ} [NeZero p] (s : Finset (Fin N))
    (t : ZMod p) :
    ZMod.dft (residueVector (N := N) (p := p) s) t =
      ∑ a ∈ s,
        ZMod.stdAddChar (-(exponentResidue (p := p) a * t)) *
          canonicalRoot N ^ a.val := by
  classical
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, residueVector]
  exact sum_weighted_fibers s (exponentResidue (p := p))
    (fun r : ZMod p ↦ ZMod.stdAddChar (-(r * t)))
    (fun a : Fin N ↦ canonicalRoot N ^ a.val)

/-- In a minimal vanishing sum, if every residue-class subsum vanishes, all
terms have the same residue. -/
theorem residue_constant_of_minimal {N p : ℕ} (s : Finset (Fin N))
    (hmin : MinimallyVanishes s (fun a ↦ canonicalRoot N ^ a.val))
    (hzero : residueVector (N := N) (p := p) s = 0) :
    ∃ r : ZMod p, ∀ a ∈ s, exponentResidue (p := p) a = r := by
  classical
  obtain ⟨a₀, ha₀⟩ := hmin.1
  let r₀ : ZMod p := exponentResidue (p := p) a₀
  let fiber : Finset (Fin N) :=
    s.filter fun a ↦ exponentResidue (p := p) a = r₀
  have hfiber_nonempty : fiber.Nonempty := by
    exact ⟨a₀, by simp [fiber, r₀, ha₀]⟩
  have hfiber_vanish : Vanishes fiber (fun a ↦ canonicalRoot N ^ a.val) := by
    have hr := congrFun hzero r₀
    simpa [residueVector, fiber, Vanishes] using hr
  have hfiber_eq : fiber = s := by
    by_contra hne
    have hproper : fiber ⊂ s :=
      (Finset.ssubset_iff_subset_ne).2 ⟨Finset.filter_subset _ _, hne⟩
    exact hmin.2.2 fiber hproper hfiber_nonempty hfiber_vanish
  refine ⟨r₀, ?_⟩
  intro a ha
  have : a ∈ fiber := hfiber_eq.symm ▸ ha
  simpa [fiber] using this

#print axioms dft_residueVector
#print axioms residue_constant_of_minimal

end A387471
