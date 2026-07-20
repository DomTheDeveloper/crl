import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite Fourier lemmas for the A387471 Mann reduction

This module uses Mathlib's invertible discrete Fourier transform on `ZMod N`.
It isolates the exact linear-algebra step needed in the specialized Mann
argument: if all but one Fourier coefficient vanish and one original
coordinate vanishes, then the entire vector is zero.
-/

open Complex Finset
open scoped BigOperators ZMod

namespace A387471

variable {N : ℕ} [NeZero N]

/-- The unnormalised inverse DFT identity, specialized to complex-valued
functions on `ZMod N`. -/
lemma dft_inverse_sum (Φ : ZMod N → ℂ) (x : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (x * k) * ZMod.dft Φ k =
      (N : ℂ) * Φ x := by
  have h := congrFun (ZMod.dft_dft Φ) (-x)
  rw [ZMod.dft_apply] at h
  simpa only [smul_eq_mul, mul_neg, neg_neg, mul_comm] using h

/-- If all DFT coefficients except possibly `t₀` vanish, and one original
coordinate vanishes, then every coordinate vanishes.  This is the exact
`p - 1` conjugate argument used in the large-prime step of Mann's theorem. -/
theorem dft_eq_zero_of_one_missing (v : ZMod N → ℂ) (t₀ r₀ : ZMod N)
    (hv₀ : v r₀ = 0)
    (hvan : ∀ t : ZMod N, t ≠ t₀ → ZMod.dft v t = 0) :
    v = 0 := by
  classical
  have hmissing : ZMod.dft v t₀ = 0 := by
    have hinv := dft_inverse_sum v r₀
    rw [hv₀, mul_zero] at hinv
    have hsingle :
        (∑ t : ZMod N, ZMod.stdAddChar (r₀ * t) * ZMod.dft v t) =
          ZMod.stdAddChar (r₀ * t₀) * ZMod.dft v t₀ := by
      apply Fintype.sum_eq_single t₀
      intro t ht
      rw [hvan t ht, mul_zero]
    rw [hsingle] at hinv
    have hchar : (ZMod.stdAddChar (r₀ * t₀) : ℂ) ≠ 0 :=
      Circle.coe_ne_zero _
    exact (mul_eq_zero.mp hinv).resolve_left hchar
  apply ZMod.dft.injective
  funext t
  by_cases ht : t = t₀
  · subst t
    simp [hmissing]
  · simp [hvan t ht]

#print axioms dft_inverse_sum
#print axioms dft_eq_zero_of_one_missing

end A387471
