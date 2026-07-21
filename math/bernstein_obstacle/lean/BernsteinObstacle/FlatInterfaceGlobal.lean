import BernsteinObstacle.HilbertFalk
import BernsteinObstacle.CutPatchSaturation
import Mathlib.Tactic

open scoped BigOperators InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Global flat-interface prism aggregation

The explicit geometry gives two retained quarter-width prisms in every interface
square. Their combined local obstruction is `a² h⁴ / 768`. This file performs
the remaining finite summation: at least `W/h` such squares produce the global
`a² W h³ / 768` squared lower bound, and the Hilbert-space Falk theorem supplies
the matching upper bound for the actual continuous/discrete VI solutions.
-/

/-- Summing the explicit per-square flat-prism obstruction over at least `W/h`
interface squares yields the exact global squared lower constant. -/
theorem flatInterface_squareEnergies_lowerSq
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (error a W h : ℝ)
    (hh : 0 < h)
    (hsumSq : ∑ i ∈ S, energy i ≤ error ^ 2)
    (hlocal : ∀ i ∈ S, a ^ 2 * h ^ 4 / 768 ≤ energy i)
    (hcount : W / h ≤ (S.card : ℝ)) :
    a ^ 2 * W * h ^ 3 / 768 ≤ error ^ 2 := by
  have hq : 0 ≤ a ^ 2 * h ^ 4 / 768 := by positivity
  have hcardScaled :
      (W / h) * (a ^ 2 * h ^ 4 / 768) ≤
        (S.card : ℝ) * (a ^ 2 * h ^ 4 / 768) :=
    mul_le_mul_of_nonneg_right hcount hq
  have hsumLower :
      (S.card : ℝ) * (a ^ 2 * h ^ 4 / 768) ≤
        ∑ i ∈ S, energy i :=
    card_mul_le_sum_of_le S energy (a ^ 2 * h ^ 4 / 768) hlocal
  calc
    a ^ 2 * W * h ^ 3 / 768 =
        (W / h) * (a ^ 2 * h ^ 4 / 768) := by
      field_simp [ne_of_gt hh]
    _ ≤ (S.card : ℝ) * (a ^ 2 * h ^ 4 / 768) := hcardScaled
    _ ≤ ∑ i ∈ S, energy i := hsumLower
    _ ≤ error ^ 2 := hsumSq

/-- The same global lower bound starting directly from the certified pair-of-prisms
formula `(h/2) * (a² h³/384)` in every interface square. -/
theorem flatInterface_prismPairs_lowerSq
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (error a W h : ℝ)
    (hh : 0 < h)
    (hsumSq : ∑ i ∈ S, energy i ≤ error ^ 2)
    (hlocal : ∀ i ∈ S,
      (h / 2) * (a ^ 2 * h ^ 3 / 384) ≤ energy i)
    (hcount : W / h ≤ (S.card : ℝ)) :
    a ^ 2 * W * h ^ 3 / 768 ≤ error ^ 2 := by
  apply flatInterface_squareEnergies_lowerSq
    S energy error a W h hh hsumSq
  · intro i hi
    have hp := hlocal i hi
    rw [flatPrism_pair_squareContribution] at hp
    exact hp
  · exact hcount

section HilbertFlat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Fully aggregated flat-interface theorem for continuous/discrete Hilbert VI
solutions. The global lower bound is derived from local square energies and the
interface-square count; the upper bound is derived from the VI Falk estimate. -/
theorem flatInterface_hilbertVI_sharp_of_squareEnergies
    {ι : Type*}
    (S : Finset ι) (energy : ι → ℝ)
    (K Kh : Set E) (z u uh vh : E)
    (a W h : ℝ)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (hh : 0 < h)
    (hsub : Kh ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (huh : IsHilbertVISolution Kh z uh)
    (hvh : vh ∈ Kh)
    (hsumSq : ∑ i ∈ S, energy i ≤ ‖u - uh‖ ^ 2)
    (hlocal : ∀ i ∈ S, a ^ 2 * h ^ 4 / 768 ≤ energy i)
    (hcount : W / h ≤ (S.card : ℝ))
    (hcomparison : ‖u - vh‖ ^ 2 = a ^ 2 * W * h ^ 3 / 24)
    (hconsistency : ⟪u - z, vh - u⟫_ℝ = a ^ 2 * W * h ^ 3 / 48) :
    (a * Real.sqrt (W / 768)) * (h * Real.sqrt h) ≤ ‖u - uh‖ ∧
      ‖u - uh‖ ≤ (a * Real.sqrt (W / 12)) * (h * Real.sqrt h) := by
  have hprismLower := flatInterface_squareEnergies_lowerSq
    S energy ‖u - uh‖ a W h hh hsumSq hlocal hcount
  exact flatInterface_hilbertVI_sharp
    K Kh z u uh vh a W h ha hW hh.le hsub hu huh hvh
    hprismLower hcomparison hconsistency

/-- Explicit pair-of-prisms version of the fully aggregated Hilbert-VI theorem.
The global scalar lower-bound hypothesis has disappeared completely. -/
theorem flatInterface_hilbertVI_sharp_from_prismPairs
    {ι : Type*}
    (S : Finset ι) (energy : ι → ℝ)
    (K Kh : Set E) (z u uh vh : E)
    (a W h : ℝ)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (hh : 0 < h)
    (hsub : Kh ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (huh : IsHilbertVISolution Kh z uh)
    (hvh : vh ∈ Kh)
    (hsumSq : ∑ i ∈ S, energy i ≤ ‖u - uh‖ ^ 2)
    (hlocal : ∀ i ∈ S,
      (h / 2) * (a ^ 2 * h ^ 3 / 384) ≤ energy i)
    (hcount : W / h ≤ (S.card : ℝ))
    (hcomparison : ‖u - vh‖ ^ 2 = a ^ 2 * W * h ^ 3 / 24)
    (hconsistency : ⟪u - z, vh - u⟫_ℝ = a ^ 2 * W * h ^ 3 / 48) :
    (a * Real.sqrt (W / 768)) * (h * Real.sqrt h) ≤ ‖u - uh‖ ∧
      ‖u - uh‖ ≤ (a * Real.sqrt (W / 12)) * (h * Real.sqrt h) := by
  have hprismLower := flatInterface_prismPairs_lowerSq
    S energy ‖u - uh‖ a W h hh hsumSq hlocal hcount
  exact flatInterface_hilbertVI_sharp
    K Kh z u uh vh a W h ha hW hh.le hsub hu huh hvh
    hprismLower hcomparison hconsistency

/-- Exact-width specialization: `n` interface squares of width `h` cover a
flat segment of length `n h`, so no separate square-count hypothesis remains. -/
theorem flatInterface_hilbertVI_sharp_of_finPatch
    {n : ℕ}
    (energy : Fin n → ℝ)
    (K Kh : Set E) (z u uh vh : E)
    (a h : ℝ)
    (ha : 0 ≤ a) (hh : 0 < h)
    (hsub : Kh ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (huh : IsHilbertVISolution Kh z uh)
    (hvh : vh ∈ Kh)
    (hsumSq : ∑ i, energy i ≤ ‖u - uh‖ ^ 2)
    (hlocal : ∀ i,
      (h / 2) * (a ^ 2 * h ^ 3 / 384) ≤ energy i)
    (hcomparison : ‖u - vh‖ ^ 2 =
      a ^ 2 * ((n : ℝ) * h) * h ^ 3 / 24)
    (hconsistency : ⟪u - z, vh - u⟫_ℝ =
      a ^ 2 * ((n : ℝ) * h) * h ^ 3 / 48) :
    (a * Real.sqrt (((n : ℝ) * h) / 768)) * (h * Real.sqrt h) ≤ ‖u - uh‖ ∧
      ‖u - uh‖ ≤
        (a * Real.sqrt (((n : ℝ) * h) / 12)) * (h * Real.sqrt h) := by
  have hW : 0 ≤ (n : ℝ) * h :=
    mul_nonneg (Nat.cast_nonneg n) hh.le
  have hcount : ((n : ℝ) * h) / h ≤
      ((Finset.univ : Finset (Fin n)).card : ℝ) := by
    have hh0 : h ≠ 0 := ne_of_gt hh
    simp [hh0]
  apply flatInterface_hilbertVI_sharp_from_prismPairs
    (Finset.univ : Finset (Fin n)) energy K Kh z u uh vh
    a ((n : ℝ) * h) h ha hW hh hsub hu huh hvh
  · simpa using hsumSq
  · intro i hi
    exact hlocal i
  · exact hcount
  · exact hcomparison
  · exact hconsistency

end HilbertFlat

end

end BernsteinObstacle
