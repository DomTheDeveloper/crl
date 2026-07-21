import BernsteinObstacle.CutPatchSaturation
import BernsteinObstacle.FlatInterfaceBenchmark
import BernsteinObstacle.HilbertFalk
import Mathlib.Tactic

open scoped BigOperators InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Global flat-interface prism lower bound

This module removes the remaining global scalar lower-bound oracle from the
explicit flat-interface Hilbert-VI theorem.  The two retained prisms in each
interface square contribute `a² h⁴ / 768`; at least `W / h` interface squares
therefore contribute `a² W h³ / 768` globally.
-/

/-- Summing the certified pair-of-prisms obstruction over a flat interface
patch gives the exact global squared lower constant.

The only physical localization input is `hsumSq`: the retained disjoint local
energies are dominated by the global squared error. -/
theorem flatInterface_prismPatch_lowerSq
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (error a W h : ℝ)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (hh : 0 < h)
    (hsumSq : ∑ i ∈ S, energy i ≤ error ^ 2)
    (hlocal : ∀ i ∈ S,
      (h / 2) * (a ^ 2 * h ^ 3 / 384) ≤ energy i)
    (hcard : W / h ≤ (S.card : ℝ)) :
    a ^ 2 * W * h ^ 3 / 768 ≤ error ^ 2 := by
  have hC : 0 ≤ a ^ 2 / 768 := by positivity
  have henergy : ∀ i ∈ S,
      (a ^ 2 / 768) * h ^ (2 + 2) ≤ energy i := by
    intro i hi
    have hp := hlocal i hi
    rw [flatPrism_pair_squareContribution] at hp
    convert hp using 1 <;> norm_num <;> ring
  have hcard' : W / h ^ (2 - 1) ≤ (S.card : ℝ) := by
    simpa using hcard
  have hsumLower := cutPatch_sum_energy_ge_cubic
    S energy (a ^ 2 / 768) W h 2 (by norm_num) hh hC hW henergy hcard'
  calc
    a ^ 2 * W * h ^ 3 / 768 = (a ^ 2 / 768) * W * h ^ 3 := by ring
    _ ≤ ∑ i ∈ S, energy i := hsumLower
    _ ≤ error ^ 2 := hsumSq

/-- The fully composed explicit flat-interface theorem for the actual
continuous and discrete Hilbert variational-inequality solutions.

Compared with `flatInterface_hilbertVI_sharp`, the global scalar lower-bound
hypothesis has disappeared: it is reconstructed by finite prism summation. -/
theorem flatInterface_hilbertVI_sharp_from_prismPatch
    {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (hcard : W / h ≤ (S.card : ℝ))
    (hcomparison : ‖u - vh‖ ^ 2 = a ^ 2 * W * h ^ 3 / 24)
    (hconsistency : ⟪u - z, vh - u⟫_ℝ = a ^ 2 * W * h ^ 3 / 48) :
    (a * Real.sqrt (W / 768)) * (h * Real.sqrt h) ≤ ‖u - uh‖ ∧
      ‖u - uh‖ ≤ (a * Real.sqrt (W / 12)) * (h * Real.sqrt h) := by
  have hprismLower : a ^ 2 * W * h ^ 3 / 768 ≤ ‖u - uh‖ ^ 2 :=
    flatInterface_prismPatch_lowerSq
      S energy ‖u - uh‖ a W h ha hW hh hsumSq hlocal hcard
  exact flatInterface_hilbertVI_sharp
    K Kh z u uh vh a W h ha hW (le_of_lt hh)
    hsub hu huh hvh hprismLower hcomparison hconsistency

/-- Exact-width specialization: `n` interface squares of width `h` cover a
flat segment of length `n h`, so no separate cardinality hypothesis is needed. -/
theorem flatInterface_hilbertVI_sharp_of_finPatch
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
  have hW : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg n) (le_of_lt hh)
  have hcard : ((n : ℝ) * h) / h ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) := by
    have hh0 : h ≠ 0 := ne_of_gt hh
    simp [hh0]
  apply flatInterface_hilbertVI_sharp_from_prismPatch
    (Finset.univ : Finset (Fin n)) energy K Kh z u uh vh
    a ((n : ℝ) * h) h ha hW hh hsub hu huh hvh
  · simpa using hsumSq
  · intro i hi
    exact hlocal i
  · exact hcard
  · exact hcomparison
  · exact hconsistency

end

end BernsteinObstacle
