import BernsteinObstacle.HilbertVI
import BernsteinObstacle.FlatInterfaceBenchmark
import Mathlib.Tactic

open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Hilbert-space Falk transfer

This file removes the remaining abstract upper-transfer oracle from the explicit
flat-interface benchmark.  The classical Falk estimate follows directly from the
continuous and discrete projection variational inequalities when the discrete
feasible set is contained in the continuous one.
-/

section Falk

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hilbert-space Falk inequality for nested obstacle feasible sets.

If `u` solves the variational inequality on `K`, `uh` solves it on `Kh ⊆ K`,
and `vh ∈ Kh` is any feasible comparison function, then

`‖u-uh‖² ≤ ‖u-vh‖² + 2 ⟪u-z, vh-u⟫`.

The second term is the obstacle consistency/multiplier contribution. -/
theorem hilbert_falk_error_sq
    (K Kh : Set E) (z u uh vh : E)
    (hsub : Kh ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (huh : IsHilbertVISolution Kh z uh)
    (hvh : vh ∈ Kh) :
    ‖u - uh‖ ^ 2 ≤
      ‖u - vh‖ ^ 2 + 2 * ⟪u - z, vh - u⟫_ℝ := by
  have huhK : uh ∈ K := hsub huh.1
  have hcontinuous := hilbert_vi_pythagorean u uh z (hu.2 uh huhK)
  have hdiscrete := hilbert_vi_pythagorean uh vh z (huh.2 vh hvh)
  have hdist : ‖uh - z‖ ^ 2 ≤ ‖vh - z‖ ^ 2 := by
    nlinarith [sq_nonneg ‖vh - uh‖]
  have hgap :
      ‖uh - u‖ ^ 2 ≤ ‖vh - z‖ ^ 2 - ‖u - z‖ ^ 2 := by
    nlinarith
  have hvz : vh - z = (vh - u) + (u - z) := by
    abel
  have hleft : ⟪vh - u, vh - u⟫_ℝ = ‖vh - u‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (vh - u))
  have hright : ⟪u - z, u - z⟫_ℝ = ‖u - z‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (u - z))
  have hexpand :
      ‖vh - z‖ ^ 2 - ‖u - z‖ ^ 2 =
        ‖vh - u‖ ^ 2 + 2 * ⟪u - z, vh - u⟫_ℝ := by
    calc
      ‖vh - z‖ ^ 2 - ‖u - z‖ ^ 2 =
          ⟪(vh - u) + (u - z), (vh - u) + (u - z)⟫_ℝ -
            ‖u - z‖ ^ 2 := by
        rw [← hvz]
        symm
        congr 1
        simpa using
          (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (vh - z))
      _ = ‖vh - u‖ ^ 2 + 2 * ⟪u - z, vh - u⟫_ℝ := by
        rw [real_inner_add_add_self, hleft, hright]
        rw [real_inner_comm (vh - u) (u - z)]
        ring
  rw [hexpand] at hgap
  have hnormError : ‖u - uh‖ = ‖uh - u‖ := norm_sub_rev u uh
  have hnormApprox : ‖u - vh‖ = ‖vh - u‖ := norm_sub_rev u vh
  rw [hnormError, hnormApprox]
  exact hgap

/-- The flat benchmark's exact comparison energy and multiplier constants give
its explicit upper squared-error constant through the certified Falk estimate. -/
theorem flatInterface_hilbertVI_upperSq
    (K Kh : Set E) (z u uh vh : E)
    (a W h : ℝ)
    (hsub : Kh ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (huh : IsHilbertVISolution Kh z uh)
    (hvh : vh ∈ Kh)
    (hcomparison : ‖u - vh‖ ^ 2 = a ^ 2 * W * h ^ 3 / 24)
    (hconsistency : ⟪u - z, vh - u⟫_ℝ = a ^ 2 * W * h ^ 3 / 48) :
    ‖u - uh‖ ^ 2 ≤ a ^ 2 * W * h ^ 3 / 12 := by
  have hFalk := hilbert_falk_error_sq K Kh z u uh vh hsub hu huh hvh
  rw [hcomparison, hconsistency] at hFalk
  nlinarith

/-- Fully composed flat-interface Hilbert-VI sharp theorem.

The lower hypothesis is exactly the global domination by the two retained
prisms per interface square.  The upper estimate is no longer assumed: it is
derived from the continuous/discrete variational inequalities and the exact
comparison/multiplier identities. -/
theorem flatInterface_hilbertVI_sharp
    (K Kh : Set E) (z u uh vh : E)
    (a W h : ℝ)
    (ha : 0 ≤ a) (hW : 0 ≤ W) (hh : 0 ≤ h)
    (hsub : Kh ⊆ K)
    (hu : IsHilbertVISolution K z u)
    (huh : IsHilbertVISolution Kh z uh)
    (hvh : vh ∈ Kh)
    (hprismLower : a ^ 2 * W * h ^ 3 / 768 ≤ ‖u - uh‖ ^ 2)
    (hcomparison : ‖u - vh‖ ^ 2 = a ^ 2 * W * h ^ 3 / 24)
    (hconsistency : ⟪u - z, vh - u⟫_ℝ = a ^ 2 * W * h ^ 3 / 48) :
    (a * Real.sqrt (W / 768)) * (h * Real.sqrt h) ≤ ‖u - uh‖ ∧
      ‖u - uh‖ ≤ (a * Real.sqrt (W / 12)) * (h * Real.sqrt h) := by
  have hupperSq := flatInterface_hilbertVI_upperSq
    K Kh z u uh vh a W h hsub hu huh hvh hcomparison hconsistency
  exact flatBenchmark_sharp_sandwich
    a W h ‖u - uh‖ ha hW hh (norm_nonneg _) hprismLower hupperSq

end Falk

end

end BernsteinObstacle
