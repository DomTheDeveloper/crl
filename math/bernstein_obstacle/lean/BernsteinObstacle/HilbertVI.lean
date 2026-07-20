import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped InnerProductSpace

namespace BernsteinObstacle

noncomputable section

/-!
# Hilbert-space variational inequalities

This file lifts the finite coefficient-space projection argument to an arbitrary
real inner-product space. It formalizes the exact Pythagorean estimate behind
obstacle variational inequalities and proves uniqueness of the projection/VI
solution without assuming coordinates or a finite mesh.
-/

section HilbertVI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point `u` in `K` solves the metric-projection variational inequality for
`z` when the residual `u - z` has nonnegative inner product with every feasible
direction `v - u`. -/
def IsHilbertVISolution (K : Set E) (z u : E) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, 0 ≤ ⟪u - z, v - u⟫_ℝ

/-- A feasible point minimizes squared distance to `z` over `K`. -/
def IsHilbertSqDistMinimizer (K : Set E) (z u : E) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, ‖u - z‖ ^ 2 ≤ ‖v - z‖ ^ 2

/-- The exact Hilbert-space Pythagorean inequality implied by the obstacle
variational inequality. -/
theorem hilbert_vi_pythagorean
    (u v z : E)
    (hvi : 0 ≤ ⟪u - z, v - u⟫_ℝ) :
    ‖v - u‖ ^ 2 + ‖u - z‖ ^ 2 ≤ ‖v - z‖ ^ 2 := by
  have hvz : v - z = (v - u) + (u - z) := by
    abel
  have hleft : ⟪v - u, v - u⟫_ℝ = ‖v - u‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (v - u))
  have hright : ⟪u - z, u - z⟫_ℝ = ‖u - z‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (u - z))
  have hnorm :
      ‖v - z‖ ^ 2 =
        ‖v - u‖ ^ 2 + 2 * ⟪u - z, v - u⟫_ℝ + ‖u - z‖ ^ 2 := by
    calc
      ‖v - z‖ ^ 2 = ‖(v - u) + (u - z)‖ ^ 2 := by rw [hvz]
      _ = ⟪(v - u) + (u - z), (v - u) + (u - z)⟫_ℝ := by
        symm
        simpa using
          (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) ((v - u) + (u - z)))
      _ = ‖v - u‖ ^ 2 + 2 * ⟪u - z, v - u⟫_ℝ + ‖u - z‖ ^ 2 := by
        rw [real_inner_add_add_self, hleft, hright]
        rw [real_inner_comm (v - u) (u - z)]
  linarith

/-- Recovery/competitor form of the Pythagorean estimate. -/
theorem hilbert_vi_error_sq_le_distance_gap
    (u v z : E)
    (hvi : 0 ≤ ⟪u - z, v - u⟫_ℝ) :
    ‖v - u‖ ^ 2 ≤ ‖v - z‖ ^ 2 - ‖u - z‖ ^ 2 := by
  have h := hilbert_vi_pythagorean u v z hvi
  linarith

/-- Every Hilbert-space VI solution minimizes squared distance over the feasible
set. -/
theorem hilbert_vi_is_sqDistMinimizer
    (K : Set E) (z u : E)
    (hu : IsHilbertVISolution K z u) :
    IsHilbertSqDistMinimizer K z u := by
  constructor
  · exact hu.1
  · intro v hv
    have h := hilbert_vi_pythagorean u v z (hu.2 v hv)
    nlinarith [sq_nonneg ‖v - u‖]

/-- A Hilbert-space obstacle VI has at most one solution. -/
theorem hilbert_vi_unique
    (K : Set E) (z u w : E)
    (hu : IsHilbertVISolution K z u)
    (hw : IsHilbertVISolution K z w) :
    u = w := by
  have huw := hilbert_vi_pythagorean u w z (hu.2 w hw.1)
  have hwu := hilbert_vi_pythagorean w u z (hw.2 u hu.1)
  have hnorm : ‖u - w‖ = ‖w - u‖ := norm_sub_rev u w
  have hsquare : ‖w - u‖ ^ 2 ≤ 0 := by
    rw [hnorm] at hwu
    linarith
  have hzero : ‖w - u‖ = 0 := by
    nlinarith [norm_nonneg (w - u)]
  have hsub : w - u = 0 := norm_eq_zero.mp hzero
  exact (sub_eq_zero.mp hsub).symm

end HilbertVI

end

end BernsteinObstacle
