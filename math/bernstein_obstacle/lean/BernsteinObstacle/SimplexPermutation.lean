import BernsteinObstacle.Simplex
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Permutation invariance of simplicial Bernstein data

Renumbering barycentric coordinates by an equivalence preserves the simplex,
degree-`n` multi-indices, and the corresponding Bernstein basis value.  This
is the concrete orientation mechanism needed to transport the standard last
face results to arbitrary local face enumerations.
-/

/-- Renumber the barycentric coordinates of a simplex point. -/
def permuteBarycentricPoint (d : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1))
    (x : BarycentricPoint d) : BarycentricPoint d := by
  refine ⟨fun i => x.1 (e i), ?_, ?_⟩
  · intro i
    exact x.2.1 (e i)
  · calc
      (∑ i, x.1 (e i)) = ∑ i, x.1 i := e.sum_comp x.1
      _ = 1 := x.2.2

/-- Renumber the components of a degree-`n` simplex multi-index. -/
def permuteMultiIndex (d n : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1))
    (α : MultiIndex d n) : MultiIndex d n := by
  refine ⟨fun i => α.1 (e i), ?_⟩
  calc
    (∑ i, (α.1 (e i) : ℕ)) = ∑ i, (α.1 i : ℕ) :=
      e.sum_comp (fun i => (α.1 i : ℕ))
    _ = n := α.2

@[simp]
theorem permuteBarycentricPoint_apply (d : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1))
    (x : BarycentricPoint d) (i : Fin (d + 1)) :
    (permuteBarycentricPoint d e x).1 i = x.1 (e i) := by
  rfl

@[simp]
theorem permuteMultiIndex_apply (d n : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1))
    (α : MultiIndex d n) (i : Fin (d + 1)) :
    (permuteMultiIndex d n e α).1 i = α.1 (e i) := by
  rfl

/-- Renumbering by the identity equivalence changes nothing. -/
@[simp]
theorem permuteBarycentricPoint_refl (d : ℕ)
    (x : BarycentricPoint d) :
    permuteBarycentricPoint d (Equiv.refl _) x = x := by
  apply Subtype.ext
  funext i
  rfl

/-- Renumbering a multi-index by the identity equivalence changes nothing. -/
@[simp]
theorem permuteMultiIndex_refl (d n : ℕ)
    (α : MultiIndex d n) :
    permuteMultiIndex d n (Equiv.refl _) α = α := by
  apply Subtype.ext
  funext i
  rfl

/-- Successive coordinate renumberings compose. -/
theorem permuteBarycentricPoint_trans (d : ℕ)
    (e f : Fin (d + 1) ≃ Fin (d + 1))
    (x : BarycentricPoint d) :
    permuteBarycentricPoint d e (permuteBarycentricPoint d f x) =
      permuteBarycentricPoint d (e.trans f) x := by
  apply Subtype.ext
  funext i
  rfl

/-- Successive multi-index renumberings compose. -/
theorem permuteMultiIndex_trans (d n : ℕ)
    (e f : Fin (d + 1) ≃ Fin (d + 1))
    (α : MultiIndex d n) :
    permuteMultiIndex d n e (permuteMultiIndex d n f α) =
      permuteMultiIndex d n (e.trans f) α := by
  apply Subtype.ext
  funext i
  rfl

/-- Coordinate renumbering is an equivalence on degree-`n` multi-indices. -/
def permuteMultiIndexEquiv (d n : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1)) :
    MultiIndex d n ≃ MultiIndex d n where
  toFun := permuteMultiIndex d n e
  invFun := permuteMultiIndex d n e.symm
  left_inv α := by
    apply Subtype.ext
    funext i
    simp
  right_inv α := by
    apply Subtype.ext
    funext i
    simp

@[simp]
theorem permuteMultiIndex_symm_apply (d n : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1)) (α : MultiIndex d n) :
    permuteMultiIndex d n e.symm (permuteMultiIndex d n e α) = α :=
  (permuteMultiIndexEquiv d n e).left_inv α

/-- The simplicial Bernstein basis is invariant under simultaneous
renumbering of its barycentric point and multi-index. -/
theorem simplexBasis_permute (d n : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1))
    (α : MultiIndex d n) (x : BarycentricPoint d) :
    simplexBasis d n (permuteMultiIndex d n e α)
      (permuteBarycentricPoint d e x) =
      simplexBasis d n α x := by
  unfold simplexBasis
  have hfactorial :
      (∏ i : Fin (d + 1),
        (Nat.factorial ((permuteMultiIndex d n e α).1 i) : ℝ)) =
      ∏ i : Fin (d + 1), (Nat.factorial (α.1 i) : ℝ) := by
    simpa using e.prod_comp
      (fun i : Fin (d + 1) => (Nat.factorial (α.1 i) : ℝ))
  have hpowers :
      (∏ i : Fin (d + 1),
        ((permuteBarycentricPoint d e x).1 i) ^
          ((permuteMultiIndex d n e α).1 i : ℕ)) =
      ∏ i : Fin (d + 1), (x.1 i) ^ (α.1 i : ℕ) := by
    simpa using e.prod_comp
      (fun i : Fin (d + 1) => (x.1 i) ^ (α.1 i : ℕ))
  rw [hfactorial, hpowers]

/-- Simultaneous coordinate renumbering preserves a complete Bernstein field
when the coefficient function is transported by the same equivalence. -/
theorem simplexField_permute (d n : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1))
    (c : MultiIndex d n → ℝ) (x : BarycentricPoint d) :
    simplexField d n
        (fun α => c (permuteMultiIndex d n e.symm α))
        (permuteBarycentricPoint d e x) =
      simplexField d n c x := by
  unfold simplexField
  rw [← (permuteMultiIndexEquiv d n e).sum_comp]
  apply Finset.sum_congr rfl
  intro α hα
  change
    c (permuteMultiIndex d n e.symm (permuteMultiIndex d n e α)) *
        simplexBasis d n (permuteMultiIndex d n e α)
          (permuteBarycentricPoint d e x) =
      c α * simplexBasis d n α x
  rw [simplexBasis_permute, permuteMultiIndex_symm_apply]

end

end BernsteinObstacle
