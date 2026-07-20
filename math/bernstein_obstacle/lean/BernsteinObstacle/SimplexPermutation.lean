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
  · simpa using e.sum_comp x.1

/-- Renumber the components of a degree-`n` simplex multi-index. -/
def permuteMultiIndex (d n : ℕ)
    (e : Fin (d + 1) ≃ Fin (d + 1))
    (α : MultiIndex d n) : MultiIndex d n := by
  refine ⟨fun i => α.1 (e i), ?_⟩
  simpa using e.sum_comp (fun i => (α.1 i : ℕ))

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
  rw [← Equiv.sum_comp
    (Equiv.ofBijective (permuteMultiIndex d n e)
      ⟨by
        intro α β h
        have h' := congrArg
          (permuteMultiIndex d n e.symm) h
        simpa [permuteMultiIndex_trans] using h',
       by
        intro β
        refine ⟨permuteMultiIndex d n e.symm β, ?_⟩
        simpa [permuteMultiIndex_trans]⟩)]
  apply Finset.sum_congr rfl
  intro α hα
  rw [simplexBasis_permute]
  congr 1
  simpa [permuteMultiIndex_trans]

end

end BernsteinObstacle
