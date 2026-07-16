import APNOutputs.ErdosProblems.erdos_741.parts.ii

open Set
open scoped Pointwise

namespace Erdos741Finite

/-- Syndeticity is upward closed under inclusion. -/
lemma isSyndetic_mono {S T : Set ℕ} (hST : S ⊆ T) (hS : IsSyndetic S) :
    IsSyndetic T := by
  unfold IsSyndetic at hS ⊢
  rcases hS with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro n
  rcases hp n with ⟨x, hx⟩
  exact ⟨x, hST hx.1, hx.2⟩

/--
The Cassels-type basis constructed in the AlphaProof solution of Erdős 741(ii)
has a stronger finite-partition obstruction: in every partition into at least
two pairwise-disjoint cells, one cell has a non-syndetic self-sumset.
-/
theorem cassels_set_finite_partition_obstruction
    (m : ℕ) (hm : 2 ≤ m)
    (parts : Fin m → Set ℕ)
    (hcover : ∀ x, x ∈ Erdos741.cassels_set ↔ ∃ i, x ∈ parts i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (parts i) (parts j)) :
    ∃ i, ¬ IsSyndetic (parts i + parts i) := by
  by_contra hnone
  have hall : ∀ i, IsSyndetic (parts i + parts i) := by
    intro i
    by_contra hnot
    exact hnone ⟨i, hnot⟩

  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let rest : Set ℕ := {x | ∃ i, i ≠ i0 ∧ x ∈ parts i}

  have hi10 : i1 ≠ i0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, i1] at hv

  have hpartition : Erdos741.cassels_set = parts i0 ∪ rest := by
    ext x
    constructor
    · intro hx
      rcases (hcover x).mp hx with ⟨i, hi⟩
      by_cases hieq : i = i0
      · left
        simpa [hieq] using hi
      · right
        exact ⟨i, hieq, hi⟩
    · intro hx
      rcases hx with hx0 | hxrest
      · exact (hcover x).mpr ⟨i0, hx0⟩
      · rcases hxrest with ⟨i, -, hi⟩
        exact (hcover x).mpr ⟨i, hi⟩

  have hdisj0rest : Disjoint (parts i0) rest := by
    refine Set.disjoint_left.2 ?_
    intro x hx0 hxrest
    rcases hxrest with ⟨i, hne, hi⟩
    exact (Set.disjoint_left.1 (hdisj i0 i (Ne.symm hne))) hx0 hi

  have hsub_i1 : parts i1 ⊆ rest := by
    intro x hx
    exact ⟨i1, hi10, hx⟩

  have hsub_sum : parts i1 + parts i1 ⊆ rest + rest := by
    intro x hx
    rcases hx with ⟨a, ha, b, hb, hab⟩
    use a
    constructor
    · exact hsub_i1 ha
    · use b
      exact ⟨hsub_i1 hb, hab⟩

  have hsyn0 : IsSyndetic (parts i0 + parts i0) := hall i0
  have hsynRest : IsSyndetic (rest + rest) :=
    isSyndetic_mono hsub_sum (hall i1)

  have hgood := Erdos741.cassels_set_is_good
  unfold Erdos741.GoodCasselsProperty at hgood
  rcases hgood with ⟨-, hgap⟩
  have hcases := hgap (parts i0) rest hpartition hdisj0rest
  rcases hcases with hgap0 | hgapRest
  · exact (Erdos741.not_syndetic_of_large_gaps (parts i0 + parts i0) hgap0) hsyn0
  · exact (Erdos741.not_syndetic_of_large_gaps (rest + rest) hgapRest) hsynRest

/-- Closed existential form, combining the upstream construction with the new upgrade lemma. -/
theorem exists_basis_with_finite_partition_obstruction :
    ∃ A : Set ℕ,
      IsAddBasisOfOrder (A ∪ {0}) 2 ∧
      ∀ (m : ℕ), 2 ≤ m →
        ∀ (parts : Fin m → Set ℕ),
          (∀ x, x ∈ A ↔ ∃ i, x ∈ parts i) →
          (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) →
          ∃ i, ¬ IsSyndetic (parts i + parts i) := by
  refine ⟨Erdos741.cassels_set, ?_, ?_⟩
  · exact Erdos741.cassels_set_is_good.1
  · intro m hm parts hcover hdisj
    exact cassels_set_finite_partition_obstruction m hm parts hcover hdisj

#print axioms Erdos741Finite.exists_basis_with_finite_partition_obstruction

end Erdos741Finite
