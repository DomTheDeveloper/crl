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
has an arbitrary-partition obstruction: for every partition indexed by a
nontrivial type, one cell has a non-syndetic self-sumset.  No finiteness
assumption on the index type is needed.
-/
theorem cassels_set_arbitrary_partition_obstruction
    {ι : Type*} [Nontrivial ι]
    (parts : ι → Set ℕ)
    (hcover : ∀ x, x ∈ Erdos741.cassels_set ↔ ∃ i, x ∈ parts i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (parts i) (parts j)) :
    ∃ i, ¬ IsSyndetic (parts i + parts i) := by
  by_contra hnone
  have hall : ∀ i, IsSyndetic (parts i + parts i) := by
    intro i
    by_contra hnot
    exact hnone ⟨i, hnot⟩

  obtain ⟨i0, i1, hi01⟩ := exists_pair_ne ι
  let rest : Set ℕ := {x | ∃ i, i ≠ i0 ∧ x ∈ parts i}

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
    exact ⟨i1, hi01.symm, hx⟩

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

/-- Closed existential form of the arbitrary-partition strengthening. -/
theorem exists_basis_with_arbitrary_partition_obstruction :
    ∃ A : Set ℕ,
      IsAddBasisOfOrder (A ∪ {0}) 2 ∧
      ∀ (ι : Type), Nontrivial ι →
        ∀ (parts : ι → Set ℕ),
          (∀ x, x ∈ A ↔ ∃ i, x ∈ parts i) →
          (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) →
          ∃ i, ¬ IsSyndetic (parts i + parts i) := by
  refine ⟨Erdos741.cassels_set, ?_, ?_⟩
  · exact Erdos741.cassels_set_is_good.1
  · intro ι hι parts hcover hdisj
    letI : Nontrivial ι := hι
    exact cassels_set_arbitrary_partition_obstruction parts hcover hdisj

#print axioms Erdos741Finite.exists_basis_with_arbitrary_partition_obstruction

end Erdos741Finite
