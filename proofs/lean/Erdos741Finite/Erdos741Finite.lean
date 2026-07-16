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
For the Cassels basis, two distinct cells of any partition cannot both have
syndetic self-sumsets.  Thus every partition has at most one syndetic cell.
No finiteness or countability assumption on the index type is needed.
-/
theorem cassels_set_at_most_one_syndetic_cell
    {ι : Type*}
    (parts : ι → Set ℕ)
    (hcover : ∀ x, x ∈ Erdos741.cassels_set ↔ ∃ i, x ∈ parts i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (i j : ι) (hij : i ≠ j) :
    ¬ (IsSyndetic (parts i + parts i) ∧ IsSyndetic (parts j + parts j)) := by
  rintro ⟨hsyni, hsynj⟩
  let rest : Set ℕ := {x | ∃ k, k ≠ i ∧ x ∈ parts k}

  have hpartition : Erdos741.cassels_set = parts i ∪ rest := by
    ext x
    constructor
    · intro hx
      rcases (hcover x).mp hx with ⟨k, hk⟩
      by_cases hki : k = i
      · left
        simpa [hki] using hk
      · right
        exact ⟨k, hki, hk⟩
    · intro hx
      rcases hx with hxi | hxrest
      · exact (hcover x).mpr ⟨i, hxi⟩
      · rcases hxrest with ⟨k, -, hk⟩
        exact (hcover x).mpr ⟨k, hk⟩

  have hdisjirest : Disjoint (parts i) rest := by
    refine Set.disjoint_left.2 ?_
    intro x hxi hxrest
    rcases hxrest with ⟨k, hki, hxk⟩
    exact (Set.disjoint_left.1 (hdisj i k (Ne.symm hki))) hxi hxk

  have hsub_j : parts j ⊆ rest := by
    intro x hx
    exact ⟨j, hij.symm, hx⟩

  have hsub_sum : parts j + parts j ⊆ rest + rest := by
    intro x hx
    rcases hx with ⟨a, ha, b, hb, hab⟩
    use a
    constructor
    · exact hsub_j ha
    · use b
      exact ⟨hsub_j hb, hab⟩

  have hsynRest : IsSyndetic (rest + rest) :=
    isSyndetic_mono hsub_sum hsynj

  have hgood := Erdos741.cassels_set_is_good
  unfold Erdos741.GoodCasselsProperty at hgood
  rcases hgood with ⟨-, hgap⟩
  have hcases := hgap (parts i) rest hpartition hdisjirest
  rcases hcases with hgapi | hgapRest
  · exact (Erdos741.not_syndetic_of_large_gaps (parts i + parts i) hgapi) hsyni
  · exact (Erdos741.not_syndetic_of_large_gaps (rest + rest) hgapRest) hsynRest

/-- Every partition indexed by a nontrivial type has a non-syndetic cell. -/
theorem cassels_set_arbitrary_partition_obstruction
    {ι : Type*} [Nontrivial ι]
    (parts : ι → Set ℕ)
    (hcover : ∀ x, x ∈ Erdos741.cassels_set ↔ ∃ i, x ∈ parts i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (parts i) (parts j)) :
    ∃ i, ¬ IsSyndetic (parts i + parts i) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  by_cases hi : IsSyndetic (parts i + parts i)
  · exact ⟨j, fun hj => cassels_set_at_most_one_syndetic_cell parts hcover hdisj i j hij ⟨hi, hj⟩⟩
  · exact ⟨i, hi⟩

/--
Closed existential form: there is an additive basis of order two such that,
in every partition indexed by any type, at most one cell has a syndetic
self-sumset.
-/
theorem exists_basis_with_at_most_one_syndetic_cell :
    ∃ A : Set ℕ,
      IsAddBasisOfOrder (A ∪ {0}) 2 ∧
      ∀ (ι : Type) (parts : ι → Set ℕ),
        (∀ x, x ∈ A ↔ ∃ i, x ∈ parts i) →
        (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) →
        ∀ i j, i ≠ j →
          ¬ (IsSyndetic (parts i + parts i) ∧ IsSyndetic (parts j + parts j)) := by
  refine ⟨Erdos741.cassels_set, Erdos741.cassels_set_is_good.1, ?_⟩
  intro ι parts hcover hdisj i j hij
  exact cassels_set_at_most_one_syndetic_cell parts hcover hdisj i j hij

#print axioms Erdos741Finite.exists_basis_with_at_most_one_syndetic_cell

end Erdos741Finite
