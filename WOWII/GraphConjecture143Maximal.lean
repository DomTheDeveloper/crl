import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
Finite maximum-cardinality selection used in the two-leaf branch of WOWII 143.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Any inhabited property of finite vertex sets has a witness of maximum
cardinality. -/
lemma exists_max_card_finset (P : Finset α → Prop) [DecidablePred P]
    (hP : ∃ s : Finset α, P s) :
    ∃ s : Finset α, P s ∧ ∀ t : Finset α, P t → t.card ≤ s.card := by
  let C : Finset (Finset α) := Finset.univ.powerset.filter P
  have hC : C.Nonempty := by
    obtain ⟨s, hs⟩ := hP
    refine ⟨s, ?_⟩
    simp [C, hs]
  let M : Finset ℕ := C.image Finset.card
  have hM : M.Nonempty := Finset.image_nonempty.mpr hC
  let m := M.max' hM
  have hmM : m ∈ M := M.max'_mem hM
  obtain ⟨s, hsC, hscard⟩ := Finset.mem_image.mp hmM
  refine ⟨s, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hsC).2
  · intro t ht
    have htC : t ∈ C := by simp [C, ht]
    have htM : t.card ∈ M := Finset.mem_image.mpr ⟨t, htC, rfl⟩
    have hle : t.card ≤ m := M.le_max' t.card htM
    simpa [m, hscard] using hle

end WrittenOnTheWallII.GraphConjecture143
