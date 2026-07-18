import WotW316

/-!
# Additional structural cases for Conjecture 316
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture316

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- In a connected graph, two adjacent pendant vertices force every vertex to be pendant. -/
theorem all_pendant_of_adjacent_pendants
    (hG : G.Connected) {l c : α}
    (hl : l ∈ pendantVertices G) (hc : c ∈ pendantVertices G) (hlc : G.Adj l c) :
    ∀ v : α, G.degree v = 1 := by
  classical
  have hdl : G.degree l = 1 := by simpa [pendantVertices] using hl
  have hdc : G.degree c = 1 := by simpa [pendantVertices] using hc
  have hul : ∀ w, G.Adj l w → w = c := by
    rcases (G.degree_eq_one_iff_existsUnique_adj).mp hdl with ⟨u, hlu, hu⟩
    intro w hlw
    exact (hu w hlw).trans (hu c hlc).symm
  have huc : ∀ w, G.Adj c w → w = l := by
    rcases (G.degree_eq_one_iff_existsUnique_adj).mp hdc with ⟨u, hcu, hu⟩
    intro w hcw
    exact (hu w hcw).trans (hu l hlc.symm).symm
  have hpair : ∀ v : α, G.Reachable l v → v = l ∨ v = c := by
    intro v hv
    rw [G.reachable_iff_reflTransGen l v] at hv
    induction hv with
    | refl => exact Or.inl rfl
    | @tail b d hreach hbd ih =>
        rcases ih with rfl | rfl
        · exact Or.inr (hul d hbd)
        · exact Or.inl (huc d hbd)
  intro v
  rcases hpair v (hG.preconnected l v) with rfl | rfl
  · exact hdl
  · exact hdc

/-- A complete graph is well totally dominated. -/
theorem wellTotallyDominated_of_complete [Nonempty α]
    (hcomplete : ∀ u v : α, u ≠ v → G.Adj u v) :
    G.IsWellTotallyDominated := by
  classical
  have hcard (S : Finset α) (hS : G.IsMinimalTotalDominatingSet S) : S.card = 2 := by
    let v₀ : α := Classical.choice (inferInstance : Nonempty α)
    rcases hS.1 v₀ with ⟨a, haS, _⟩
    rcases hS.1 a with ⟨b, hbS, hab⟩
    have habne : a ≠ b := hab.ne
    have hpairTDS : G.IsTotalDominatingSet {a, b} := by
      intro v
      by_cases hva : v = a
      · subst v
        exact ⟨b, by simp, hab⟩
      · exact ⟨a, by simp, hcomplete v a hva⟩
    have hpairSub : ({a, b} : Finset α) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haS
      · exact hbS
    have hEq : S = {a, b} := by
      by_contra hne
      have hss : ({a, b} : Finset α) ⊂ S :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hpairSub, fun h => hne h.symm⟩
      exact (hS.2 {a, b} hss) hpairTDS
    rw [hEq]
    simp [habne]
  intro S T hS hT
  rw [hcard S hS, hcard T hT]

#print axioms all_pendant_of_adjacent_pendants
#print axioms wellTotallyDominated_of_complete

end

end WrittenOnTheWallII.GraphConjecture316
