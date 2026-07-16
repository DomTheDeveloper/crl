import WOWII.ZZGraphConjecture314Core
import WOWII.ZZGraphConjecture314Cycle5

/-!
Well-total-domination of surjective blow-ups of the 5-cycle.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- In a surjective blow-up of `C₅`, the image of a minimal total dominating set
on the five bags is again a minimal total dominating set, and cardinality is preserved. -/
lemma image_minimalTDS_cycle5_of_blowup
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (bag : α → Fin 5) (hbag : Function.Surjective bag)
    (hAdj : ∀ x y : α,
      G.Adj x y ↔ (cycleGraph 5).Adj (bag x) (bag y))
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) :
    IsMinimalTotalDominatingSet (cycleGraph 5) (S.image bag) ∧
      (S.image bag).card = S.card := by
  have hinjS : Set.InjOn bag (S : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    have htwin : ∀ z : α, G.Adj z x ↔ G.Adj z y := by
      intro z
      rw [hAdj z x, hAdj z y, hxy]
    exact (not_both_mem_minimalTDS_of_false_twins G hS hne htwin) ⟨hx, hy⟩
  have hcard : (S.image bag).card = S.card :=
    Finset.card_image_of_injOn hinjS
  have htds : IsTotalDominatingSet (cycleGraph 5) (S.image bag) := by
    intro i
    obtain ⟨x, rfl⟩ := hbag i
    obtain ⟨y, hyS, hxy⟩ := hS.1 x
    exact ⟨bag y, Finset.mem_image.mpr ⟨y, hyS, rfl⟩, (hAdj x y).mp hxy⟩
  refine ⟨⟨htds, ?_⟩, hcard⟩
  intro T hTB
  obtain ⟨b, hbB, hbT⟩ := Finset.exists_of_ssubset hTB
  obtain ⟨s, hsS, hsb⟩ := Finset.mem_image.mp hbB
  obtain ⟨x, hxs, hpriv⟩ :=
    exists_private_neighbor_of_mem_minimalTDS G hS hsS
  intro hTdom
  obtain ⟨t, htT, hxt⟩ := hTdom (bag x)
  have htB : t ∈ S.image bag := hTB.1 htT
  obtain ⟨y, hyS, hyt⟩ := Finset.mem_image.mp htB
  have hxy : G.Adj x y := by
    apply (hAdj x y).mpr
    simpa [hyt] using hxt
  have hys : y = s := hpriv y hyS hxy
  have htb : t = b := by
    rw [← hyt, hys, hsb]
  exact hbT (htb ▸ htT)

/-- Every minimal total dominating set of a surjective blow-up of `C₅` has size three. -/
lemma minimalTDS_card_eq_three_of_cycle5_blowup
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (bag : α → Fin 5) (hbag : Function.Surjective bag)
    (hAdj : ∀ x y : α,
      G.Adj x y ↔ (cycleGraph 5).Adj (bag x) (bag y))
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) :
    S.card = 3 := by
  obtain ⟨hB, hcard⟩ := image_minimalTDS_cycle5_of_blowup G bag hbag hAdj hS
  have hB3 := cycleGraph_five_minimalTDS_card_eq_three (S.image bag) hB
  omega

/-- Every surjective blow-up of `C₅` is well totally dominated. -/
lemma isWellTotallyDominated_of_cycle5_blowup
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (bag : α → Fin 5) (hbag : Function.Surjective bag)
    (hAdj : ∀ x y : α,
      G.Adj x y ↔ (cycleGraph 5).Adj (bag x) (bag y)) :
    IsWellTotallyDominated G := by
  intro S T hS hT
  rw [minimalTDS_card_eq_three_of_cycle5_blowup G bag hbag hAdj hS,
    minimalTDS_card_eq_three_of_cycle5_blowup G bag hbag hAdj hT]

end WrittenOnTheWallII.GraphConjecture314
