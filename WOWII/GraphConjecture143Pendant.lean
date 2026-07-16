import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
Pendant-extension lemma for the maximal induced-tree argument in WOWII 143.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Adding a new vertex with exactly one neighbor in an induced tree preserves
the induced-tree property. -/
lemma induce_insert_isTree_of_unique_neighbor {G : SimpleGraph α}
    [DecidableRel G.Adj] {S : Finset α} {z a : α}
    (hzS : z ∉ S) (haS : a ∈ S) (hza : G.Adj z a)
    (huniq : ∀ b ∈ S, G.Adj z b → b = a)
    (hT : (G.induce (S : Set α)).IsTree) :
    (G.induce ((insert z S : Finset α) : Set α)).IsTree := by
  let H := G.induce (S : Set α)
  let H' := G.induce ((insert z S : Finset α) : Set α)
  let aH : (S : Set α) := ⟨a, by simpa using haS⟩
  let aH' : ((insert z S : Finset α) : Set α) := ⟨a, by simp [haS]⟩
  let zH' : ((insert z S : Finset α) : Set α) := ⟨z, by simp⟩
  have hconn : H'.Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨aH', ?_⟩
    intro w
    by_cases hwz : (w : α) = z
    · have hw : w = zH' := by exact Subtype.ext hwz
      subst w
      exact Adj.reachable (by simpa [H', aH', zH'] using hza.symm)
    · have hwS : (w : α) ∈ S := by
        have hwmem := w.property
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hwmem
        exact hwmem.resolve_left hwz
      let wH : (S : Set α) := ⟨w, by simpa using hwS⟩
      let incl : H →g H' :=
        ⟨fun x => ⟨x.1, by simp [x.2]⟩, fun h => h⟩
      have hr : H.Reachable aH wH := by
        change (G.induce (S : Set α)).Reachable aH wH
        exact hT.1 aH wH
      simpa [aH, aH', wH, incl] using hr.map incl
  refine ⟨hconn, ?_⟩
  intro u c hc
  by_cases hzc : zH' ∈ c.support
  · let r := c.rotate hzc
    have hr : r.IsCycle := hc.rotate hzc
    have hzs : H'.Adj zH' r.snd := r.adj_snd hr.not_nil
    have hzp : H'.Adj zH' r.penultimate := (r.adj_penultimate hr.not_nil).symm
    have hsS : (r.snd : α) ∈ S := by
      have hs := r.snd.property
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hs
      exact hs.resolve_left fun h => hzs.ne (Subtype.ext h.symm)
    have hpS : (r.penultimate : α) ∈ S := by
      have hp := r.penultimate.property
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hp
      exact hp.resolve_left fun h => hzp.ne (Subtype.ext h.symm)
    have hsa : (r.snd : α) = a := huniq _ hsS (by exact hzs)
    have hpa : (r.penultimate : α) = a := huniq _ hpS (by exact hzp)
    apply hr.snd_ne_penultimate
    apply Subtype.ext
    exact hsa.trans hpa.symm
  · have hcsub : c.mapToSubgraph.IsCycle := by
      have hmapped : (c.mapToSubgraph.map c.toSubgraph.hom).IsCycle := by
        rw [c.map_mapToSubgraph_hom]
        exact hc
      exact (Walk.map_isCycle_iff_of_injective Subtype.val_injective).mp hmapped
    let f : c.toSubgraph.coe →g H :=
      ⟨fun x => ⟨x.1.1, by
          have hxSupp : x.1 ∈ c.support := c.mem_verts_toSubgraph.mp x.2
          have hxmem := x.1.2
          simp only [Finset.coe_insert, Set.mem_insert_iff] at hxmem
          exact hxmem.resolve_left fun hxz => hzc (by
            have : x.1 = zH' := Subtype.ext hxz
            simpa [this] using hxSupp)⟩,
        fun h => by exact c.toSubgraph.adj_sub h⟩
    have hfinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg (fun q : (S : Set α) => (q : α)) hxy
      simpa [f] using hval
    have hcH : (c.mapToSubgraph.map f).IsCycle := hcsub.map hfinj
    have hA : H.IsAcyclic := by
      simpa [H] using hT.2
    exact hA _ hcH

end WrittenOnTheWallII.GraphConjecture143