import WOWII.GraphConjecture143Proof
import WOWII.ZZGraphConjecture314DominatingEdge

/-!
An explicit induced `P₅` supplies the five-vertex witness in the official
`largestInducedPathSize` invariant used by WOWII Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph
open WrittenOnTheWallII.GraphConjecture143

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma largestInducedPathSize_ge_five_of_FormsInducedP5
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {x0 x1 x2 x3 x4 : α}
    (h : FormsInducedP5 G x0 x1 x2 x3 x4) :
    5 ≤ largestInducedPathSize G := by
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34,
    ha01, ha12, ha23, ha34, hn02, hn03, hn04, hn13, hn14, hn24⟩
  let S : Finset α := {x0, x1, x2, x3, x4}
  let p : G.Walk x0 x4 :=
    .cons ha01 (.cons ha12 (.cons ha23 (.cons ha34 .nil)))
  have hp : p.IsPath := by
    simp [p, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
  have hScard : S.card = 5 := by
    simp [S, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
  have hsupp : p.support.toFinset = S := by
    simp [p, S]
  let hiso : G.induce (S : Set α) ≃g p.toSubgraph.coe :=
    { toFun := fun a => ⟨a, by
          have haFin : (a : α) ∈ p.support.toFinset := by
            rw [hsupp]
            simpa using a.property
          exact p.mem_verts_toSubgraph.mpr (by simpa using haFin)⟩
      invFun := fun a => ⟨a, by
          have haSupp : (a : α) ∈ p.support := p.mem_verts_toSubgraph.mp a.property
          have haFin : (a : α) ∈ p.support.toFinset := by simpa using haSupp
          rw [hsupp] at haFin
          simpa using haFin⟩
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rfl
      map_rel_iff' := by
        intro a b
        rcases a with ⟨a, ha⟩
        rcases b with ⟨b, hb⟩
        change p.toSubgraph.Adj a b ↔ G.Adj a b
        simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl | rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl | rfl | rfl <;>
          simp_all [p, Walk.toSubgraph, Subgraph.coe_adj, Sym2.eq, Sym2.rel_iff'] }
  have htree : (G.induce (S : Set α)).IsTree := by
    exact hiso.isTree_iff.mpr (path_toSubgraph_isTree hp)
  have hdeg : ∀ v : (S : Set α), (G.induce (S : Set α)).degree v ≤ 2 := by
    intro v
    have hdegree :
        (G.induce (S : Set α)).degree v = p.toSubgraph.coe.degree (hiso v) := by
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      exact Fintype.card_congr (hiso.mapNeighborSet v)
    let w : p.toSubgraph.verts := hiso v
    have hwdeg : p.toSubgraph.coe.degree w ≤ 2 := by
      have hwSupport : (w : α) ∈ p.support := p.mem_verts_toSubgraph.mp w.property
      obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hwSupport
      have hlen : p.length = 4 := by simp [p]
      have hi4 : i ≤ 4 := by simpa [hlen] using hil
      interval_cases i
      · have hw : w = ⟨p.getVert 0, hwSupport⟩ := by
          apply Subtype.ext
          exact hi.symm
        subst w
        change (p.toSubgraph.neighborSet (p.getVert 0)).ncard ≤ 2
        rw [show p.getVert 0 = x0 by simp, hp.neighborSet_toSubgraph_startpoint (by simp [p])]
        simp
      · have hw : w = ⟨p.getVert 1, hwSupport⟩ := by
          apply Subtype.ext
          exact hi.symm
        subst w
        change (p.toSubgraph.neighborSet (p.getVert 1)).ncard ≤ 2
        rw [hp.neighborSet_toSubgraph_internal (by omega) (by simp [p])]
        simp
      · have hw : w = ⟨p.getVert 2, hwSupport⟩ := by
          apply Subtype.ext
          exact hi.symm
        subst w
        change (p.toSubgraph.neighborSet (p.getVert 2)).ncard ≤ 2
        rw [hp.neighborSet_toSubgraph_internal (by omega) (by simp [p])]
        simp
      · have hw : w = ⟨p.getVert 3, hwSupport⟩ := by
          apply Subtype.ext
          exact hi.symm
        subst w
        change (p.toSubgraph.neighborSet (p.getVert 3)).ncard ≤ 2
        rw [hp.neighborSet_toSubgraph_internal (by omega) (by simp [p])]
        simp
      · have hw : w = ⟨p.getVert 4, hwSupport⟩ := by
          apply Subtype.ext
          exact hi.symm
        subst w
        change (p.toSubgraph.neighborSet (p.getVert 4)).ncard ≤ 2
        have hend : p.getVert 4 = x4 := by simp [p]
        rw [hend, hp.neighborSet_toSubgraph_endpoint (by simp [p])]
        simp
    exact hdegree.trans_le (by simpa [w] using hwdeg)
  unfold largestInducedPathSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨T, rfl, -, -⟩
      exact T.card_le_univ⟩
  · exact ⟨S, hScard, htree, hdeg⟩

lemma no_FormsInducedP5_of_largestInducedPathSize_le_four
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hPath : largestInducedPathSize G ≤ 4) :
    ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4 := by
  intro x0 x1 x2 x3 x4 hP5
  have hfive := largestInducedPathSize_ge_five_of_FormsInducedP5 G hP5
  omega

end WrittenOnTheWallII.GraphConjecture314
