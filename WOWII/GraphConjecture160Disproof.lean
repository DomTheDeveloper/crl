import FormalConjectures.WrittenOnTheWallII.GraphConjecture160

/-!
A five-vertex counterexample to Written on the Wall II Graph Conjecture 160.
All finite checks use kernel-reduced `decide`; no native-code evaluator is trusted.
-/

namespace WrittenOnTheWallII.GraphConjecture160

open Classical SimpleGraph

/-- The finite edge set of the counterexample. Keeping it as a `Finset` supplies
an executable adjacency decision procedure for the concrete graph. -/
def counterexample160Edges : Finset (Sym2 (Fin 5)) :=
  {s(0,2), s(0,3), s(0,4), s(1,2), s(1,3), s(1,4), s(2,4)}

/-- `K_{2,3}` with one additional edge inside the three-vertex part. -/
def counterexample160 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet counterexample160Edges

instance counterexample160DecidableAdj : DecidableRel counterexample160.Adj := by
  intro u v
  change Decidable (s(u, v) ∈ counterexample160Edges ∧ u ≠ v)
  infer_instance

/-- Kernel-checked finite verification that the counterexample graph is connected. -/
lemma counterexample160_connected : counterexample160.Connected := by
  decide

/-- Kernel-checked finite verification of the maximum local independence number. -/
lemma counterexample160_max_local_independence :
    (Finset.univ.image (indepNeighborsCard counterexample160)).max' (by simp) = 2 := by
  unfold indepNeighborsCard
  simp_rw [indep_num_eq_computable]
  unfold computable_indep_num
  decide

/-- Kernel-checked finite verification of the maximum triangle incidence. -/
lemma counterexample160_max_triangles :
    maxTrianglesAtVertex counterexample160 = 2 := by
  unfold maxTrianglesAtVertex numTrianglesAtVertex
  decide

/-- Kernel-checked finite verification of the induced four-cycle count. -/
lemma counterexample160_induced_C4_count :
    countInducedC4 counterexample160 = 2 := by
  unfold countInducedC4 isInducedC4
  decide

/-- The maximum number of leaves of a spanning tree never exceeds the number of vertices. -/
lemma Ls_le_card {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    Ls G ≤ Fintype.card α := by
  unfold Ls
  dsimp only
  apply csSup_le
  · obtain ⟨T, hTG, hTtree⟩ := hG.exists_isTree_le
    let H : G.Subgraph := G.toSubgraph T hTG
    have hspan : H.IsSpanning := by
      simpa [H] using SimpleGraph.toSubgraph.isSpanning T hTG
    have htree : H.coe.IsTree := by
      have hspanning : H.spanningCoe.IsTree := by
        simpa [H, SimpleGraph.toSubgraph, Subgraph.spanningCoe] using hTtree
      exact (H.spanningCoeEquivCoeOfSpanning hspan).isTree_iff.mp hspanning
    exact Set.image_nonempty.mpr ⟨H, ⟨hspan, htree⟩⟩
  · rintro y ⟨H, hH, rfl⟩
    have hcard :
        (H.verts.toFinset.filter (fun v => H.degree v = 1)).card ≤ Fintype.card α := by
      calc
        (H.verts.toFinset.filter (fun v => H.degree v = 1)).card
            ≤ H.verts.toFinset.card := Finset.card_filter_le _ _
        _ = Fintype.card α := hH.1.card_verts
    change (((H.verts.toFinset.filter (fun v => H.degree v = 1)).card : ℕ) : ℝ) ≤
      (Fintype.card α : ℝ)
    exact_mod_cast hcard

lemma counterexample160_Ls_le_five : Ls counterexample160 ≤ 5 := by
  simpa using Ls_le_card counterexample160 counterexample160_connected

/-- The five-vertex graph violates WOWII Conjecture 160: its proposed lower bound is 6,
while every spanning tree has at most five leaves. -/
theorem counterexample160_refutes_statement :
    ¬ (let maxL :=
          (Finset.univ.image (fun v => indepNeighborsCard counterexample160 v)).max' (by simp)
       let maxT := maxTrianglesAtVertex counterexample160
       let cC4 := countInducedC4 counterexample160
       (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls counterexample160) := by
  simp only [counterexample160_max_local_independence,
    counterexample160_max_triangles, counterexample160_induced_C4_count]
  apply not_le_of_gt
  exact lt_of_le_of_lt counterexample160_Ls_le_five (by norm_num)

/-- Repository-style resolution: the universally quantified conjecture is false. -/
theorem conjecture160_false :
    answer(False) ↔
      ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
        (G : SimpleGraph α) [DecidableRel G.Adj] (_ : G.Connected),
        let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
        let maxT := maxTrianglesAtVertex G
        let cC4 := countInducedC4 G
        (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls G := by
  constructor
  · intro h
    exact h.elim
  · intro h
    exact counterexample160_refutes_statement
      (h (Fin 5) counterexample160 counterexample160_connected)

end WrittenOnTheWallII.GraphConjecture160
