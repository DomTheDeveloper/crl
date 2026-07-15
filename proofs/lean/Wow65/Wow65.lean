import FormalConjectures.WrittenOnTheWallII.GraphConjecture65

/-!
# Written on the Wall II, Conjecture 65

A formal proof that the distance terms in Conjecture 65 are each at most one,
so the claimed bound follows from the existence of a two-vertex induced forest.
-/

namespace WrittenOnTheWallII.GraphConjecture65

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

private lemma walk_exists_crossing
    {G : SimpleGraph α} {S : Set α} {u v : α} (p : G.Walk u v)
    (hu : u ∉ S) (hv : v ∈ S) :
    ∃ x y, x ∉ S ∧ y ∈ S ∧ G.Adj x y := by
  induction p with
  | nil => exact (hu hv).elim
  | @cons u w v huw p ih =>
      by_cases hw : w ∈ S
      · exact ⟨u, w, hu, hw, huw⟩
      · exact ih hw hv

private lemma distToSet_le_one_of_adj
    {G : SimpleGraph α} {S : Set α} {x y : α}
    (hy : y ∈ S) (hxy : G.Adj x y) :
    distToSet G x S ≤ 1 := by
  unfold distToSet
  split_ifs with hS
  · apply Finset.min'_le
    refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
    · simpa using hy
    · simpa using (dist_eq_one_iff_adj.mpr hxy)
  · exact (hS ⟨y, by simpa using hy⟩).elim

private lemma distMin_le_one_of_nonempty
    {G : SimpleGraph α} (hG : G.Connected) {S : Set α} (hS : S.Nonempty) :
    distMin G S ≤ 1 := by
  classical
  unfold distMin
  dsimp only
  split_ifs with hout
  · obtain ⟨u, huout⟩ := hout
    have hu : u ∉ S := (Finset.mem_filter.mp huout).2
    obtain ⟨s, hs⟩ := hS
    obtain ⟨p⟩ := hG u s
    obtain ⟨x, y, hx, hy, hxy⟩ := walk_exists_crossing p hu hs
    have hxmem : distToSet G x S ∈
        Finset.image (fun v => distToSet G v S) (Finset.univ.filter (fun v => v ∉ S)) :=
      Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩
    have hmin :
        (Finset.image (fun v => distToSet G v S)
          (Finset.univ.filter (fun v => v ∉ S))).min' ⟨distToSet G x S, hxmem⟩ ≤
            distToSet G x S :=
      Finset.min'_le
        (Finset.image (fun v => distToSet G v S)
          (Finset.univ.filter (fun v => v ∉ S)))
        (distToSet G x S) hxmem
    exact hmin.trans (distToSet_le_one_of_adj hy hxy)
  · exact Nat.zero_le 1

private lemma two_le_largestInducedForestSize
    {G : SimpleGraph α} [Nontrivial α] :
    2 ≤ G.largestInducedForestSize := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne α
  let s : Finset α := {u, v}
  have hs : s.card = 2 := by simp [s, huv]
  have hac : (G.induce s).IsAcyclic := by
    intro w p hp
    have hlen : 3 ≤ p.length := hp.three_le_length
    let f : Fin 3 → s := fun i => p.getVert (i.val + 1)
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      have hij' : i.val + 1 = j.val + 1 := hp.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        hij
      omega
    have hcard : Fintype.card (Fin 3) ≤ Fintype.card s :=
      Fintype.card_le_of_injective f hf
    have hscard : Fintype.card s = s.card := by
      simpa using (Set.toFinset_card (s : Set α)).symm
    rw [Fintype.card_fin, hscard, hs] at hcard
    omega
  unfold largestInducedForestSize
  have hbdd : BddAbove {n : ℕ | ∃ t : Finset α, (G.induce t).IsAcyclic ∧ t.card = n} := by
    refine ⟨Fintype.card α, ?_⟩
    intro n hn
    obtain ⟨t, _, rfl⟩ := hn
    exact Finset.card_le_univ t
  apply le_csSup hbdd
  exact ⟨s, hac, hs⟩

/-- A proof of Written on the Wall II, Conjecture 65.

The key observation is that `distMin G S ≤ 1` for every nonempty vertex set `S`
in a connected graph. The minimum- and maximum-degree vertex sets are nonempty,
so the left side is at most two, while every nontrivial finite graph has an
induced forest on two vertices. -/
theorem conjecture65_proved
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let A : Set α := {v | G.degree v = G.minDegree}
    let M : Set α := {v | G.degree v = G.maxDegree}
    (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤
      (G.largestInducedForestSize : ℝ) := by
  dsimp
  let A : Set α := {v | G.degree v = G.minDegree}
  let M : Set α := {v | G.degree v = G.maxDegree}
  obtain ⟨a, ha⟩ := G.exists_minimal_degree_vertex
  obtain ⟨m, hm⟩ := G.exists_maximal_degree_vertex
  have hAne : A.Nonempty := ⟨a, ha.symm⟩
  have hMne : M.Nonempty := ⟨m, hm.symm⟩
  have hA : distMin G A ≤ 1 := distMin_le_one_of_nonempty h hAne
  have hM : distMin G M ≤ 1 := distMin_le_one_of_nonempty h hMne
  have hforest : 2 ≤ G.largestInducedForestSize := two_le_largestInducedForestSize
  interval_cases hda : distMin G A <;>
    interval_cases hdm : distMin G M <;>
    norm_num [hda, hdm] at * <;>
    omega

/-- Exact replacement for the open theorem in Formal Conjectures. -/
theorem conjecture65_exact
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let A : Set α := {v | G.degree v = G.minDegree}
    let M : Set α := {v | G.degree v = G.maxDegree}
    (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤
      (G.largestInducedForestSize : ℝ) :=
  conjecture65_proved G h

end WrittenOnTheWallII.GraphConjecture65

#print axioms WrittenOnTheWallII.GraphConjecture65.conjecture65_exact
