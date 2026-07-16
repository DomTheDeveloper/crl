import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
Development of a proof of WOWII Graph Conjecture 143.

The proof splits into:
1. acyclic graphs;
2. cyclic graphs with second-smallest degree at least two;
3. the exceptional case where the second-smallest degree is one.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma induce_pair_isTree_of_adj {G : SimpleGraph α} {u v : α} (huv : G.Adj u v) :
    (G.induce ({u, v} : Set α)).IsTree := by
  refine ⟨induce_pair_connected_of_adj huv, ?_⟩
  intro z p hp
  have hnon : ¬p.Nil := hp.not_nil
  have hs := p.adj_snd hnon
  have ht := p.adj_penultimate hnon
  have hsz : z ≠ p.snd := hs.ne
  have htz : p.penultimate ≠ z := ht.ne
  apply hp.snd_ne_penultimate
  apply Subtype.ext
  have hz := z.property
  have hsmem := p.snd.property
  have htmem := p.penultimate.property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz hsmem htmem
  grind

lemma path_toSubgraph_spanningCoe_isAcyclic {G : SimpleGraph α} {u v : α}
    {p : G.Walk u v} (hp : p.IsPath) : p.toSubgraph.spanningCoe.IsAcyclic := by
  induction p with
  | nil =>
      change (⊥ : SimpleGraph α).IsAcyclic
      exact isAcyclic_bot
  | @cons u v w huv p ih =>
      rw [Walk.cons_isPath_iff] at hp
      have ihA := ih hp.1
      have hu_not : u ∉ p.toSubgraph.verts := by
        simpa [Walk.mem_verts_toSubgraph] using hp.2
      have hnreach : ¬p.toSubgraph.spanningCoe.Reachable u v := by
        rintro ⟨q⟩
        have hq : ¬q.Nil := Walk.not_nil_of_ne huv.ne
        have hadj := q.adj_snd hq
        exact hu_not (p.toSubgraph.edge_vert hadj)
      have hadd :=
        (isAcyclic_add_edge_iff_of_not_reachable u v hnreach).2 ihA
      simpa [Walk.toSubgraph, sup_comm] using hadd

lemma path_toSubgraph_isTree {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath) : p.toSubgraph.coe.IsTree := by
  refine ⟨p.toSubgraph_connected.coe, ?_⟩
  let f : p.toSubgraph.coe →g p.toSubgraph.spanningCoe :=
    ⟨Subtype.val, fun h => h⟩
  exact IsAcyclic.comap f Subtype.val_injective
    (path_toSubgraph_spanningCoe_isAcyclic hp)

lemma edge_getVert_succ_mem_edges {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    {i : ℕ} (hi : i < p.length) : s(p.getVert i, p.getVert (i + 1)) ∈ p.edges := by
  have hi' : i < p.darts.length := by simpa [p.length_darts] using hi
  have hd : p.darts[i]'hi' ∈ p.darts := List.getElem_mem _
  have hm : (p.darts[i]'hi').edge ∈ p.edges := by
    change (p.darts[i]'hi').edge ∈ p.darts.map Dart.edge
    exact List.mem_map.mpr ⟨_, hd, rfl⟩
  rw [p.darts_getElem_eq_getVert i hi'] at hm
  exact hm

lemma geodesic_adj_mem_edges {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hgeo : p.length = G.dist u v) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) :
    s(p.getVert i, p.getVert j) ∈ p.edges := by
  have hne : i ≠ j := by
    intro hij
    subst j
    exact hadj.ne rfl
  have forward : ∀ {a b : ℕ}, a < b → b ≤ p.length →
      G.Adj (p.getVert a) (p.getVert b) →
      s(p.getVert a, p.getVert b) ∈ p.edges := by
    intro a b hab hb habadj
    let q := (p.drop a).take (b - a)
    have hqsub : q.IsSubwalk p :=
      (Walk.isSubwalk_take (p.drop a) (b - a)).trans (Walk.isSubwalk_drop p a)
    have hseg := length_eq_dist_of_subwalk hgeo hqsub
    have hmin : b - a ≤ p.length - a := by omega
    have hseg' : b - a = G.dist (p.getVert a) (p.getVert b) := by
      simpa [q, Nat.min_eq_left hmin, Nat.add_sub_of_le hab.le] using hseg
    have hdiff : b - a = 1 := by
      rw [dist_eq_one_iff_adj.mpr habadj] at hseg'
      exact hseg'
    have hba : b = a + 1 := by omega
    subst b
    exact edge_getVert_succ_mem_edges p (by omega)
  by_cases hij : i < j
  · exact forward hij hj hadj
  · have hji : j < i := by omega
    simpa [Sym2.eq_swap] using forward hji hi hadj.symm

lemma geodesic_support_induces_tree {G : SimpleGraph α} {u v : α} {p : G.Walk u v}
    (hgeo : p.length = G.dist u v) :
    (G.induce {x : α | x ∈ p.support}).IsTree := by
  have hverts : {x : α | x ∈ p.support} = p.toSubgraph.verts := by
    ext x
    simp [Walk.mem_verts_toSubgraph]
  rw [hverts]
  have heq : G.induce p.toSubgraph.verts = p.toSubgraph.coe := by
    ext x y
    constructor
    · intro hxy
      change p.toSubgraph.Adj (x : α) (y : α)
      rw [Walk.adj_toSubgraph_iff_mem_edges]
      have hx : (x : α) ∈ p.support := p.mem_verts_toSubgraph.mp x.property
      have hy : (y : α) ∈ p.support := p.mem_verts_toSubgraph.mp y.property
      obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      obtain ⟨j, hjy, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hy
      have hadj : G.Adj (p.getVert i) (p.getVert j) := by
        simpa [hix, hjy] using hxy
      simpa [hix, hjy] using geodesic_adj_mem_edges hgeo hi hj hadj
    · intro hxy
      exact p.toSubgraph.adj_sub hxy
  rw [heq]
  exact path_toSubgraph_isTree (p.isPath_of_length_eq_dist hgeo)

lemma dist_add_one_le_largestInducedTreeSize (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (u v : α) :
    G.dist u v + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hp, hgeo⟩ := hG.exists_path_of_dist u v
  unfold largestInducedTreeSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨s, rfl, _⟩
      exact s.card_le_univ⟩
  · refine ⟨p.support.toFinset, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hgeo]
    · have hset : (↑p.support.toFinset : Set α) = {x : α | x ∈ p.support} := by
        ext x
        simp
      rw [hset]
      exact geodesic_support_induces_tree hgeo

lemma two_le_largestInducedTreeSize (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) [Nontrivial α] :
    2 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne α
  obtain ⟨w, huw⟩ : ∃ w, G.Adj u w := by
    obtain ⟨p⟩ := hG u v
    cases p with
    | nil => exact (huv rfl).elim
    | cons h p => exact ⟨_, h⟩
  unfold largestInducedTreeSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨s, rfl, _⟩
      exact s.card_le_univ⟩
  · refine ⟨{u, w}, by simp [huw.ne], ?_⟩
    have hset : (↑({u, w} : Finset α) : Set α) = ({u, w} : Set α) := by
      ext x
      simp
    rw [hset]
    exact induce_pair_isTree_of_adj huw

lemma conjecture143_of_girth_zero [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hσ : 0 < secondSmallestDegree G) (hg : G.girth = 0) :
    (G.girth : ℝ) + 1 ≤
      (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
  have ht : 0 < largestInducedTreeSize G :=
    lt_of_lt_of_le (by norm_num) (two_le_largestInducedTreeSize G hG)
  have hprod : 0 < largestInducedTreeSize G * secondSmallestDegree G :=
    Nat.mul_pos ht hσ
  have hone : 1 ≤ largestInducedTreeSize G * secondSmallestDegree G := hprod
  rw [hg]
  norm_num
  exact_mod_cast hone

lemma conjecture143_of_large_sigma (G : SimpleGraph α) [DecidableRel G.Adj]
    (hgirth : 3 ≤ G.girth)
    (htree : G.girth - 1 ≤ largestInducedTreeSize G)
    (hσ : 2 ≤ secondSmallestDegree G) :
    (G.girth : ℝ) + 1 ≤
      (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
  have htreeNat : G.girth ≤ largestInducedTreeSize G + 1 := by omega
  have htreeR : (G.girth : ℝ) ≤ (largestInducedTreeSize G : ℝ) + 1 := by
    exact_mod_cast htreeNat
  have hσR : (2 : ℝ) ≤ secondSmallestDegree G := by
    exact_mod_cast hσ
  have hgirthR : (3 : ℝ) ≤ G.girth := by
    exact_mod_cast hgirth
  have htreeNonneg : (0 : ℝ) ≤ largestInducedTreeSize G := by positivity
  have hmul :
      2 * (largestInducedTreeSize G : ℝ) ≤
        (largestInducedTreeSize G : ℝ) * (secondSmallestDegree G : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hσR htreeNonneg]
  nlinarith

/-- Any inhabited property of finite vertex sets has a witness of maximum cardinality. -/
lemma exists_max_card_finset_main (P : Finset α → Prop) [DecidablePred P]
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

/-- A nontrivial connected set has a graph edge crossing to its complement. -/
lemma exists_crossing_edge_main {G : SimpleGraph α} (hG : G.Connected)
    {S : Set α} (hS : S.Nonempty) (hS_ne : S ≠ Set.univ) :
    ∃ u ∈ S, ∃ v ∉ S, G.Adj u v := by
  obtain ⟨u, hu⟩ := hS
  have hex : ∃ v : α, v ∉ S := by
    by_contra h
    push_neg at h
    apply hS_ne
    ext x
    simp [h x]
  obtain ⟨v, hv⟩ := hex
  have aux : ∀ {a b : α} (p : G.Walk a b), a ∈ S → b ∉ S →
      ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
    intro a b p
    induction p with
    | nil =>
        intro ha hb
        exact (hb ha).elim
    | @cons a c b hac p ih =>
        intro ha hb
        by_cases hc : c ∈ S
        · exact ih hc hb
        · exact ⟨a, ha, c, hc, hac⟩
  exact (hG u v).elim fun p => aux p hu hv

/-- Among all induced trees containing two specified vertices, one has maximum cardinality. -/
lemma exists_max_induced_tree_containing (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (x y : α) :
    ∃ S : Finset α,
      x ∈ S ∧ y ∈ S ∧ (G.induce (S : Set α)).IsTree ∧
      ∀ T : Finset α,
        x ∈ T → y ∈ T → (G.induce (T : Set α)).IsTree → T.card ≤ S.card := by
  let P : Finset α → Prop := fun S =>
    x ∈ S ∧ y ∈ S ∧ (G.induce (S : Set α)).IsTree
  have hP : ∃ S : Finset α, P S := by
    obtain ⟨p, hp, hgeo⟩ := hG.exists_path_of_dist x y
    refine ⟨p.support.toFinset, ?_, ?_, ?_⟩
    · simp
    · simp
    · have hset : (↑p.support.toFinset : Set α) = {z : α | z ∈ p.support} := by
        ext z
        simp
      rw [hset]
      exact geodesic_support_induces_tree hgeo
  obtain ⟨S, hSP, hmax⟩ := exists_max_card_finset_main P hP
  refine ⟨S, hSP.1, hSP.2.1, hSP.2.2, ?_⟩
  intro T hxT hyT htreeT
  exact hmax T ⟨hxT, hyT, htreeT⟩

end WrittenOnTheWallII.GraphConjecture143