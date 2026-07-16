import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
The cycle-and-cardinality core of the sigma-one branch of WOWII 143.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

private lemma two_le_degree_of_mem_cycle_attach {G : SimpleGraph α} [DecidableRel G.Adj]
    {u x : α} {c : G.Walk u u} (hc : c.IsCycle) (hx : x ∈ c.support) :
    2 ≤ G.degree x := by
  have hroot : 2 ≤ G.degree x := by
    let r := c.rotate hx
    have hr : r.IsCycle := hc.rotate hx
    have hs : r.snd ∈ G.neighborFinset x := by
      simpa using r.adj_snd hr.not_nil
    have hp : r.penultimate ∈ G.neighborFinset x := by
      simpa using (r.adj_penultimate hr.not_nil).symm
    have hne : r.snd ≠ r.penultimate := hr.snd_ne_penultimate
    have hsub : ({r.snd, r.penultimate} : Finset α) ⊆ G.neighborFinset x := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hs
      · exact hp
    calc
      2 = ({r.snd, r.penultimate} : Finset α).card := by simp [hne]
      _ ≤ (G.neighborFinset x).card := Finset.card_le_card hsub
      _ = G.degree x := rfl
  exact hroot

/-- If an induced tree contains two distinct degree-one vertices and an outside
vertex has two distinct neighbors in the tree, then the tree has at least
`girth G + 1` vertices. -/
lemma girth_add_one_le_card_of_tree_with_two_leaves_and_external_chord
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} {x y z a b : α}
    (hT : (G.induce (S : Set α)).IsTree)
    (hxS : x ∈ S) (hyS : y ∈ S) (hxy : x ≠ y)
    (hdx : G.degree x = 1) (hdy : G.degree y = 1)
    (hzS : z ∉ S) (haS : a ∈ S) (hbS : b ∈ S)
    (hab : a ≠ b) (hza : G.Adj z a) (hzb : G.Adj z b) :
    G.girth + 1 ≤ S.card := by
  let H := G.induce (S : Set α)
  let aH : (S : Set α) := ⟨a, by simpa using haS⟩
  let bH : (S : Set α) := ⟨b, by simpa using hbS⟩
  obtain ⟨q, hq⟩ := hT.1.exists_isPath aH bH
  let incl : H →g G := ⟨Subtype.val, fun h => h⟩
  let p : G.Walk a b := q.map incl
  have hp : p.IsPath := by
    simpa [p, incl, aH, bH] using
      (Walk.map_isPath_of_injective Subtype.val_injective hq)
  have hzp : z ∉ p.support := by
    intro hz
    have hz' : z ∈ q.support.map incl := by
      simpa [p] using hz
    rw [List.mem_map] at hz'
    obtain ⟨w, hw, hwz⟩ := hz'
    have hzw : z = (w : α) := by simpa [incl] using hwz.symm
    exact hzS (hzw ▸ w.property)
  let r : G.Walk a z := p.concat hzb.symm
  have hr : r.IsPath := by
    exact hp.concat hzp hzb.symm
  have hpen : r.penultimate = b := by
    change r.getVert (r.length - 1) = b
    dsimp [r]
    rw [Walk.length_concat]
    have hidx : p.length + 1 - 1 = p.length := by omega
    rw [hidx, Walk.concat_eq_append, Walk.getVert_append]
    simp
  have hclose : s(z, a) ∉ r.edges := by
    intro he
    have haPen : a = r.penultimate := hr.eq_penultimate_of_mem_edges he
    rw [hpen] at haPen
    exact hab haPen
  let c : G.Walk z z := Walk.cons hza r
  have hc : c.IsCycle := by
    exact (Walk.cons_isCycle_iff r hza).2 ⟨hr, hclose⟩
  have hclen : c.length = p.length + 2 := by
    simp [c, r]
  have hpSub : p.support ⊆ c.support := by
    intro w hw
    simp [c, r, hw]
  have hxNot : x ∉ p.support := by
    intro hx
    have hxc : x ∈ c.support := hpSub hx
    have hdeg := two_le_degree_of_mem_cycle_attach hc hxc
    omega
  have hyNot : y ∉ p.support := by
    intro hy
    have hyc : y ∈ c.support := hpSub hy
    have hdeg := two_le_degree_of_mem_cycle_attach hc hyc
    omega
  let Q : Finset α := p.support.toFinset
  have hQsub : Q ⊆ S := by
    intro w hw
    have hwp : w ∈ p.support := by simpa [Q] using hw
    have hwm : w ∈ q.support.map incl := by simpa [p] using hwp
    rw [List.mem_map] at hwm
    obtain ⟨t, ht, htw⟩ := hwm
    have : w = (t : α) := by simpa [incl] using htw.symm
    exact this ▸ t.property
  have hxQ : x ∉ Q := by simpa [Q] using hxNot
  have hyQ : y ∉ Q := by simpa [Q] using hyNot
  have hQcard : Q.card = p.length + 1 := by
    simp [Q, List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  let U : Finset α := insert x (insert y Q)
  have hUsub : U ⊆ S := by
    intro w hw
    simp only [U, Finset.mem_insert] at hw
    rcases hw with rfl | rfl | hw
    · exact hxS
    · exact hyS
    · exact hQsub hw
  have hUcard : U.card = p.length + 3 := by
    have hxIns : x ∉ insert y Q := by simp [hxy, hxQ]
    rw [show U = insert x (insert y Q) by rfl,
      Finset.card_insert_of_notMem hxIns,
      Finset.card_insert_of_notMem hyQ, hQcard]
  have hcard : p.length + 3 ≤ S.card := by
    rw [← hUcard]
    exact Finset.card_le_card hUsub
  have hgirth : G.girth ≤ c.length := G.girth_le_length hc
  rw [hclen] at hgirth
  omega

end WrittenOnTheWallII.GraphConjecture143