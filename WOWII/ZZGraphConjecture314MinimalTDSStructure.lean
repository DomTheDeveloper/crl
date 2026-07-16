import WOWII.ZZGraphConjecture314DominatingEdge

/-!
Structural lemmas toward the remaining cardinality bound for WOWII Graph
Conjecture 314.  Minimality supplies an open private neighbor for every selected
vertex.  In a triangle-free induced-P5-free graph, private neighbors of two
selected vertices with a common center must be adjacent; hence no vertex can
have three distinct selected neighbors.  Also, the selected subgraph of a
minimal total dominating set cannot contain an induced P4.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Two private neighbors belonging to distinct selected vertices with a common
center must be adjacent, or they extend the selected P3 to an induced P5. -/
lemma private_neighbors_adj_of_common_center
    (G : SimpleGraph α)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    {S : Finset α} {a b r x y : α}
    (haS : a ∈ S) (hbS : b ∈ S) (hab : a ≠ b)
    (har : G.Adj a r) (hrb : G.Adj r b)
    (hxa : G.Adj x a)
    (hxpriv : ∀ w : α, w ∈ S → G.Adj x w → w = a)
    (hyb : G.Adj y b)
    (hypriv : ∀ w : α, w ∈ S → G.Adj y w → w = b) :
    G.Adj x y := by
  by_contra hnxy
  have hnab : ¬G.Adj a b := by
    intro habAdj
    exact hTriFree a r b har hrb habAdj.symm
  have hxne_a : x ≠ a := hxa.ne
  have hxne_r : x ≠ r := by
    intro hxr
    subst x
    exact hab (hxpriv b hbS hrb)
  have hxne_b : x ≠ b := by
    intro hxb
    subst x
    exact hnab hxa.symm
  have hyne_b : y ≠ b := hyb.ne
  have hyne_r : y ≠ r := by
    intro hyr
    subst y
    exact hab (hypriv a haS har.symm).symm
  have hyne_a : y ≠ a := by
    intro hya
    subst y
    exact hnab hyb
  have hxne_y : x ≠ y := by
    intro hxy
    subst y
    exact hab (hxpriv b hbS hyb)
  have hnxr : ¬G.Adj x r := by
    intro hxr
    exact hTriFree x a r hxa har hxr.symm
  have hnxb : ¬G.Adj x b := by
    intro hxb
    exact hab (hxpriv b hbS hxb)
  have hnay : ¬G.Adj a y := by
    intro hay
    exact hab (hypriv a haS hay.symm).symm
  have hnry : ¬G.Adj r y := by
    intro hry
    exact hTriFree r b y hrb hyb.symm hry.symm
  apply hNoP5 x a r b y
  unfold FormsInducedP5
  exact ⟨hxne_a, hxne_r, hxne_b, hxne_y,
    har.ne, hab, hyne_a.symm,
    hrb.ne, hyne_r.symm, hyne_b.symm,
    hxa, har, hrb, hyb.symm,
    hnxr, hnxb, hnxy, hnab, hnay, hnry⟩

/-- In a triangle-free induced-P5-free graph, a vertex has at most two distinct
neighbors belonging to a fixed minimal total dominating set. -/
lemma no_three_mem_minimalTDS_adj_common_center
    (G : SimpleGraph α)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {r a b c : α}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hra : G.Adj r a) (hrb : G.Adj r b) (hrc : G.Adj r c) :
    False := by
  obtain ⟨x, hxa, hxpriv⟩ := exists_private_neighbor_of_mem_minimalTDS G hS haS
  obtain ⟨y, hyb, hypriv⟩ := exists_private_neighbor_of_mem_minimalTDS G hS hbS
  obtain ⟨z, hzc, hzpriv⟩ := exists_private_neighbor_of_mem_minimalTDS G hS hcS
  have hxy : G.Adj x y := private_neighbors_adj_of_common_center
    G hTriFree hNoP5 haS hbS hab hra.symm hrb hxa hxpriv hyb hypriv
  have hxz : G.Adj x z := private_neighbors_adj_of_common_center
    G hTriFree hNoP5 haS hcS hac hra.symm hrc hxa hxpriv hzc hzpriv
  have hyz : G.Adj y z := private_neighbors_adj_of_common_center
    G hTriFree hNoP5 hbS hcS hbc hrb.symm hrc hyb hypriv hzc hzpriv
  exact hTriFree x y z hxy hyz hxz.symm

/-- The graph induced by a minimal total dominating set contains no induced P4:
a private neighbor of an endpoint would extend it to an induced P5. -/
lemma no_inducedP4_inside_minimalTDS
    (G : SimpleGraph α)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {a b c d : α}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (had_ne : a ≠ d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hnac : ¬G.Adj a c) (hnad : ¬G.Adj a d) (hnbd : ¬G.Adj b d) :
    False := by
  obtain ⟨x, hxa, hxpriv⟩ := exists_private_neighbor_of_mem_minimalTDS G hS haS
  have hxne_a : x ≠ a := hxa.ne
  have hxne_b : x ≠ b := by
    intro hxb
    subst x
    exact hac_ne (hxpriv c hcS hbc)
  have hxne_c : x ≠ c := by
    intro hxc
    subst x
    exact hab_ne (hxpriv b hbS hbc.symm)
  have hxne_d : x ≠ d := by
    intro hxd
    subst x
    exact hac_ne (hxpriv c hcS hcd.symm)
  have hnxb : ¬G.Adj x b := by
    intro hxb
    exact hab_ne (hxpriv b hbS hxb)
  have hnxc : ¬G.Adj x c := by
    intro hxc
    exact hac_ne (hxpriv c hcS hxc)
  have hnxd : ¬G.Adj x d := by
    intro hxd
    exact had_ne (hxpriv d hdS hxd)
  apply hNoP5 x a b c d
  unfold FormsInducedP5
  exact ⟨hxne_a, hxne_b, hxne_c, hxne_d,
    hab_ne, hac_ne, had_ne,
    hbc_ne, hbd_ne, hcd_ne,
    hxa, hab, hbc, hcd,
    hnxb, hnxc, hnxd, hnac, hnad, hnbd⟩

end WrittenOnTheWallII.GraphConjecture314
