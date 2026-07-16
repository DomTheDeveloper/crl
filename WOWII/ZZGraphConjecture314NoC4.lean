import WOWII.ZZGraphConjecture314MinimalTDSStructure

/-!
A minimal total dominating set in a triangle-free induced-P5-free graph cannot
induce a four-cycle. Opposite selected vertices force adjacent private
neighbors. P5-freeness then forces a perfect matching between the two private
pairs, and either matching produces an induced P5.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma no_inducedC4_inside_minimalTDS
    (G : SimpleGraph α)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S)
    {a b c d : α}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (had_ne : a ≠ d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a)
    (hnac : ¬G.Adj a c) (hnbd : ¬G.Adj b d) :
    False := by
  obtain ⟨x, hxa, hxpriv⟩ := exists_private_neighbor_of_mem_minimalTDS G hS haS
  obtain ⟨y, hyb, hypriv⟩ := exists_private_neighbor_of_mem_minimalTDS G hS hbS
  obtain ⟨z, hzc, hzpriv⟩ := exists_private_neighbor_of_mem_minimalTDS G hS hcS
  obtain ⟨w, hwd, hwpriv⟩ := exists_private_neighbor_of_mem_minimalTDS G hS hdS

  have hx_b : ¬G.Adj x b := fun h => hab_ne (hxpriv b hbS h).symm
  have hx_c : ¬G.Adj x c := fun h => hac_ne (hxpriv c hcS h).symm
  have hx_d : ¬G.Adj x d := fun h => had_ne (hxpriv d hdS h).symm
  have hy_a : ¬G.Adj y a := fun h => hab_ne (hypriv a haS h)
  have hy_c : ¬G.Adj y c := fun h => hbc_ne (hypriv c hcS h).symm
  have hy_d : ¬G.Adj y d := fun h => hbd_ne (hypriv d hdS h).symm
  have hz_a : ¬G.Adj z a := fun h => hac_ne (hzpriv a haS h)
  have hz_b : ¬G.Adj z b := fun h => hbc_ne (hzpriv b hbS h)
  have hz_d : ¬G.Adj z d := fun h => hcd_ne (hzpriv d hdS h).symm
  have hw_a : ¬G.Adj w a := fun h => had_ne (hwpriv a haS h)
  have hw_b : ¬G.Adj w b := fun h => hbd_ne (hwpriv b hbS h)
  have hw_c : ¬G.Adj w c := fun h => hcd_ne (hwpriv c hcS h)

  have hx_ne_b : x ≠ b := by intro h; subst x; exact hx_c hbc
  have hx_ne_c : x ≠ c := by intro h; subst x; exact hnac hxa.symm
  have hx_ne_d : x ≠ d := by intro h; subst x; exact hx_c hcd.symm
  have hy_ne_a : y ≠ a := by intro h; subst y; exact hy_d hda.symm
  have hy_ne_c : y ≠ c := by intro h; subst y; exact hy_d hcd
  have hy_ne_d : y ≠ d := by intro h; subst y; exact hy_a hda
  have hz_ne_a : z ≠ a := by intro h; subst z; exact hz_b hab
  have hz_ne_b : z ≠ b := by intro h; subst z; exact hz_a hab.symm
  have hz_ne_d : z ≠ d := by intro h; subst z; exact hz_a hda
  have hw_ne_a : w ≠ a := by intro h; subst w; exact hw_b hab
  have hw_ne_b : w ≠ b := by intro h; subst w; exact hw_c hbc
  have hw_ne_c : w ≠ c := by intro h; subst w; exact hw_b hbc.symm
  have hx_ne_y : x ≠ y := by
    intro h
    subst y
    exact hab_ne (hxpriv b hbS hyb).symm
  have hx_ne_w : x ≠ w := by
    intro h
    subst w
    exact had_ne (hxpriv d hdS hwd).symm
  have hy_ne_z : y ≠ z := by
    intro h
    subst z
    exact hbc_ne (hypriv c hcS hzc).symm
  have hz_ne_w : z ≠ w := by
    intro h
    subst w
    exact hcd_ne (hzpriv d hdS hwd).symm

  have hxz : G.Adj x z := private_neighbors_adj_of_common_center
    G hTriFree hNoP5 haS hcS hac_ne hab hbc hxa hxpriv hzc hzpriv
  have hyw : G.Adj y w := private_neighbors_adj_of_common_center
    G hTriFree hNoP5 hbS hdS hbd_ne hab.symm hda.symm hyb hypriv hwd hwpriv

  have hyx_or_hyz : G.Adj y x ∨ G.Adj y z := by
    by_contra h
    push_neg at h
    apply hNoP5 y b a x z
    unfold FormsInducedP5
    exact ⟨hyb.ne, hy_ne_a, hx_ne_y.symm, hy_ne_z,
      hab_ne.symm, hx_ne_b.symm, hz_ne_b.symm,
      hxa.ne.symm, hz_ne_a.symm, hxz.ne,
      hyb, hab.symm, hxa.symm, hxz,
      hy_a, h.1, h.2,
      fun hbx => hx_b hbx.symm,
      fun hbz => hz_b hbz.symm,
      fun haz => hz_a haz.symm⟩

  have hwx_or_hwz : G.Adj w x ∨ G.Adj w z := by
    by_contra h
    push_neg at h
    apply hNoP5 w d a x z
    unfold FormsInducedP5
    exact ⟨hwd.ne, hw_ne_a, hx_ne_w.symm, hz_ne_w.symm,
      had_ne.symm, hx_ne_d.symm, hz_ne_d.symm,
      hxa.ne.symm, hz_ne_a.symm, hxz.ne,
      hwd, hda, hxa.symm, hxz,
      hw_a, h.1, h.2,
      fun hdx => hx_d hdx.symm,
      fun hdz => hz_d hdz.symm,
      fun haz => hz_a haz.symm⟩

  rcases hyx_or_hyz with hyx | hyz <;> rcases hwx_or_hwz with hwx | hwz
  · exact hTriFree y w x hyw hwx hyx.symm
  · apply hNoP5 a b c z w
    unfold FormsInducedP5
    exact ⟨hab_ne, hac_ne, hz_ne_a.symm, hw_ne_a.symm,
      hbc_ne, hz_ne_b.symm, hw_ne_b.symm,
      hzc.ne.symm, hw_ne_c.symm, hz_ne_w,
      hab, hbc, hzc.symm, hwz.symm,
      hnac,
      fun haz => hz_a haz.symm,
      fun haw => hw_a haw.symm,
      fun hbz => hz_b hbz.symm,
      fun hbw => hw_b hbw.symm,
      fun hcw => hw_c hcw.symm⟩
  · apply hNoP5 b c d w x
    unfold FormsInducedP5
    exact ⟨hbc_ne, hbd_ne, hw_ne_b.symm, hx_ne_b.symm,
      hcd_ne, hw_ne_c.symm, hx_ne_c.symm,
      hwd.ne.symm, hx_ne_d.symm, hx_ne_w.symm,
      hbc, hcd, hwd.symm, hwx,
      hnbd,
      fun hbw => hw_b hbw.symm,
      fun hbx => hx_b hbx.symm,
      fun hcw => hw_c hcw.symm,
      fun hcx => hx_c hcx.symm,
      fun hdx => hx_d hdx.symm⟩
  · exact hTriFree y w z hyw hwz hyz.symm

end WrittenOnTheWallII.GraphConjecture314
