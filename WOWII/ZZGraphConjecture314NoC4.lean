import WOWII.ZZGraphConjecture314MinimalTDSStructure

/-!
A minimal total dominating set in a triangle-free induced-P5-free graph cannot
induce a four-cycle.  Opposite selected vertices force adjacent private
neighbors.  P5-freeness then forces a perfect matching between the two private
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

  have hxz : G.Adj x z := private_neighbors_adj_of_common_center
    G hTriFree hNoP5 haS hcS hac_ne hab hbc hxa hxpriv hzc hzpriv
  have hyw : G.Adj y w := private_neighbors_adj_of_common_center
    G hTriFree hNoP5 hbS hdS hbd_ne hab.symm hda.symm hyb hypriv hwd hwpriv

  have hn_y_a : ¬G.Adj y a := by
    intro hya
    exact hab_ne (hypriv a haS hya)
  have hn_y_x_of : ¬G.Adj y x → True := fun _ => trivial
  have hn_b_x : ¬G.Adj b x := by
    intro hbx
    exact hab_ne (hxpriv b hbS hbx.symm).symm
  have hn_b_z : ¬G.Adj b z := by
    intro hbz
    exact hbc_ne (hzpriv b hbS hbz.symm)
  have hn_a_z : ¬G.Adj a z := by
    intro haz
    exact hac_ne (hzpriv a haS haz.symm)

  have hy_ne_a : y ≠ a := by
    intro h
    subst y
    exact hbd_ne (hypriv d hdS hda.symm)
  have hy_ne_x : y ≠ x := by
    intro h
    subst y
    exact hab_ne (hxpriv b hbS hyb)
  have hy_ne_z : y ≠ z := by
    intro h
    subst z
    exact hbc_ne (hypriv c hcS hzc)
  have hb_ne_x : b ≠ x := by
    intro h
    subst x
    exact hbc_ne (hxpriv c hcS hbc)
  have hb_ne_z : b ≠ z := by
    intro h
    subst z
    exact hab_ne (hzpriv a haS hab.symm).symm
  have ha_ne_x : a ≠ x := hxa.ne.symm
  have ha_ne_z : a ≠ z := by
    intro h
    subst z
    exact hcd_ne (hzpriv d hdS hda)

  have hyx_or_hyz : G.Adj y x ∨ G.Adj y z := by
    by_contra h
    push_neg at h
    apply hNoP5 y b a x z
    unfold FormsInducedP5
    exact ⟨hyb.ne, hy_ne_a, hy_ne_x, hy_ne_z,
      hab_ne.symm, hb_ne_x, hb_ne_z,
      ha_ne_x, ha_ne_z, hxz.ne,
      hyb, hab.symm, hxa.symm, hxz,
      hn_y_a, h.1, h.2, hn_b_x, hn_b_z, hn_a_z⟩

  have hn_w_a : ¬G.Adj w a := by
    intro hwa
    exact had_ne (hwpriv a haS hwa)
  have hn_d_x : ¬G.Adj d x := by
    intro hdx
    exact had_ne (hxpriv d hdS hdx.symm).symm
  have hn_d_z : ¬G.Adj d z := by
    intro hdz
    exact hcd_ne (hzpriv d hdS hdz.symm).symm
  have hw_ne_a : w ≠ a := by
    intro h
    subst w
    exact hab_ne (hwpriv b hbS hab)
  have hw_ne_x : w ≠ x := by
    intro h
    subst w
    exact had_ne (hxpriv d hdS hwd)
  have hw_ne_z : w ≠ z := by
    intro h
    subst w
    exact hcd_ne (hzpriv d hdS hwd)
  have hd_ne_x : d ≠ x := by
    intro h
    subst x
    exact hac_ne (hxpriv c hcS hcd.symm)
  have hd_ne_z : d ≠ z := by
    intro h
    subst z
    exact had_ne (hzpriv a haS hda).symm

  have hwx_or_hwz : G.Adj w x ∨ G.Adj w z := by
    by_contra h
    push_neg at h
    apply hNoP5 w d a x z
    unfold FormsInducedP5
    exact ⟨hwd.ne, hw_ne_a, hw_ne_x, hw_ne_z,
      had_ne, hd_ne_x, hd_ne_z,
      ha_ne_x, ha_ne_z, hxz.ne,
      hwd, hda, hxa.symm, hxz,
      hn_w_a, h.1, h.2, hn_d_x, hn_d_z, hn_a_z⟩

  rcases hyx_or_hyz with hyx | hyz <;> rcases hwx_or_hwz with hwx | hwz
  · exact hTriFree y w x hyw hwx hyx.symm
  · have hn_a_z' : ¬G.Adj a z := hn_a_z
    have hn_a_w : ¬G.Adj a w := by
      intro haw
      exact had_ne (hwpriv a haS haw.symm)
    have hn_b_z' : ¬G.Adj b z := hn_b_z
    have hn_b_w : ¬G.Adj b w := by
      intro hbw
      exact hbd_ne (hwpriv b hbS hbw.symm)
    have hn_c_w : ¬G.Adj c w := by
      intro hcw
      exact hcd_ne (hwpriv c hcS hcw.symm).symm
    apply hNoP5 a b c z w
    unfold FormsInducedP5
    exact ⟨hab_ne, hac_ne, ha_ne_z, by
        intro h; subst w; exact had_ne hwd.ne.symm,
      hbc_ne, hb_ne_z, by
        intro h; subst w; exact hbd_ne hwd.ne.symm,
      hzc.ne.symm, hw_ne_z.symm, hwz.ne,
      hab, hbc, hzc.symm, hwz.symm,
      hnac, hn_a_z', hn_a_w, hn_b_z', hn_b_w, hn_c_w⟩
  · have hn_b_w : ¬G.Adj b w := by
      intro hbw
      exact hbd_ne (hwpriv b hbS hbw.symm)
    have hn_b_x' : ¬G.Adj b x := hn_b_x
    have hn_c_w : ¬G.Adj c w := by
      intro hcw
      exact hcd_ne (hwpriv c hcS hcw.symm).symm
    have hn_c_x : ¬G.Adj c x := by
      intro hcx
      exact hac_ne (hxpriv c hcS hcx.symm).symm
    have hn_d_x' : ¬G.Adj d x := hn_d_x
    apply hNoP5 b c d w x
    unfold FormsInducedP5
    exact ⟨hbc_ne, hbd_ne, by
        intro h; subst w; exact hbd_ne hwd.ne.symm,
      hb_ne_x, hcd_ne, by
        intro h; subst w; exact hcd_ne hwd.ne.symm,
      by
        intro h; subst x; exact hbd_ne (hxpriv b hbS hda.symm),
      hwd.ne.symm, hd_ne_x, hwx.ne,
      hbc, hcd, hwd.symm, hwx,
      hnbd, hn_b_w, hn_b_x', hn_c_w, hn_c_x, hn_d_x'⟩
  · exact hTriFree y w z hyw hwz hyz.symm

end WrittenOnTheWallII.GraphConjecture314
