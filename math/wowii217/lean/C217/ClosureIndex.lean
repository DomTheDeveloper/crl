import C217.WalkTransfer
import Mathlib.Tactic

open Classical
open SimpleGraph

namespace C217

universe u

namespace SimpleGraph.Walk

variable {V : Type u}
variable {G : SimpleGraph V}
variable {a b u v : V}

lemma IsPath.getVert_injective_on {p : G.Walk a b} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hij : p.getVert i = p.getVert j) : i = j :=
  hp.getVert_injOn hi hj hij

lemma adj_base_of_ne_added_index [DecidableEq V]
    (p : (G ⊔ edge u v).Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi : i < p.length)
    (hui : p.getVert i = u) (hvi : p.getVert (i + 1) = v)
    (hj : j < p.length) (hji : j ≠ i) :
    G.Adj (p.getVert j) (p.getVert (j + 1)) := by
  have hAdj := p.adj_getVert_succ hj
  rw [SimpleGraph.sup_adj] at hAdj
  rcases hAdj with hG | hedge
  · exact hG
  · rw [SimpleGraph.edge_adj] at hedge
    rcases hedge.1 with h | h
    · rcases h with ⟨hx, hy⟩
      have hEq : p.getVert j = p.getVert i := by rw [hx, hui]
      have : j = i := hp.getVert_injective_on hj.le hi.le hEq
      exact (hji this).elim
    · rcases h with ⟨hx, hy⟩
      have hEq₁ : p.getVert j = p.getVert (i + 1) := by rw [hx, hvi]
      have hEq₂ : p.getVert (j + 1) = p.getVert i := by rw [hy, hui]
      have hj₁ : j = i + 1 := hp.getVert_injective_on hj.le (by omega) hEq₁
      have hj₂ : j + 1 = i := hp.getVert_injective_on (by omega) hi.le hEq₂
      omega

section Crossing

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private lemma card_neighbors_before_end
    (p : G.Walk a b) (hp : p.IsHamiltonian)
    (x : V) (hxb : ¬ G.Adj x b) :
    (Finset.univ.filter fun j : Fin p.length => G.Adj x (p.getVert j.val)).card =
      G.degree x := by
  let A : Finset (Fin p.length) :=
    Finset.univ.filter fun j => G.Adj x (p.getVert j.val)
  let f : Fin p.length → V := fun j => p.getVert j.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hp.isPath.getVert_injective_on i.isLt.le j.isLt.le hij
  have himage : A.image f = G.neighborFinset x := by
    ext y
    simp only [A, f, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hxy
      have hyb : y ≠ b := by
        intro hy
        subst y
        exact hxb hxy
      let k : Fin p.support.length := hp.getVertEquiv.symm y
      have hkget : p.getVert k.val = y := hp.getVertEquiv.apply_symm_apply y
      have hkle : k.val ≤ p.length := by
        have hklt := k.isLt
        rw [p.length_support] at hklt
        omega
      have hkne : k.val ≠ p.length := by
        intro hk
        rw [hk, p.getVert_length] at hkget
        exact hyb hkget.symm
      have hklt : k.val < p.length := lt_of_le_of_ne hkle hkne
      let j : Fin p.length := ⟨k.val, hklt⟩
      refine ⟨j, ?_, ?_⟩
      · simpa [j, hkget] using hxy
      · simpa [j] using hkget
  calc
    (Finset.univ.filter fun j : Fin p.length => G.Adj x (p.getVert j.val)).card
        = A.card := rfl
    _ = (A.image f).card := (Finset.card_image_of_injective A hf).symm
    _ = (G.neighborFinset x).card := congrArg Finset.card himage
    _ = G.degree x := G.card_neighborFinset_eq_degree x

private lemma card_neighbors_after_start
    (p : G.Walk a b) (hp : p.IsHamiltonian)
    (x : V) (hxa : ¬ G.Adj x a) :
    (Finset.univ.filter fun j : Fin p.length => G.Adj x (p.getVert (j.val + 1))).card =
      G.degree x := by
  let A : Finset (Fin p.length) :=
    Finset.univ.filter fun j => G.Adj x (p.getVert (j.val + 1))
  let f : Fin p.length → V := fun j => p.getVert (j.val + 1)
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hsucc : i.val + 1 = j.val + 1 :=
      hp.isPath.getVert_injective_on (by omega) (by omega) hij
    omega
  have himage : A.image f = G.neighborFinset x := by
    ext y
    simp only [A, f, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hxy
      have hya : y ≠ a := by
        intro hy
        subst y
        exact hxa hxy
      let k : Fin p.support.length := hp.getVertEquiv.symm y
      have hkget : p.getVert k.val = y := hp.getVertEquiv.apply_symm_apply y
      have hkle : k.val ≤ p.length := by
        have hklt := k.isLt
        rw [p.length_support] at hklt
        omega
      have hkzero : k.val ≠ 0 := by
        intro hk
        rw [hk, p.getVert_zero] at hkget
        exact hya hkget.symm
      have hkpos : 0 < k.val := Nat.pos_of_ne_zero hkzero
      have hpredlt : k.val - 1 < p.length := by omega
      let j : Fin p.length := ⟨k.val - 1, hpredlt⟩
      refine ⟨j, ?_, ?_⟩
      · have hsucc : j.val + 1 = k.val := by simp [j, Nat.sub_add_cancel hkpos]
        simpa [hsucc, hkget] using hxy
      · have hsucc : j.val + 1 = k.val := by simp [j, Nat.sub_add_cancel hkpos]
        simpa [hsucc] using hkget
  calc
    (Finset.univ.filter fun j : Fin p.length => G.Adj x (p.getVert (j.val + 1))).card
        = A.card := rfl
    _ = (A.image f).card := (Finset.card_image_of_injective A hf).symm
    _ = (G.neighborFinset x).card := congrArg Finset.card himage
    _ = G.degree x := G.card_neighborFinset_eq_degree x

/-- The counting core of the Bondy--Chvátal path-closure surgery. If the
added edge occurs at position `i`, neither easy endpoint reconnection is
available, and the degree sum is large enough, then some other position
`t` supplies the two crossing edges used by the path rotation. -/
lemma exists_closure_crossing_index
    (p : (G ⊔ edge u v).Walk a b) (hp : p.IsHamiltonian)
    {i : ℕ} (hi : i < p.length)
    (hui : p.getVert i = u) (hvi : p.getVert (i + 1) = v)
    (hub : ¬ G.Adj u b) (hva : ¬ G.Adj v a)
    (hdeg : p.length ≤ G.degree u + G.degree v) :
    ∃ t < p.length, t ≠ i ∧
      G.Adj u (p.getVert t) ∧ G.Adj v (p.getVert (t + 1)) := by
  let A : Finset (Fin p.length) :=
    Finset.univ.filter fun j => G.Adj u (p.getVert j.val)
  let B : Finset (Fin p.length) :=
    Finset.univ.filter fun j => G.Adj v (p.getVert (j.val + 1))
  let bad : Fin p.length := ⟨i, hi⟩
  have hcardA : A.card = G.degree u := by
    simpa [A] using card_neighbors_before_end p hp u hub
  have hcardB : B.card = G.degree v := by
    simpa [B] using card_neighbors_after_start p hp v hva
  have hbadA : bad ∉ A := by
    simp [A, bad, hui]
  have hbadB : bad ∉ B := by
    simp [B, bad, hvi]
  have hnotdis : ¬ Disjoint A B := by
    intro hdis
    have hsub : A ∪ B ⊆ Finset.univ.erase bad := by
      intro j hj
      have hjne : j ≠ bad := by
        intro hEq
        subst j
        rcases Finset.mem_union.mp hj with hjA | hjB
        · exact hbadA hjA
        · exact hbadB hjB
      exact Finset.mem_erase.mpr ⟨hjne, Finset.mem_univ j⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_erase_of_mem (Finset.mem_univ bad),
      Finset.card_univ, Fintype.card_fin] at hcard
    rw [hcardA, hcardB] at hcard
    omega
  rw [Finset.not_disjoint_iff] at hnotdis
  rcases hnotdis with ⟨j, hjA, hjB⟩
  refine ⟨j.val, j.isLt, ?_, ?_, ?_⟩
  · intro hEq
    apply hbadA
    simpa [bad, hEq] using hjA
  · simpa [A] using hjA
  · simpa [B] using hjB

end Crossing

end SimpleGraph.Walk

end C217
