import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
Degree-sequence lemmas for the second-smallest-degree-one branch of WOWII 143.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma degree_pos_of_connected [Nontrivial α] {G : SimpleGraph α}
    [DecidableRel G.Adj] (hG : G.Connected) (v : α) : 0 < G.degree v :=
  hG.preconnected.degree_pos_of_nontrivial v

/-- The second-smallest degree of a connected nontrivial finite graph is positive. -/
lemma secondSmallestDegree_pos_of_connected [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    0 < secondSmallestDegree G := by
  let ds := degreeSequence G
  let D : Multiset ℕ := Finset.univ.val.map (fun v => G.degree v)
  have hcoe : (↑ds : Multiset ℕ) = D := by
    simp [ds, D, degreeSequence]
  have hlen : ds.length = Fintype.card α := by
    simp [ds, degreeSequence]
  have hcard : 2 ≤ Fintype.card α := by
    exact Nat.succ_le_iff.mpr Fintype.one_lt_card
  have h1lt : 1 < ds.length := by omega
  have hm : ds[1] ∈ ds := List.getElem_mem (by omega)
  have hm' : ds[1] ∈ D := by
    rw [← hcoe]
    simpa using hm
  obtain ⟨v, -, hv⟩ := Multiset.mem_map.mp hm'
  have hpos : 0 < ds[1] := by
    rw [← hv]
    exact degree_pos_of_connected hG v
  change 0 < ds.getD 1 0
  rw [List.getD_eq_getElem ds 0 h1lt]
  exact hpos

/-- If a connected nontrivial graph has second-smallest degree one, then it has
at least two distinct degree-one vertices. -/
lemma exists_two_degree_one_of_secondSmallestDegree_eq_one [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hσ : secondSmallestDegree G = 1) :
    ∃ x y : α, x ≠ y ∧ G.degree x = 1 ∧ G.degree y = 1 := by
  let ds := degreeSequence G
  let D : Multiset ℕ := Finset.univ.val.map (fun v => G.degree v)
  have hcoe : (↑ds : Multiset ℕ) = D := by
    simp [ds, D, degreeSequence]
  have hlen : ds.length = Fintype.card α := by
    simp [ds, degreeSequence]
  have hcard : 2 ≤ Fintype.card α := by
    exact Nat.succ_le_iff.mpr Fintype.one_lt_card
  have h1lt : 1 < ds.length := by omega
  have hget1 : ds[1] = 1 := by
    rw [← List.getD_eq_getElem ds 0 h1lt]
    simpa [ds, secondSmallestDegree] using hσ
  have hsorted : ds.Pairwise (· ≤ ·) := by
    simp [ds, degreeSequence]
  let i0 : Fin ds.length := ⟨0, by omega⟩
  let i1 : Fin ds.length := ⟨1, h1lt⟩
  have hi01 : i0 < i1 := by simp [i0, i1]
  have hget0le : ds[0] ≤ ds[1] := by
    have h := hsorted.rel_get_of_lt hi01
    simpa [i0, i1] using h
  have hget0pos : 0 < ds[0] := by
    have hm : ds[0] ∈ ds := List.getElem_mem (by omega)
    have hm' : ds[0] ∈ D := by
      rw [← hcoe]
      simpa using hm
    obtain ⟨v, -, hv⟩ := Multiset.mem_map.mp hm'
    rw [← hv]
    exact degree_pos_of_connected hG v
  have hget0 : ds[0] = 1 := by omega
  have hcount_ds : 2 ≤ ds.count 1 := by
    cases hds : ds with
    | nil => simp [hds] at h1lt
    | cons d0 rest =>
        cases hrest : rest with
        | nil => simp [hds, hrest] at h1lt
        | cons d1 tail =>
            have hd0 : d0 = 1 := by simpa [hds] using hget0
            have hd1 : d1 = 1 := by simpa [hds, hrest] using hget1
            subst d0
            subst d1
            simp
  have hcount_orig : 2 ≤ D.count 1 := by
    rw [← hcoe]
    simpa using hcount_ds
  let L : Finset α := Finset.univ.filter (fun v => 1 = G.degree v)
  have hcount_eq : D.count 1 = L.card := by
    change (Finset.univ.val.map (fun v => G.degree v)).count 1 =
      (Finset.univ.filter (fun v => 1 = G.degree v)).card
    rw [Multiset.count_map]
    rfl
  have hLcard : 2 ≤ L.card := by
    rwa [← hcount_eq]
  have hLnonempty : L.Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) hLcard)
  obtain ⟨x, hx⟩ := hLnonempty
  have herase : 0 < (L.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp herase
  have hyL : y ∈ L := Finset.mem_of_mem_erase hy
  have hyx : y ≠ x := Finset.ne_of_mem_erase hy
  refine ⟨x, y, hyx.symm, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hx).2.symm
  · exact (Finset.mem_filter.mp hyL).2.symm

end WrittenOnTheWallII.GraphConjecture143