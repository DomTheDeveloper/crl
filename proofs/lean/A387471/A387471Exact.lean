import A387471CandidateMembership

/-!
# Exact solution-set equality and the A387471 cardinality theorem
-/

open Finset

namespace A387471

lemma permTriple_mem_allTriples {n a b c : ℕ} (σ : Fin 6)
    (ha : a ∈ indices n) (hb : b ∈ indices n) (hc : c ∈ indices n) :
    permTripleNat σ a b c ∈ allTriples n := by
  fin_cases σ <;> simp [allTriples, permTripleNat, ha, hb, hc]

lemma mem_indices_self {n : ℕ} (hn : 0 < n) : n ∈ indices n := by
  simp [indices]
  omega

lemma ordinaryParam_mem_allTriples {n : ℕ} (hn : 0 < n) (p : OrdinaryParam n) :
    ordinaryParamTriple n p ∈ allTriples n := by
  have hr := ordinaryR_bounds p
  have hrmem : ordinaryR p ∈ indices n := by
    simp [indices]
    omega
  have hnmem := mem_indices_self hn
  have hlmem : 2 * n - ordinaryR p ∈ indices n := by
    simp [indices]
    omega
  exact permTriple_mem_allTriples p.2 hrmem hnmem hlmem

lemma mem_allTriples_of_mem_ordinarySet {n : ℕ} (hn : 0 < n) {t : Triple}
    (h : t ∈ ordinarySet n) : t ∈ allTriples n := by
  rw [ordinarySet, Finset.mem_insert] at h
  rcases h with rfl | h
  · simp [allTriples, mem_indices_self hn]
  · rcases Finset.mem_image.mp h with ⟨p, -, rfl⟩
    exact ordinaryParam_mem_allTriples hn p

lemma exceptionalParam_mem_allTriples {q : ℕ} (hq : 0 < q) (p : ExceptionalParam) :
    exceptionalParamTriple q p ∈ allTriples (5 * q) := by
  rcases p with ⟨f, σ⟩
  have hqmem : q ∈ indices (5 * q) := by simp [indices]; omega
  have h2mem : 2 * q ∈ indices (5 * q) := by simp [indices]; omega
  have h3mem : 3 * q ∈ indices (5 * q) := by simp [indices]; omega
  have h7mem : 7 * q ∈ indices (5 * q) := by simp [indices]; omega
  have h8mem : 8 * q ∈ indices (5 * q) := by simp [indices]; omega
  have h9mem : 9 * q ∈ indices (5 * q) := by simp [indices]; omega
  fin_cases f
  · exact permTriple_mem_allTriples σ hqmem h7mem h8mem
  · exact permTriple_mem_allTriples σ h2mem h3mem h9mem

lemma mem_allTriples_of_mem_exceptionalSet {q : ℕ} (hq : 0 < q) {t : Triple}
    (h : t ∈ exceptionalSet q) : t ∈ allTriples (5 * q) := by
  rcases Finset.mem_image.mp h with ⟨p, -, rfl⟩
  exact exceptionalParam_mem_allTriples hq p

lemma mem_allTriples_of_mem_candidateSet {n : ℕ} (hn : 0 < n) {t : Triple}
    (h : t ∈ candidateSet n) : t ∈ allTriples n := by
  by_cases h5 : 5 ∣ n
  · rw [candidateSet, dif_pos h5, Finset.mem_union] at h
    rcases h with ho | he
    · exact mem_allTriples_of_mem_ordinarySet hn ho
    · have hq : 0 < n / 5 := div_five_pos hn h5
      have he' := mem_allTriples_of_mem_exceptionalSet hq he
      simpa [five_mul_div_five h5] using he'
  · rw [candidateSet, dif_neg h5] at h
    exact mem_allTriples_of_mem_ordinarySet hn h

lemma IndexClassified_of_mem_candidateSet {n : ℕ} {t : Triple}
    (h : t ∈ candidateSet n) :
    IndexClassified (n : ℤ) (t.1 : ℤ) (t.2.1 : ℤ) (t.2.2 : ℤ) := by
  by_cases h5 : 5 ∣ n
  · rw [candidateSet, dif_pos h5, Finset.mem_union] at h
    rcases h with ho | he
    · exact Or.inl (OrdinaryIndices_of_mem_ordinarySet ho)
    · apply Or.inr
      have hex := ExceptionalIndices_of_mem_exceptionalSet he
      have hnq : (n : ℤ) = 5 * ((n / 5 : ℕ) : ℤ) := by
        exact_mod_cast (five_mul_div_five h5).symm
      rwa [← hnq] at hex
  · rw [candidateSet, dif_neg h5] at h
    exact Or.inl (OrdinaryIndices_of_mem_ordinarySet h)

lemma mem_candidateSet_of_IndexClassified {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n)
    (h : IndexClassified (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ)) :
    (i, j, k) ∈ candidateSet n := by
  rcases h with hord | hexc
  · have ho := mem_ordinarySet_of_OrdinaryIndices hn hi hj hk hord
    by_cases h5 : 5 ∣ n
    · rw [candidateSet, dif_pos h5]
      exact Finset.mem_union_left _ ho
    · rwa [candidateSet, dif_neg h5]
  · have h5z : (5 : ℤ) ∣ (n : ℤ) := five_dvd_of_exceptional hexc
    have h5 : 5 ∣ n := by exact_mod_cast h5z
    rw [candidateSet, dif_pos h5]
    apply Finset.mem_union_right
    have hnq : (n : ℤ) = 5 * ((n / 5 : ℕ) : ℤ) := by
      exact_mod_cast (five_mul_div_five h5).symm
    rw [hnq] at hexc
    exact mem_exceptionalSet_of_ExceptionalIndices hexc

/-- The candidate set is exactly the classified predicate inside the index box. -/
theorem mem_candidateSet_iff_indexClassified {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n) :
    (i, j, k) ∈ candidateSet n ↔
      IndexClassified (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ) := by
  constructor
  · exact IndexClassified_of_mem_candidateSet
  · exact mem_candidateSet_of_IndexClassified hn hi hj hk

/-- Exact equality between the original trigonometric solution finset and the
explicit classified candidate finset. -/
theorem solutionTriples_eq_candidateSet (n : ℕ) (hn : 1 ≤ n) :
    solutionTriples n = candidateSet n := by
  classical
  ext t
  have hnpos : 0 < n := hn
  constructor
  · intro h
    rw [solutionTriples] at h
    simp only [Finset.mem_filter] at h
    rcases h with ⟨hall, hcon⟩
    have hbox : t.1 ∈ indices n ∧ t.2.1 ∈ indices n ∧ t.2.2 ∈ indices n := by
      simpa [allTriples] using hall
    exact mem_candidateSet_of_IndexClassified hnpos hbox.1 hbox.2.1 hbox.2.2
      (every_solution_indexClassified n t.1 t.2.1 t.2.2 hnpos
        hbox.1 hbox.2.1 hbox.2.2 hcon)
  · intro h
    have hall := mem_allTriples_of_mem_candidateSet hnpos h
    have hbox : t.1 ∈ indices n ∧ t.2.1 ∈ indices n ∧ t.2.2 ∈ indices n := by
      simpa [allTriples] using hall
    have hclass := IndexClassified_of_mem_candidateSet h
    have hcon := concurrent_of_IndexClassified hnpos hclass
    rw [solutionTriples]
    exact Finset.mem_filter.mpr ⟨hall, hcon⟩

/-- The original exact OEIS A387471 statement. -/
theorem exactStatement_proved : ExactStatement := by
  intro n hn
  rw [solutionTriples_eq_candidateSet n hn, card_candidateSet n hn]

#print axioms solutionTriples_eq_candidateSet
#print axioms exactStatement_proved

end A387471
