import A387471CandidateCard

/-!
# Exact membership characterization of the candidate set
-/

open Finset

namespace A387471

lemma OrdinaryIndices_of_mem_ordinarySet {n : ℕ} {t : Triple}
    (h : t ∈ ordinarySet n) :
    OrdinaryIndices (n : ℤ) (t.1 : ℤ) (t.2.1 : ℤ) (t.2.2 : ℤ) := by
  rw [ordinarySet, Finset.mem_insert] at h
  rcases h with rfl | h
  · simp [OrdinaryIndices]
  · rcases Finset.mem_image.mp h with ⟨⟨r, σ⟩, -, rfl⟩
    fin_cases σ <;>
      simp [OrdinaryIndices, ordinaryParamTriple, ordinaryR, permTripleNat] <;> omega

/-- Encode a natural `r` with `1≤r<n` as the ordinary small parameter. -/
def smallOrdinaryFin {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r < n) : Fin (n - 1) :=
  ⟨r - 1, by omega⟩

@[simp] lemma ordinaryR_smallOrdinaryFin {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r < n) :
    ordinaryR (smallOrdinaryFin hr1 hrn, (0 : Fin 6)) = r := by
  simp [ordinaryR, smallOrdinaryFin]
  omega

lemma ordinary_witness {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r < n) (σ : Fin 6) :
    permTripleNat σ r n (2 * n - r) ∈ ordinarySet n := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨(smallOrdinaryFin hr1 hrn, σ), by simp, ?_⟩
  simp [ordinaryParamTriple, ordinaryR, smallOrdinaryFin]
  omega

lemma mem_ordinarySet_of_OrdinaryIndices {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n)
    (h : OrdinaryIndices (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ)) :
    (i, j, k) ∈ ordinarySet n := by
  obtain ⟨hi1, hi2⟩ := index_bounds hi
  obtain ⟨hj1, hj2⟩ := index_bounds hj
  obtain ⟨hk1, hk2⟩ := index_bounds hk
  rcases h with ⟨hin, hjk⟩ | ⟨hjn, hik⟩ | ⟨hkn, hij⟩
  · have hiN : i = n := by exact_mod_cast hin
    subst i
    by_cases hjN : j = n
    · have hkN : k = n := by omega
      subst j; subst k
      simp [ordinarySet]
    · by_cases hjlt : j < n
      · have hw := ordinary_witness hj1 hjlt (2 : Fin 6)
        simpa [permTripleNat] using (show permTripleNat (2 : Fin 6) j n (2 * n - j) ∈ ordinarySet n from hw)
      · have hnkj : k < n := by omega
        have hw := ordinary_witness hk1 hnkj (3 : Fin 6)
        simpa [permTripleNat] using (show permTripleNat (3 : Fin 6) k n (2 * n - k) ∈ ordinarySet n from hw)
  · have hjN : j = n := by exact_mod_cast hjn
    subst j
    by_cases hiN : i = n
    · have hkN : k = n := by omega
      subst i; subst k
      simp [ordinarySet]
    · by_cases hilt : i < n
      · have hw := ordinary_witness hi1 hilt (0 : Fin 6)
        simpa [permTripleNat] using (show permTripleNat (0 : Fin 6) i n (2 * n - i) ∈ ordinarySet n from hw)
      · have hnki : k < n := by omega
        have hw := ordinary_witness hk1 hnki (5 : Fin 6)
        simpa [permTripleNat] using (show permTripleNat (5 : Fin 6) k n (2 * n - k) ∈ ordinarySet n from hw)
  · have hkN : k = n := by exact_mod_cast hkn
    subst k
    by_cases hiN : i = n
    · have hjN : j = n := by omega
      subst i; subst j
      simp [ordinarySet]
    · by_cases hilt : i < n
      · have hw := ordinary_witness hi1 hilt (1 : Fin 6)
        simpa [permTripleNat] using (show permTripleNat (1 : Fin 6) i n (2 * n - i) ∈ ordinarySet n from hw)
      · have hnji : j < n := by omega
        have hw := ordinary_witness hj1 hnji (4 : Fin 6)
        simpa [permTripleNat] using (show permTripleNat (4 : Fin 6) j n (2 * n - j) ∈ ordinarySet n from hw)

lemma ExceptionalIndices_of_mem_exceptionalSet {q : ℕ} {t : Triple}
    (h : t ∈ exceptionalSet q) :
    ExceptionalIndices (5 * (q : ℤ)) (t.1 : ℤ) (t.2.1 : ℤ) (t.2.2 : ℤ) := by
  rcases Finset.mem_image.mp h with ⟨⟨f, σ⟩, -, rfl⟩
  refine ⟨q, by norm_num, ?_⟩
  fin_cases f <;> fin_cases σ <;>
    simp [exceptionalParamTriple, permTripleNat, Perm3]

lemma exceptional_witness_one (q : ℕ) (σ : Fin 6) :
    permTripleNat σ q (7 * q) (8 * q) ∈ exceptionalSet q := by
  apply Finset.mem_image.mpr
  refine ⟨((0 : Fin 2), σ), by simp, ?_⟩
  simp [exceptionalParamTriple]

lemma exceptional_witness_two (q : ℕ) (σ : Fin 6) :
    permTripleNat σ (2 * q) (3 * q) (9 * q) ∈ exceptionalSet q := by
  apply Finset.mem_image.mpr
  refine ⟨((1 : Fin 2), σ), by simp, ?_⟩
  simp [exceptionalParamTriple]

lemma mem_exceptionalSet_of_ExceptionalIndices {q i j k : ℕ}
    (h : ExceptionalIndices (5 * (q : ℤ)) (i : ℤ) (j : ℤ) (k : ℤ)) :
    (i, j, k) ∈ exceptionalSet q := by
  rcases h with ⟨q', hnq, hp | hp⟩
  have hq' : q' = q := by omega
  subst q'
  · rcases hp with h | h | h | h | h | h
    all_goals rcases h with ⟨hi, hj, hk⟩
    · simpa [permTripleNat] using exceptional_witness_one q (0 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_one q (1 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_one q (2 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_one q (3 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_one q (4 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_one q (5 : Fin 6)
  · rcases hp with h | h | h | h | h | h
    all_goals rcases h with ⟨hi, hj, hk⟩
    · simpa [permTripleNat] using exceptional_witness_two q (0 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_two q (1 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_two q (2 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_two q (3 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_two q (4 : Fin 6)
    · simpa [permTripleNat] using exceptional_witness_two q (5 : Fin 6)

#print axioms OrdinaryIndices_of_mem_ordinarySet
#print axioms mem_ordinarySet_of_OrdinaryIndices
#print axioms ExceptionalIndices_of_mem_exceptionalSet
#print axioms mem_exceptionalSet_of_ExceptionalIndices

end A387471
