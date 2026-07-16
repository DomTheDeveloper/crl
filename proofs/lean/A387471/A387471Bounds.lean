import A387471Trig

/-!
# Exact admissible bounds for the reduced A387471 coefficients
-/

namespace A387471

lemma index_bounds {n i : ℕ} (hi : i ∈ indices n) :
    1 ≤ i ∧ i ≤ 2 * n - 1 := by
  simpa [indices] using hi

lemma reducedA_bounds {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n) :
    -3 * (n : ℤ) < reducedA n i j k ∧
      reducedA n i j k < 3 * (n : ℤ) := by
  obtain ⟨hi1, hi2⟩ := index_bounds hi
  obtain ⟨hj1, hj2⟩ := index_bounds hj
  obtain ⟨hk1, hk2⟩ := index_bounds hk
  simp [reducedA]
  omega

lemma reducedB_bounds {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n) :
    -3 * (n : ℤ) < reducedB n i j k ∧
      reducedB n i j k < 3 * (n : ℤ) := by
  obtain ⟨hi1, hi2⟩ := index_bounds hi
  obtain ⟨hj1, hj2⟩ := index_bounds hj
  obtain ⟨hk1, hk2⟩ := index_bounds hk
  simp [reducedB]
  omega

lemma reducedC_bounds {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n) :
    -3 * (n : ℤ) < reducedC n i j k ∧
      reducedC n i j k < 3 * (n : ℤ) := by
  obtain ⟨hi1, hi2⟩ := index_bounds hi
  obtain ⟨hj1, hj2⟩ := index_bounds hj
  obtain ⟨hk1, hk2⟩ := index_bounds hk
  simp [reducedC]
  omega

lemma reducedAB_eq {n i j k : ℕ} :
    reducedA n i j k + reducedB n i j k = 2 * ((i : ℤ) - n) := by
  simp [reducedA, reducedB]
  ring

lemma reducedAC_eq {n i j k : ℕ} :
    reducedA n i j k + reducedC n i j k = 2 * ((j : ℤ) - n) := by
  simp [reducedA, reducedC]
  ring

lemma reducedBC_eq {n i j k : ℕ} :
    reducedB n i j k + reducedC n i j k = 2 * ((k : ℤ) - n) := by
  simp [reducedB, reducedC]
  ring

lemma reducedAB_bounds {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) :
    -2 * (n : ℤ) < reducedA n i j k + reducedB n i j k ∧
      reducedA n i j k + reducedB n i j k < 2 * (n : ℤ) := by
  obtain ⟨hi1, hi2⟩ := index_bounds hi
  rw [reducedAB_eq]
  omega

lemma reducedAC_bounds {n i j k : ℕ} (hn : 0 < n)
    (hj : j ∈ indices n) :
    -2 * (n : ℤ) < reducedA n i j k + reducedC n i j k ∧
      reducedA n i j k + reducedC n i j k < 2 * (n : ℤ) := by
  obtain ⟨hj1, hj2⟩ := index_bounds hj
  rw [reducedAC_eq]
  omega

lemma reducedBC_bounds {n i j k : ℕ} (hn : 0 < n)
    (hk : k ∈ indices n) :
    -2 * (n : ℤ) < reducedB n i j k + reducedC n i j k ∧
      reducedB n i j k + reducedC n i j k < 2 * (n : ℤ) := by
  obtain ⟨hk1, hk2⟩ := index_bounds hk
  rw [reducedBC_eq]
  omega

#print axioms reducedA_bounds
#print axioms reducedAB_bounds

end A387471
