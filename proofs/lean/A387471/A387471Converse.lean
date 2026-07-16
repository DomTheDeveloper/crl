import A387471GridClassification

/-!
# Converse: every classified index family is a solution
-/

namespace A387471

lemma ordinaryABC_of_indices_reduced {n i j k : ℕ}
    (h : OrdinaryIndices (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ)) :
    ∃ s : ℤ, Perm3 (reducedA n i j k) (reducedB n i j k)
      (reducedC n i j k) 0 s (-s) := by
  rcases h with ⟨hi, hjk⟩ | ⟨hj, hik⟩ | ⟨hk, hij⟩
  · refine ⟨reducedA n i j k, ?_⟩
    simp only [Perm3]
    simp [reducedA, reducedB, reducedC]
    omega
  · refine ⟨reducedA n i j k, ?_⟩
    simp only [Perm3]
    simp [reducedA, reducedB, reducedC]
    omega
  · refine ⟨reducedA n i j k, ?_⟩
    simp only [Perm3]
    simp [reducedA, reducedB, reducedC]
    omega

lemma exceptionalABC_of_indices_reduced {n i j k : ℕ}
    (h : ExceptionalIndices (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ)) :
    ExceptionalABC (n : ℤ) (reducedA n i j k) (reducedB n i j k)
      (reducedC n i j k) := by
  rcases h with ⟨q, hnq, hp | hp⟩
  · refine ⟨q, hnq, Or.inl ?_⟩
    rcases hp with h | h | h | h | h | h
    all_goals rcases h with ⟨hi, hj, hk⟩
    all_goals simp only [Perm3]
    all_goals simp [reducedA, reducedB, reducedC]
    all_goals omega
  · refine ⟨q, hnq, Or.inr ?_⟩
    rcases hp with h | h | h | h | h | h
    all_goals rcases h with ⟨hi, hj, hk⟩
    all_goals simp only [Perm3]
    all_goals simp [reducedA, reducedB, reducedC]
    all_goals omega

lemma sine_sum_of_ordinaryABC {n : ℕ} {A B C s : ℤ}
    (h : Perm3 A B C 0 s (-s)) :
    Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0 := by
  rcases h with h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl, rfl⟩
  all_goals simp [latticeAngle, add_assoc, add_left_comm, add_comm]

lemma exceptional_lattice_angles {n : ℕ} (hn : 0 < n) {q : ℤ}
    (hnq : (n : ℤ) = 5 * q) :
    latticeAngle n (-5 * q) = -Real.pi / 6 ∧
    latticeAngle n (-3 * q) = -Real.pi / 10 ∧
    latticeAngle n (9 * q) = 3 * Real.pi / 10 ∧
    latticeAngle n (-9 * q) = -3 * Real.pi / 10 ∧
    latticeAngle n (3 * q) = Real.pi / 10 ∧
    latticeAngle n (5 * q) = Real.pi / 6 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnqR : (n : ℝ) = 5 * (q : ℝ) := by exact_mod_cast hnq
  constructor
  · simp [latticeAngle]
    field_simp [hn0]
    nlinarith
  constructor
  · simp [latticeAngle]
    field_simp [hn0]
    nlinarith
  constructor
  · simp [latticeAngle]
    field_simp [hn0]
    nlinarith
  constructor
  · simp [latticeAngle]
    field_simp [hn0]
    nlinarith
  constructor
  · simp [latticeAngle]
    field_simp [hn0]
    nlinarith
  · simp [latticeAngle]
    field_simp [hn0]
    nlinarith

lemma sine_sum_of_exceptionalABC {n : ℕ} (hn : 0 < n) {A B C : ℤ}
    (h : ExceptionalABC (n : ℤ) A B C) :
    Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0 := by
  rcases h with ⟨q, hnq, hp | hp⟩
  have hang := exceptional_lattice_angles hn hnq
  rcases hang with ⟨h5n, h3n, h9p, h9n, h3p, h5p⟩
  · rcases hp with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals simp only [h5n, h3n, h9p]
    all_goals first
      | exact exceptional_sine_identity_one
      | simpa [add_assoc, add_left_comm, add_comm] using exceptional_sine_identity_one
  · rcases hp with h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals simp only [h9n, h3p, h5p]
    all_goals first
      | exact exceptional_sine_identity_two
      | simpa [add_assoc, add_left_comm, add_comm] using exceptional_sine_identity_two

lemma reducedSineEquation_of_IndexClassified {n i j k : ℕ} (hn : 0 < n)
    (h : IndexClassified (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ)) :
    ReducedSineEquation n i j k := by
  rcases h with hord | hexc
  · obtain ⟨s, hs⟩ := ordinaryABC_of_indices_reduced hord
    exact sine_sum_of_ordinaryABC hs
  · exact sine_sum_of_exceptionalABC hn (exceptionalABC_of_indices_reduced hexc)

/-- Every classified admissible triple satisfies trigonometric Ceva. -/
theorem concurrent_of_IndexClassified {n i j k : ℕ} (hn : 0 < n)
    (h : IndexClassified (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ)) :
    CevianConcurrent n i j k :=
  (cevianConcurrent_iff_reduced n i j k hn).mpr
    (reducedSineEquation_of_IndexClassified hn h)

/-- On the allowed box, concurrence is exactly the classified index predicate. -/
theorem concurrent_iff_indexClassified {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n) :
    CevianConcurrent n i j k ↔
      IndexClassified (n : ℤ) (i : ℤ) (j : ℤ) (k : ℤ) := by
  constructor
  · exact every_solution_indexClassified n i j k hn hi hj hk
  · exact concurrent_of_IndexClassified hn

#print axioms concurrent_of_IndexClassified
#print axioms concurrent_iff_indexClassified

end A387471
