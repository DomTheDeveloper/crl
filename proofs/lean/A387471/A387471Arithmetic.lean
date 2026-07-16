import Mathlib

/-!
# Arithmetic lemmas for the specialized weight-six Mann theorem
-/

namespace A387471

/-- If a positive integer does not divide `30`, then it has either a prime
factor larger than six or a repeated prime factor. -/
theorem exists_bad_prime_of_not_dvd_thirty {N : ℕ} (hN : N ≠ 0)
    (hnot : ¬ N ∣ 30) :
    ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ (6 < p ∨ p ^ 2 ∣ N) := by
  by_contra hbad
  apply hnot
  rw [← Nat.factorization_le_iff_dvd hN (by norm_num)]
  intro p
  by_cases hp : p.Prime
  · by_cases hpd : p ∣ N
    · have hp_le : p ≤ 6 := by
        by_contra hp6
        exact hbad ⟨p, hp, hpd, Or.inl (lt_of_not_ge hp6)⟩
      have hsq : ¬ p ^ 2 ∣ N := by
        intro hsq
        exact hbad ⟨p, hp, hpd, Or.inr hsq⟩
      have hfac : N.factorization p ≤ 1 := by
        by_contra hle
        have htwo : 2 ≤ N.factorization p := by omega
        exact hsq ((hp.pow_dvd_iff_le_factorization hN).2 htwo)
      interval_cases p <;> norm_num at hp ⊢
      all_goals simpa using hfac
    · simp [Nat.factorization_eq_zero_of_not_dvd hpd]
  · simp [Nat.factorization_eq_zero_of_not_prime N hp]

/-- A set of at most six residue classes modulo a prime larger than six misses
at least one class. -/
theorem exists_missing_residue {ι : Type*} [DecidableEq ι] {p : ℕ}
    (hp : p.Prime) (s : Finset ι) (tag : ι → ZMod p)
    (hcard : s.card ≤ 6) (hp6 : 6 < p) :
    ∃ r : ZMod p, ∀ i ∈ s, tag i ≠ r := by
  classical
  by_contra h
  push_neg at h
  have hsurj : Set.SurjOn tag (s : Set ι) Set.univ := by
    intro r _
    obtain ⟨i, hi, hir⟩ := h r
    exact ⟨i, hi, hir⟩
  have hle : Fintype.card (ZMod p) ≤ s.card := by
    simpa using Finset.card_le_card_of_surjOn hsurj
  have hpcard : Fintype.card (ZMod p) = p := ZMod.card p
  omega

#print axioms exists_bad_prime_of_not_dvd_thirty
#print axioms exists_missing_residue

end A387471
