import A387471PairLabels
import A387471TripleLabels

/-!
# The nonminimal six-root branch
-/

open Finset
open scoped BigOperators

namespace A387471

lemma sixRoot_ne_zero {n : ℕ} {A B C : ℤ} (r : Fin 6) : sixRoot n A B C r ≠ 0 := by
  fin_cases r <;> simp [sixRoot, Complex.exp_ne_zero]

lemma vanishes_sdiff {ι : Type*} [DecidableEq ι] (s t : Finset ι) (z : ι → ℂ)
    (hts : t ⊆ s) (hs : Vanishes s z) (ht : Vanishes t z) :
    Vanishes (s \ t) z := by
  rw [Vanishes] at hs ht ⊢
  have hsplit := Finset.sum_sdiff hts (f := z)
  rw [hs, ht] at hsplit
  simpa using hsplit

lemma singleton_not_vanishes {n : ℕ} {A B C : ℤ} (r : Fin 6) :
    ¬ Vanishes {r} (sixRoot n A B C) := by
  simp [Vanishes, sixRoot_ne_zero]

/-- If the full six-root sum is not minimal, the admissible relation is ordinary. -/
theorem nonminimal_six_root_classification {n : ℕ} (hn : 0 < n)
    {A B C : ℤ}
    (hA : -3 * (n : ℤ) < A ∧ A < 3 * (n : ℤ))
    (hB : -3 * (n : ℤ) < B ∧ B < 3 * (n : ℤ))
    (hC : -3 * (n : ℤ) < C ∧ C < 3 * (n : ℤ))
    (hAB : -2 * (n : ℤ) < A + B ∧ A + B < 2 * (n : ℤ))
    (hAC : -2 * (n : ℤ) < A + C ∧ A + C < 2 * (n : ℤ))
    (hBC : -2 * (n : ℤ) < B + C ∧ B + C < 2 * (n : ℤ))
    (hsin : Real.sin (latticeAngle n A) + Real.sin (latticeAngle n B) +
      Real.sin (latticeAngle n C) = 0)
    (hnotmin : ¬ MinimallyVanishes Finset.univ (sixRoot n A B C)) :
    ABCClassified (n : ℤ) A B C := by
  have hfull : Vanishes Finset.univ (sixRoot n A B C) :=
    sixRoot_vanishes_of_sines hsin
  have hex : ∃ t : Finset (Fin 6), t ⊂ Finset.univ ∧ t.Nonempty ∧
      Vanishes t (sixRoot n A B C) := by
    by_contra hno
    apply hnotmin
    refine ⟨by simp, hfull, ?_⟩
    intro t htproper htne htvan
    exact hno ⟨t, htproper, htne, htvan⟩
  obtain ⟨t, htproper, htne, htvan⟩ := hex
  have htpos : 0 < t.card := Finset.card_pos.mpr htne
  have htlt : t.card < 6 := by
    have hcard := Finset.card_lt_card htproper
    simpa using hcard
  have htcases : t.card = 1 ∨ t.card = 2 ∨ t.card = 3 ∨
      t.card = 4 ∨ t.card = 5 := by omega
  rcases htcases with htc | htc | htc | htc | htc
  · obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp htc
    exact (singleton_not_vanishes r htvan).elim
  · obtain ⟨r, s, hrs, rfl⟩ := Finset.card_eq_two.mp htc
    have hpair : sixRoot n A B C r + sixRoot n A B C s = 0 := by
      simpa [Vanishes, hrs] using htvan
    exact Or.inl (labeled_pair_implies_ordinary hn hA hB hC hAB hAC hBC hsin
      r s hrs hpair)
  · obtain ⟨r, s, u, hrs, hru, hsu, rfl⟩ := Finset.card_eq_three.mp htc
    have htriple : sixRoot n A B C r + sixRoot n A B C s +
        sixRoot n A B C u = 0 := by
      simpa [Vanishes, hrs, hru, hsu, add_assoc, add_left_comm, add_comm] using htvan
    exact (labeled_triple_impossible hn hA hB hC hAB hAC hBC
      r s u hrs hru hsu htriple).elim
  · let u : Finset (Fin 6) := Finset.univ \ t
    have huvan : Vanishes u (sixRoot n A B C) :=
      vanishes_sdiff Finset.univ t (sixRoot n A B C) htproper.1 hfull htvan
    have hucard : u.card = 2 := by
      change (Finset.univ \ t).card = 2
      rw [Finset.card_sdiff_of_subset htproper.1]
      simp [htc]
    obtain ⟨r, s, hrs, hu⟩ := Finset.card_eq_two.mp hucard
    have hpair : sixRoot n A B C r + sixRoot n A B C s = 0 := by
      rw [hu] at huvan
      simpa [Vanishes, hrs] using huvan
    exact Or.inl (labeled_pair_implies_ordinary hn hA hB hC hAB hAC hBC hsin
      r s hrs hpair)
  · let u : Finset (Fin 6) := Finset.univ \ t
    have huvan : Vanishes u (sixRoot n A B C) :=
      vanishes_sdiff Finset.univ t (sixRoot n A B C) htproper.1 hfull htvan
    have hucard : u.card = 1 := by
      change (Finset.univ \ t).card = 1
      rw [Finset.card_sdiff_of_subset htproper.1]
      simp [htc]
    obtain ⟨r, hu⟩ := Finset.card_eq_one.mp hucard
    rw [hu] at huvan
    exact (singleton_not_vanishes r huvan).elim

/-- Specialization of the nonminimal branch to reduced cevian coefficients. -/
theorem nonminimal_reduced_classification {n i j k : ℕ} (hn : 0 < n)
    (hi : i ∈ indices n) (hj : j ∈ indices n) (hk : k ∈ indices n)
    (hsin : ReducedSineEquation n i j k)
    (hnotmin : ¬ MinimallyVanishes Finset.univ
      (sixRoot n (reducedA n i j k) (reducedB n i j k) (reducedC n i j k))) :
    ABCClassified (n : ℤ) (reducedA n i j k) (reducedB n i j k)
      (reducedC n i j k) :=
  nonminimal_six_root_classification hn
    (reducedA_bounds hn hi hj hk)
    (reducedB_bounds hn hi hj hk)
    (reducedC_bounds hn hi hj hk)
    (reducedAB_bounds hn hi)
    (reducedAC_bounds hn hj)
    (reducedBC_bounds hn hk)
    hsin hnotmin

#print axioms nonminimal_six_root_classification
#print axioms nonminimal_reduced_classification

end A387471
