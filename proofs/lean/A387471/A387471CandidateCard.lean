import A387471Parameters

/-!
# Exact cardinality of the classified candidate set
-/

open Finset

namespace A387471

/-- A triple contains the central coordinate `n`. -/
def HasCentralCoordinate (n : ℕ) (t : Triple) : Prop :=
  t.1 = n ∨ t.2.1 = n ∨ t.2.2 = n

lemma ordinaryParam_hasCentral (n : ℕ) (p : OrdinaryParam n) :
    HasCentralCoordinate n (ordinaryParamTriple n p) := by
  rcases p with ⟨r, σ⟩
  fin_cases σ <;> simp [HasCentralCoordinate, ordinaryParamTriple, permTripleNat]

lemma hasCentral_of_mem_ordinarySet {n : ℕ} {t : Triple}
    (h : t ∈ ordinarySet n) : HasCentralCoordinate n t := by
  rw [ordinarySet, Finset.mem_insert] at h
  rcases h with rfl | h
  · simp [HasCentralCoordinate]
  · rcases Finset.mem_image.mp h with ⟨p, -, rfl⟩
    exact ordinaryParam_hasCentral n p

lemma exceptionalParam_notCentral {q : ℕ} (hq : 0 < q) (p : ExceptionalParam) :
    ¬ HasCentralCoordinate (5 * q) (exceptionalParamTriple q p) := by
  rcases p with ⟨f, σ⟩
  fin_cases f <;> fin_cases σ <;>
    simp [HasCentralCoordinate, exceptionalParamTriple, permTripleNat] <;> omega

lemma not_hasCentral_of_mem_exceptionalSet {q : ℕ} (hq : 0 < q) {t : Triple}
    (h : t ∈ exceptionalSet q) : ¬ HasCentralCoordinate (5 * q) t := by
  rcases Finset.mem_image.mp h with ⟨p, -, rfl⟩
  exact exceptionalParam_notCentral hq p

/-- The ordinary and exceptional families are disjoint. -/
theorem ordinary_exceptional_disjoint {q : ℕ} (hq : 0 < q) :
    Disjoint (ordinarySet (5 * q)) (exceptionalSet q) := by
  rw [Finset.disjoint_left]
  intro t ho he
  exact not_hasCentral_of_mem_exceptionalSet hq he (hasCentral_of_mem_ordinarySet ho)

/-- The exact classified set, with exceptional points included iff `5∣n`. -/
def candidateSet (n : ℕ) : Finset Triple :=
  if h : 5 ∣ n then ordinarySet n ∪ exceptionalSet (n / 5) else ordinarySet n

lemma div_five_pos {n : ℕ} (hn : 0 < n) (h5 : 5 ∣ n) : 0 < n / 5 := by
  rcases h5 with ⟨q, rfl⟩
  simp
  omega

lemma five_mul_div_five {n : ℕ} (h5 : 5 ∣ n) : 5 * (n / 5) = n :=
  Nat.mul_div_cancel' h5

/-- Exact cardinality of the classified set. -/
theorem card_candidateSet (n : ℕ) (hn : 1 ≤ n) :
    (candidateSet n).card = closedForm n := by
  have hnpos : 0 < n := hn
  by_cases h5 : 5 ∣ n
  · rw [candidateSet, dif_pos h5]
    have hq : 0 < n / 5 := div_five_pos hnpos h5
    have hdis : Disjoint (ordinarySet n) (exceptionalSet (n / 5)) := by
      rw [← five_mul_div_five h5]
      exact ordinary_exceptional_disjoint hq
    rw [Finset.card_union_of_disjoint hdis, card_ordinarySet hnpos,
      card_exceptionalSet hq]
    rw [closedForm_eq_family_count n hn]
    simp [h5]
  · rw [candidateSet, dif_neg h5, card_ordinarySet hnpos]
    rw [closedForm_eq_family_count n hn]
    simp [h5]

#print axioms ordinary_exceptional_disjoint
#print axioms card_candidateSet

end A387471
