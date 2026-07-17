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
        have hnot_two : ¬ 2 ≤ N.factorization p := by
          intro htwo
          exact hsq ((hp.pow_dvd_iff_le_factorization hN).2 htwo)
        exact Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hnot_two)
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
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_contra h
  push_neg at h
  have huniv : (Finset.univ : Finset (ZMod p)) ⊆ s.image tag := by
    intro r _
    obtain ⟨i, hi, hir⟩ := h r
    exact Finset.mem_image.mpr ⟨i, hi, hir⟩
  have hle_image : Fintype.card (ZMod p) ≤ (s.image tag).card := by
    simpa using Finset.card_le_card huniv
  have hle : Fintype.card (ZMod p) ≤ s.card :=
    hle_image.trans Finset.card_image_le
  have hpcard : Fintype.card (ZMod p) = p := ZMod.card p
  omega

/-- The power used to realize the Fourier frequency `t` by a Galois
conjugation fixing the quotient-conductor part. -/
def conjugatingExponent (p m : ℕ) (t : ZMod p) : ℕ :=
  1 + (p - t.val) * m

/-- The conjugating exponent is always coprime to the quotient part `m`. -/
theorem conjugatingExponent_coprime_quotient (p m : ℕ) (t : ZMod p) :
    (conjugatingExponent p m t).Coprime m := by
  simp [conjugatingExponent]

/-- If `p ∣ m`, every Fourier frequency is represented by an exponent coprime
to the full conductor `p*m`. -/
theorem conjugatingExponent_coprime_squareful {p m : ℕ} (hp : p.Prime)
    (hpm : p ∣ m) (t : ZMod p) :
    (conjugatingExponent p m t).Coprime (p * m) := by
  let u := conjugatingExponent p m t
  have hum : u.Coprime m := conjugatingExponent_coprime_quotient p m t
  refine Nat.coprime_of_dvd ?_
  intro q hq hqu hqpm
  have hqm : q ∣ m := by
    rcases (hq.dvd_mul.mp hqpm) with hqp | hqm
    · have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      simpa [hqp_eq] using hpm
    · exact hqm
  exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hum hqu hqm)

/-- Outside the unique missing frequency `m⁻¹`, the conjugating exponent is
coprime to `p*m` when `p ∤ m`. -/
theorem conjugatingExponent_coprime_squarefree {p m : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) (t : ZMod p)
    (ht : t ≠ ((m : ZMod p)⁻¹)) :
    (conjugatingExponent p m t).Coprime (p * m) := by
  letI : Fact p.Prime := ⟨hp⟩
  let u := conjugatingExponent p m t
  have hum : u.Coprime m := conjugatingExponent_coprime_quotient p m t
  have hm0 : (m : ZMod p) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hpm
  have hup : u.Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hpu
    have hu0 : (u : ZMod p) = 0 := by
      simpa [ZMod.natCast_eq_zero_iff] using hpu
    have hrel : (1 : ZMod p) - t * (m : ZMod p) = 0 := by
      simpa [u, conjugatingExponent, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub (Nat.le_of_lt t.val_lt), ZMod.natCast_zmod_val,
        sub_eq_add_neg] using hu0
    have htm : t * (m : ZMod p) = 1 := (sub_eq_zero.mp hrel).symm
    exact ht (eq_inv_of_mul_eq_one_left htm)
  refine Nat.coprime_of_dvd ?_
  intro q hq hqu hqpm
  rcases (hq.dvd_mul.mp hqpm) with hqp | hqm
  · exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hup hqu hqp)
  · exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hum hqu hqm)

#print axioms exists_bad_prime_of_not_dvd_thirty
#print axioms exists_missing_residue
#print axioms conjugatingExponent_coprime_quotient
#print axioms conjugatingExponent_coprime_squareful
#print axioms conjugatingExponent_coprime_squarefree

end A387471
