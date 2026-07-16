import A387471Mann

/-!
# Completion of the weight-six Mann reduction

This module performs conductor descent after the prime-residue collapse proved
in `A387471Mann`.  It yields the exact specialized Mann theorem needed by the
A387471 roots-of-unity classification.
-/

open Complex Finset
open scoped BigOperators ZMod

namespace A387471

/-- Dividing a minimal relation by one labeled term and lowering the conductor
preserves minimality. -/
theorem exists_normalized_relation {ι : Type*} {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0)
    (s : Finset ι) (a : ι → Fin (p * m))
    (hmin : MinimallyVanishes s
      (fun i ↦ canonicalRoot (p * m) ^ (a i).val))
    (hconst : ∃ r : ZMod p,
      ∀ i ∈ s, exponentResidue (p := p) (a i) = r) :
    ∃ i₀ ∈ s, ∃ b : ι → Fin m,
      (∀ i ∈ s,
        canonicalRoot m ^ (b i).val =
          canonicalRoot (p * m) ^ (a i).val /
            canonicalRoot (p * m) ^ (a i₀).val) ∧
      MinimallyVanishes s (fun i ↦ canonicalRoot m ^ (b i).val) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero m := ⟨hm⟩
  obtain ⟨i₀, hi₀⟩ := hmin.1
  obtain ⟨r, hconst⟩ := hconst
  have hexp : ∀ i, i ∈ s → ∃ d : Fin m,
      canonicalRoot m ^ d.val =
        canonicalRoot (p * m) ^ (a i).val /
          canonicalRoot (p * m) ^ (a i₀).val := by
    intro i hi
    apply exists_canonical_ratio_exponent hp hm (a i) (a i₀)
    simpa [exponentResidue] using (hconst i hi).trans (hconst i₀ hi₀).symm
  let b : ι → Fin m := fun i ↦
    if hi : i ∈ s then Classical.choose (hexp i hi) else 0
  have hb : ∀ i ∈ s,
      canonicalRoot m ^ (b i).val =
        canonicalRoot (p * m) ^ (a i).val /
          canonicalRoot (p * m) ^ (a i₀).val := by
    intro i hi
    simp only [b, hi, dite_true]
    exact Classical.choose_spec (hexp i hi)
  have hN : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm
  have hroot0 : canonicalRoot (p * m) ≠ 0 :=
    (canonicalRoot_isPrimitive hN).ne_zero hN
  have hbase : canonicalRoot (p * m) ^ (a i₀).val ≠ 0 :=
    pow_ne_zero _ hroot0
  have hratio_vanish :
      ∑ i ∈ s,
        canonicalRoot (p * m) ^ (a i).val /
          canonicalRoot (p * m) ^ (a i₀).val = 0 := by
    calc
      (∑ i ∈ s,
        canonicalRoot (p * m) ^ (a i).val /
          canonicalRoot (p * m) ^ (a i₀).val) =
          (∑ i ∈ s, canonicalRoot (p * m) ^ (a i).val) /
            canonicalRoot (p * m) ^ (a i₀).val := by
              rw [Finset.sum_div]
      _ = 0 := by
        rw [show ∑ i ∈ s, canonicalRoot (p * m) ^ (a i).val = 0 by
          simpa [Vanishes] using hmin.2.1]
        simp
  have hvan_b : Vanishes s (fun i ↦ canonicalRoot m ^ (b i).val) := by
    rw [Vanishes]
    calc
      (∑ i ∈ s, canonicalRoot m ^ (b i).val) =
          ∑ i ∈ s,
            canonicalRoot (p * m) ^ (a i).val /
              canonicalRoot (p * m) ^ (a i₀).val := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hb i hi
      _ = 0 := hratio_vanish
  have hmin_b : MinimallyVanishes s (fun i ↦ canonicalRoot m ^ (b i).val) := by
    refine ⟨hmin.1, hvan_b, ?_⟩
    intro t ht htnonempty htvan
    apply hmin.2.2 t ht htnonempty
    rw [Vanishes] at htvan ⊢
    have htsub : t ⊆ s := ht.1
    have hratio_t :
        ∑ i ∈ t,
          canonicalRoot (p * m) ^ (a i).val /
            canonicalRoot (p * m) ^ (a i₀).val = 0 := by
      calc
        (∑ i ∈ t,
          canonicalRoot (p * m) ^ (a i).val /
            canonicalRoot (p * m) ^ (a i₀).val) =
            ∑ i ∈ t, canonicalRoot m ^ (b i).val := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (hb i (htsub hi)).symm
        _ = 0 := htvan
    calc
      (∑ i ∈ t, canonicalRoot (p * m) ^ (a i).val) =
          ((∑ i ∈ t, canonicalRoot (p * m) ^ (a i).val) /
              canonicalRoot (p * m) ^ (a i₀).val) *
            canonicalRoot (p * m) ^ (a i₀).val := by
              field_simp
      _ = (∑ i ∈ t,
          canonicalRoot (p * m) ^ (a i).val /
            canonicalRoot (p * m) ^ (a i₀).val) *
          canonicalRoot (p * m) ^ (a i₀).val := by
            rw [Finset.sum_div]
      _ = 0 := by rw [hratio_t, zero_mul]
  exact ⟨i₀, hi₀, b, hb, hmin_b⟩

/-- Specialized Mann theorem: in a minimal vanishing sum of at most six powers
of a canonical root, every quotient is a 30th root of unity. -/
theorem mann_weight_six_canonical {ι : Type*} :
    ∀ N : ℕ, N ≠ 0 → ∀ (s : Finset ι) (a : ι → Fin N),
      s.card ≤ 6 →
      MinimallyVanishes s (fun i ↦ canonicalRoot N ^ (a i).val) →
      ∀ i ∈ s, ∀ j ∈ s,
        (canonicalRoot N ^ (a i).val /
          canonicalRoot N ^ (a j).val) ^ 30 = 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN s a hcard hmin i hi j hj
      by_cases hdiv : N ∣ 30
      · obtain ⟨q, h30⟩ := hdiv
        have hroot := canonicalRoot_isPrimitive hN
        have hroot0 : canonicalRoot N ≠ 0 := hroot.ne_zero hN
        have hxi : (canonicalRoot N ^ (a i).val) ^ N = 1 := by
          calc
            (canonicalRoot N ^ (a i).val) ^ N =
                (canonicalRoot N ^ N) ^ (a i).val := by
                  rw [← pow_mul, ← pow_mul]
                  congr 1
                  omega
            _ = 1 := by rw [hroot.pow_eq_one, one_pow]
        have hxj : (canonicalRoot N ^ (a j).val) ^ N = 1 := by
          calc
            (canonicalRoot N ^ (a j).val) ^ N =
                (canonicalRoot N ^ N) ^ (a j).val := by
                  rw [← pow_mul, ← pow_mul]
                  congr 1
                  omega
            _ = 1 := by rw [hroot.pow_eq_one, one_pow]
        have hratioN :
            (canonicalRoot N ^ (a i).val /
              canonicalRoot N ^ (a j).val) ^ N = 1 := by
          rw [div_pow, hxi, hxj, one_div]
        rw [h30, pow_mul, hratioN, one_pow]
      · obtain ⟨p, hp, hpN, hbad⟩ :=
          exists_bad_prime_of_not_dvd_thirty hN hdiv
        obtain ⟨m, rfl⟩ := hpN
        have hm : m ≠ 0 := by
          intro hm0
          subst m
          simp at hN
        have hbad' : p ∣ m ∨ 6 < p := by
          rcases hbad with hp6 | hsq
          · exact Or.inr hp6
          · left
            rw [pow_two] at hsq
            exact Nat.dvd_of_mul_dvd_mul_left hp.pos hsq
        have hconst := residue_constant_bad_prime hp hm s a hcard hmin hbad'
        obtain ⟨i₀, hi₀, b, hb, hmin_b⟩ :=
          exists_normalized_relation hp hm s a hmin hconst
        have hm_lt : m < p * m := by
          have hmpos := Nat.pos_of_ne_zero hm
          have hp2 := hp.two_le
          nlinarith
        have hind := ih m hm_lt hm s b hcard hmin_b i hi j hj
        have hN0 : canonicalRoot (p * m) ≠ 0 :=
          (canonicalRoot_isPrimitive (mul_ne_zero hp.ne_zero hm)).ne_zero
            (mul_ne_zero hp.ne_zero hm)
        have hbase : canonicalRoot (p * m) ^ (a i₀).val ≠ 0 :=
          pow_ne_zero _ hN0
        have hden : canonicalRoot (p * m) ^ (a j).val ≠ 0 :=
          pow_ne_zero _ hN0
        have hratio :
            canonicalRoot (p * m) ^ (a i).val /
                canonicalRoot (p * m) ^ (a j).val =
              canonicalRoot m ^ (b i).val /
                canonicalRoot m ^ (b j).val := by
          rw [hb i hi, hb j hj]
          field_simp
        rw [hratio]
        exact hind

#print axioms exists_normalized_relation
#print axioms mann_weight_six_canonical

end A387471
