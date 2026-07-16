import Mathlib

/-!
# Finite Fourier lemmas for the A387471 Mann reduction

The lemmas here are stated for an arbitrary prime order and an arbitrary
primitive complex root of unity.  They are the linear-algebra engine used to
eliminate prime factors from a minimal vanishing sum.
-/

open scoped BigOperators

namespace A387471

/-- A nontrivial character of a prime cyclic group has zero total sum. -/
theorem twisted_sum_zero_prime {p : ℕ} (hp : p.Prime) {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) (d : ZMod p) (hd : d ≠ 0) :
    (∑ j : Fin p, ω ^ (d.val * j.val)) = 0 := by
  have hdval_ne : d.val ≠ 0 := by
    intro h
    exact hd (ZMod.val_eq_zero.mp h)
  have hnotdvd : ¬ p ∣ d.val := by
    intro hpd
    exact hdval_ne (Nat.eq_zero_of_dvd_of_lt hpd d.val_lt)
  have hcop : Nat.Coprime d.val p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact hnotdvd
  have hprim : IsPrimitiveRoot (ω ^ d.val) p := hω.pow_of_coprime d.val hcop
  rw [Fin.sum_univ_eq_sum_range]
  simpa [pow_mul] using hprim.geom_sum_eq_zero hp.one_lt

/-- Character orthogonality for powers of an arbitrary primitive root of
prime order. -/
theorem character_orthogonality_prime {p : ℕ} (hp : p.Prime) {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) (a b : Fin p) :
    (∑ t : ZMod p,
      (ω ^ (t.val * a.val)) * (ω ^ (t.val * b.val))⁻¹) =
      if a = b then (p : ℂ) else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    have hω0 : ω ≠ 0 := hω.ne_zero
    simp [hω0]
  · have hω0 : ω ≠ 0 := hω.ne_zero
    let a' : ZMod p := a
    let b' : ZMod p := b
    let d : ZMod p := a' - b'
    have hd : d ≠ 0 := by
      intro hd0
      apply hab
      have : a' = b' := sub_eq_zero.mp hd0
      exact_mod_cast this
    have hval : (d.val + b.val) % p = a.val := by
      have hdiff : d + b' = a' := sub_add_cancel a' b'
      have h := congrArg ZMod.val hdiff
      simpa [ZMod.val_add] using h
    have hmul : ω ^ d.val * ω ^ b.val = ω ^ a.val := by
      calc
        ω ^ d.val * ω ^ b.val = ω ^ (d.val + b.val) := by
          simpa using (pow_add ω d.val b.val).symm
        _ = ω ^ ((d.val + b.val) % p) := by
          simpa using
            (pow_eq_pow_mod (a := ω) (n := p) (m := d.val + b.val) hω.pow_eq_one)
        _ = ω ^ a.val := by simp [hval]
    have hbase : ω ^ a.val * (ω ^ b.val)⁻¹ = ω ^ d.val := by
      have hb0 : ω ^ b.val ≠ 0 := pow_ne_zero _ hω0
      calc
        ω ^ a.val * (ω ^ b.val)⁻¹ =
            (ω ^ d.val * ω ^ b.val) * (ω ^ b.val)⁻¹ := by rw [hmul]
        _ = ω ^ d.val := by simp [mul_assoc, hb0]
    have hintegrand : ∀ t : ZMod p,
        (ω ^ (t.val * a.val)) * (ω ^ (t.val * b.val))⁻¹ =
          ω ^ (d.val * t.val) := by
      intro t
      calc
        (ω ^ (t.val * a.val)) * (ω ^ (t.val * b.val))⁻¹ =
            ((ω ^ a.val) ^ t.val) * ((ω ^ b.val) ^ t.val)⁻¹ := by
              rw [pow_mul', pow_mul']
        _ = ((ω ^ a.val) ^ t.val) * (((ω ^ b.val)⁻¹) ^ t.val) := by
              rw [(inv_pow (ω ^ b.val) t.val).symm]
        _ = ((ω ^ a.val) * (ω ^ b.val)⁻¹) ^ t.val := by
              simpa using (mul_pow (ω ^ a.val) ((ω ^ b.val)⁻¹) t.val).symm
        _ = (ω ^ d.val) ^ t.val := by rw [hbase]
        _ = ω ^ (d.val * t.val) := by
              simpa using (pow_mul ω d.val t.val).symm
    calc
      (∑ t : ZMod p,
          (ω ^ (t.val * a.val)) * (ω ^ (t.val * b.val))⁻¹) =
          ∑ t : ZMod p, ω ^ (d.val * t.val) := by simp [hintegrand]
      _ = ∑ t : Fin p, ω ^ (d.val * t.val) := by
        exact Fintype.sum_equiv ZMod.finEquiv _ _ (fun _ ↦ rfl)
      _ = 0 := twisted_sum_zero_prime hp hω d hd
      _ = if a = b then (p : ℂ) else 0 := by simp [hab]

/-- Fourier transform with respect to powers of a chosen primitive root. -/
noncomputable def rootFourier {p : ℕ} (ω : ℂ) (v : Fin p → ℂ) (t : ZMod p) : ℂ :=
  ∑ r : Fin p, ω ^ (t.val * r.val) * v r

/-- Pointwise Fourier inversion.  The formulation avoids dividing by `p`,
which is convenient for kernel-checked cancellation. -/
theorem rootFourier_inversion {p : ℕ} (hp : p.Prime) {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) (v : Fin p → ℂ) (r : Fin p) :
    (p : ℂ) * v r =
      ∑ t : ZMod p, (ω ^ (t.val * r.val))⁻¹ * rootFourier ω v t := by
  classical
  rw [rootFourier]
  calc
    (p : ℂ) * v r =
        ∑ s : Fin p,
          (if s = r then (p : ℂ) else 0) * v s := by simp
    _ = ∑ s : Fin p,
          (∑ t : ZMod p,
            (ω ^ (t.val * s.val)) * (ω ^ (t.val * r.val))⁻¹) * v s := by
          congr 1
          funext s
          rw [character_orthogonality_prime hp hω s r]
    _ = ∑ t : ZMod p,
          (ω ^ (t.val * r.val))⁻¹ *
            ∑ s : Fin p, ω ^ (t.val * s.val) * v s := by
          rw [Finset.sum_comm]
          congr 1
          funext t
          rw [Finset.mul_sum]
          congr 1
          funext s
          ring

/-- If all Fourier coefficients except possibly one vanish, and one original
coordinate vanishes, then every coordinate vanishes.  This is the exact
`p-1`-conjugate argument used in the squarefree prime step of Mann's theorem. -/
theorem rootFourier_eq_zero_of_one_missing {p : ℕ} (hp : p.Prime) {ω : ℂ}
    (hω : IsPrimitiveRoot ω p) (v : Fin p → ℂ) (t₀ : ZMod p) (r₀ : Fin p)
    (hv₀ : v r₀ = 0)
    (hvan : ∀ t : ZMod p, t ≠ t₀ → rootFourier ω v t = 0) :
    v = 0 := by
  classical
  have hω0 : ω ≠ 0 := hω.ne_zero
  have hFt₀ : rootFourier ω v t₀ = 0 := by
    have hinv := rootFourier_inversion hp hω v r₀
    rw [hv₀, mul_zero] at hinv
    have hsingle :
        (∑ t : ZMod p,
          (ω ^ (t.val * r₀.val))⁻¹ * rootFourier ω v t) =
          (ω ^ (t₀.val * r₀.val))⁻¹ * rootFourier ω v t₀ := by
      apply Fintype.sum_eq_single t₀
      intro t ht
      rw [hvan t ht, mul_zero]
    rw [hsingle] at hinv
    exact (mul_eq_zero.mp hinv.symm).resolve_left (inv_ne_zero (pow_ne_zero _ hω0))
  funext r
  have hinv := rootFourier_inversion hp hω v r
  have hall : ∀ t : ZMod p, rootFourier ω v t = 0 := by
    intro t
    by_cases ht : t = t₀
    · simpa [ht] using hFt₀
    · exact hvan t ht
  simp_rw [hall, mul_zero, Finset.sum_const_zero] at hinv
  exact (mul_eq_zero.mp hinv).resolve_left (by exact_mod_cast hp.ne_zero)

#print axioms twisted_sum_zero_prime
#print axioms character_orthogonality_prime
#print axioms rootFourier_inversion
#print axioms rootFourier_eq_zero_of_one_missing

end A387471
