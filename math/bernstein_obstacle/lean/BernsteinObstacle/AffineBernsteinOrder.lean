import BernsteinObstacle.AffineBernsteinTriangular
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Rank separation for affine Bernstein exponents

The total degree of the lowest affine monomial orders the Bernstein family.
A source polynomial of larger rank cannot contribute to a smaller-rank target
coefficient; at equal rank, domination forces equality of the multi-indices.
-/

/-- Total degree of the lowest affine monomial of a Bernstein polynomial. -/
def affineBernsteinRank (d n : ℕ) (α : MultiIndex d n) : ℕ :=
  ∑ i : Fin d, (α.1 i.castSucc : ℕ)

/-- Rank is the sum of the affine exponent vector. -/
theorem affineBernsteinRank_eq_exponent_sum (d n : ℕ)
    (α : MultiIndex d n) :
    affineBernsteinRank d n α =
      (affineBernsteinExponent d n α).sum (fun _ e => e) := by
  exact (affineBernsteinExponent_sum d n α).symm

/-- The first `d` components determine a degree-`n` simplex multi-index. -/
theorem affineBernsteinExponent_injective (d n : ℕ) :
    Function.Injective (affineBernsteinExponent d n) := by
  intro α β h
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply Fin.ext
    have hfirst :
        (∑ j : Fin d, (α.1 j.castSucc : ℕ)) =
          ∑ j : Fin d, (β.1 j.castSucc : ℕ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjh := congrArg (fun s : Fin d →₀ ℕ => s j) h
      simpa using hjh
    have ha := α.2
    have hb := β.2
    rw [Fin.sum_univ_castSucc] at ha hb
    omega
  · apply Fin.ext
    have hjh := congrArg (fun s : Fin d →₀ ℕ => s j) h
    simpa using hjh

/-- Pointwise domination of lowest exponents implies rank domination. -/
theorem affineBernsteinRank_le_of_exponent_le (d n : ℕ)
    {α β : MultiIndex d n}
    (h : affineBernsteinExponent d n α ≤
      affineBernsteinExponent d n β) :
    affineBernsteinRank d n α ≤ affineBernsteinRank d n β := by
  unfold affineBernsteinRank
  apply Finset.sum_le_sum
  intro i hi
  simpa using h i

/-- At equal rank, pointwise domination of affine exponents is equality. -/
theorem affineBernsteinExponent_eq_of_le_of_rank_eq (d n : ℕ)
    {α β : MultiIndex d n}
    (hle : affineBernsteinExponent d n α ≤
      affineBernsteinExponent d n β)
    (hrank : affineBernsteinRank d n α =
      affineBernsteinRank d n β) :
    affineBernsteinExponent d n α =
      affineBernsteinExponent d n β := by
  apply Finsupp.ext
  intro i
  have hi := hle i
  by_contra hne
  have hlt : affineBernsteinExponent d n α i <
      affineBernsteinExponent d n β i :=
    Nat.lt_of_le_of_ne hi hne
  have hsumlt : affineBernsteinRank d n α <
      affineBernsteinRank d n β := by
    unfold affineBernsteinRank
    apply Finset.sum_lt_sum
    · intro j hj
      simpa using hle j
    · exact ⟨i, Finset.mem_univ i, by simpa using hlt⟩
  omega

/-- A larger-rank source exponent cannot lie below a smaller-rank target. -/
theorem affineBernsteinExponent_not_le_of_rank_lt (d n : ℕ)
    {α β : MultiIndex d n}
    (h : affineBernsteinRank d n α < affineBernsteinRank d n β) :
    ¬ affineBernsteinExponent d n β ≤
      affineBernsteinExponent d n α := by
  intro hle
  have hrank := affineBernsteinRank_le_of_exponent_le d n hle
  omega

/-- Distinct multi-indices of equal rank cannot dominate one another. -/
theorem affineBernsteinExponent_not_le_of_rank_eq_of_ne (d n : ℕ)
    {α β : MultiIndex d n}
    (hrank : affineBernsteinRank d n α = affineBernsteinRank d n β)
    (hne : β ≠ α) :
    ¬ affineBernsteinExponent d n β ≤
      affineBernsteinExponent d n α := by
  intro hle
  apply hne
  apply affineBernsteinExponent_injective d n
  exact affineBernsteinExponent_eq_of_le_of_rank_eq d n hle hrank.symm

/-- Higher-rank Bernstein polynomials have zero coefficient at a lower-rank
lowest exponent. -/
theorem coeff_affineBernsteinPolynomial_eq_zero_of_rank_lt (d n : ℕ)
    (α β : MultiIndex d n)
    (h : affineBernsteinRank d n α < affineBernsteinRank d n β) :
    MvPolynomial.coeff (affineBernsteinExponent d n α)
      (affineBernsteinPolynomial d n β) = 0 :=
  coeff_affineBernsteinPolynomial_eq_zero_of_not_le d n α β
    (affineBernsteinExponent_not_le_of_rank_lt d n h)

/-- At equal rank, every distinct Bernstein polynomial has zero coefficient at
the target's lowest exponent. -/
theorem coeff_affineBernsteinPolynomial_eq_zero_of_rank_eq_of_ne (d n : ℕ)
    (α β : MultiIndex d n)
    (hrank : affineBernsteinRank d n α = affineBernsteinRank d n β)
    (hne : β ≠ α) :
    MvPolynomial.coeff (affineBernsteinExponent d n α)
      (affineBernsteinPolynomial d n β) = 0 :=
  coeff_affineBernsteinPolynomial_eq_zero_of_not_le d n α β
    (affineBernsteinExponent_not_le_of_rank_eq_of_ne d n hrank hne)

end

end BernsteinObstacle
