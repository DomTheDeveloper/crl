import BernsteinObstacle.AffineBernsteinOrder
import BernsteinObstacle.PolynomialDimension
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# The affine Bernstein family is a basis of `P_n`

Coefficient extraction at the certified lowest monomials gives a triangular
induction on `affineBernsteinRank`.  The nonzero multinomial diagonal proves
linear independence.  The already verified dimension equality then upgrades
the family to a basis of the complete total-degree polynomial space.
-/

/-- The affine Bernstein polynomial family is linearly independent. -/
theorem affineBernsteinPolynomial_linearIndependent (d n : ℕ) :
    LinearIndependent ℝ (affineBernsteinPolynomial d n) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h
  have hzero :
      (∑ β : MultiIndex d n,
        (f β - g β) • affineBernsteinPolynomial d n β) = 0 := by
    calc
      (∑ β : MultiIndex d n,
          (f β - g β) • affineBernsteinPolynomial d n β) =
          (∑ β : MultiIndex d n,
            f β • affineBernsteinPolynomial d n β) -
          ∑ β : MultiIndex d n,
            g β • affineBernsteinPolynomial d n β := by
              simp_rw [sub_smul]
              rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr h
  have hrank : ∀ k : ℕ, ∀ α : MultiIndex d n,
      affineBernsteinRank d n α = k → f α = g α := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro α hα
        have hcoeff := congrArg
          (MvPolynomial.coeff (affineBernsteinExponent d n α)) hzero
        simp only [map_sum, MvPolynomial.coeff_smul,
          MvPolynomial.coeff_zero] at hcoeff
        have hsum :
            (∑ β : MultiIndex d n,
              (f β - g β) *
                MvPolynomial.coeff (affineBernsteinExponent d n α)
                  (affineBernsteinPolynomial d n β)) =
              (f α - g α) * affineBernsteinCoefficient d n α := by
          classical
          rw [Finset.sum_eq_single α]
          · rw [coeff_affineBernsteinPolynomial_at_own_exponent]
          · intro β hβ hne
            by_cases hlt : affineBernsteinRank d n β < k
            · have hfg : f β = g β :=
                ih (affineBernsteinRank d n β) hlt β rfl
              simp [hfg]
            · have hk_le : k ≤ affineBernsteinRank d n β :=
                Nat.le_of_not_gt hlt
              by_cases heq : affineBernsteinRank d n β = k
              · have hrank_eq :
                    affineBernsteinRank d n α =
                      affineBernsteinRank d n β := by omega
                rw [coeff_affineBernsteinPolynomial_eq_zero_of_rank_eq_of_ne
                  d n α β hrank_eq hne]
                simp
              · have hk_lt : k < affineBernsteinRank d n β := by omega
                have hrank_lt :
                    affineBernsteinRank d n α <
                      affineBernsteinRank d n β := by omega
                rw [coeff_affineBernsteinPolynomial_eq_zero_of_rank_lt
                  d n α β hrank_lt]
                simp
          · intro hnot
            exact (hnot (Finset.mem_univ α)).elim
        rw [hsum] at hcoeff
        have hdiag := affineBernsteinCoefficient_ne_zero d n α
        have hdiff : f α - g α = 0 :=
          (mul_eq_zero.mp hcoeff).resolve_right hdiag
        exact sub_eq_zero.mp hdiff
  intro α
  exact hrank (affineBernsteinRank d n α) α rfl

/-- The subspace-valued affine Bernstein family is linearly independent in
`P_n`. -/
theorem affineBernsteinVector_linearIndependent (d n : ℕ) :
    LinearIndependent ℝ (affineBernsteinVector d n) := by
  apply LinearIndependent.of_comp
    (MvPolynomial.restrictTotalDegree (Fin d) ℝ n).subtype
  simpa [Function.comp_def, affineBernsteinVector] using
    affineBernsteinPolynomial_linearIndependent d n

/-- The complete affine simplicial Bernstein family is a basis of `P_n`. -/
def affineBernsteinBasis (d n : ℕ) :
    Module.Basis (MultiIndex d n) ℝ
      (MvPolynomial.restrictTotalDegree (Fin d) ℝ n) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (affineBernsteinVector d n)
    (affineBernsteinVector_linearIndependent d n)
    (finrank_restrictTotalDegree_eq_card_multiIndex d n).symm

@[simp]
theorem affineBernsteinBasis_apply (d n : ℕ) (α : MultiIndex d n) :
    affineBernsteinBasis d n α = affineBernsteinVector d n α := by
  change basisOfLinearIndependentOfCardEqFinrank'
      (affineBernsteinVector d n)
      (affineBernsteinVector_linearIndependent d n)
      (finrank_restrictTotalDegree_eq_card_multiIndex d n).symm α = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']

/-- The affine Bernstein family spans every total-degree-`n` polynomial. -/
theorem span_affineBernsteinVector_eq_top (d n : ℕ) :
    Submodule.span ℝ (Set.range (affineBernsteinVector d n)) = ⊤ := by
  exact LinearIndependent.span_eq_top_of_card_eq_finrank'
    (affineBernsteinVector_linearIndependent d n)
    (finrank_restrictTotalDegree_eq_card_multiIndex d n).symm

/-- Every polynomial in `P_n` has a unique Bernstein expansion. -/
theorem affineBernsteinBasis_sum_repr (d n : ℕ)
    (p : MvPolynomial.restrictTotalDegree (Fin d) ℝ n) :
    ∑ α, (((affineBernsteinBasis d n).repr p α : ℝ)) •
      affineBernsteinVector d n α = p := by
  simpa [affineBernsteinBasis_apply] using
    (affineBernsteinBasis d n).sum_repr p

end

end BernsteinObstacle
