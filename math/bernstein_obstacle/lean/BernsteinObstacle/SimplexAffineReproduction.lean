import BernsteinObstacle.SimplexRecovery
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Affine reproduction of positive simplex Bernstein sampling

This file develops the first-moment identity behind the positive recovery
operator.  The proof starts from the multinomial theorem in the multivariate
polynomial ring and differentiates formally in one barycentric coordinate.
-/

/-- Convert a full finite exponent function into its finitely supported form. -/
def fullSimplexExponent (d : ℕ) (α : Fin (d + 1) → ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm α

@[simp]
theorem fullSimplexExponent_apply (d : ℕ) (α : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) :
    fullSimplexExponent d α i = α i := by
  simp [fullSimplexExponent]

/-- A product of all barycentric-coordinate variables is the corresponding
monic multivariate monomial. -/
theorem prod_X_pow_eq_fullSimplexMonomial (d : ℕ)
    (α : Fin (d + 1) → ℕ) :
    (∏ i : Fin (d + 1),
      (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ) ^ α i) =
      MvPolynomial.monomial (fullSimplexExponent d α) 1 := by
  calc
    (∏ i : Fin (d + 1),
      (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ) ^ α i) =
        (fullSimplexExponent d α).prod
          (fun i e => (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ) ^ e) :=
      (Finsupp.prod_pow (fullSimplexExponent d α)
        (fun i => (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ))).symm
    _ = MvPolynomial.monomial (fullSimplexExponent d α) 1 :=
      (MvPolynomial.monic_monomial_eq (fullSimplexExponent d α)).symm

/-- Evaluation of the full monomial is the expected product of coordinate
powers. -/
theorem eval_fullSimplexMonomial (d : ℕ)
    (α : Fin (d + 1) → ℕ) (x : Fin (d + 1) → ℝ) :
    MvPolynomial.eval x
        (MvPolynomial.monomial (fullSimplexExponent d α) 1) =
      ∏ i : Fin (d + 1), x i ^ α i := by
  rw [← prod_X_pow_eq_fullSimplexMonomial]
  simp

/-- The multinomial theorem, expressed as a sum of actual multivariate
monomials in all barycentric variables. -/
theorem simplexMultinomialPolynomialExpansion (d n : ℕ) :
    ((∑ i : Fin (d + 1),
        (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ)) ^ n) =
      ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          MvPolynomial.monomial (fullSimplexExponent d α) 1 := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_congr rfl
  intro α hα
  rw [prod_X_pow_eq_fullSimplexMonomial]
  simp

/-- The partial derivative of the sum of all barycentric variables is one. -/
theorem pderiv_sum_X_eq_one (d : ℕ) (j : Fin (d + 1)) :
    MvPolynomial.pderiv j
        (∑ i : Fin (d + 1),
          (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ)) = 1 := by
  simp

/-- Differentiating the multinomial expansion and multiplying by `X_j`
weights every monomial by its `j`-th exponent. -/
theorem X_mul_pderiv_simplexMultinomialExpansion
    (d n : ℕ) (j : Fin (d + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (d + 1)) ℝ) *
        MvPolynomial.pderiv j
          ((∑ i : Fin (d + 1),
              (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ)) ^ n) =
      ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          ((α j) • MvPolynomial.monomial (fullSimplexExponent d α) 1) := by
  rw [simplexMultinomialPolynomialExpansion]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [MvPolynomial.pderiv_C_mul]
  calc
    (MvPolynomial.X j : MvPolynomial (Fin (d + 1)) ℝ) *
          (MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
            MvPolynomial.pderiv j
              (MvPolynomial.monomial (fullSimplexExponent d α) 1)) =
        MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          ((MvPolynomial.X j : MvPolynomial (Fin (d + 1)) ℝ) *
            MvPolynomial.pderiv j
              (MvPolynomial.monomial (fullSimplexExponent d α) 1)) := by ring
    _ = MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          ((fullSimplexExponent d α j) •
            MvPolynomial.monomial (fullSimplexExponent d α) 1) := by
      rw [MvPolynomial.X_mul_pderiv_monomial]
    _ = MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          ((α j) • MvPolynomial.monomial (fullSimplexExponent d α) 1) := by
      simp

end

end BernsteinObstacle
