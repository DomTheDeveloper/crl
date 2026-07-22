import BernsteinObstacle.SimplexAffineReproduction
import BernsteinObstacle.SmoothQuadraticSaturation
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Fitted simplicial quadratic contact

If a contact interface is a mesh face `lambda_j = 0`, the normal quadratic
profile `a * lambda_j^2` has nonnegative Bernstein coefficients in every fixed
degree at least two.  This file proves the simplicial second-moment identity
needed for that statement.
-/

/-- Multiplying the second partial derivative of a monomial by `X_j^2` restores
the original monomial with the falling-factorial weight. -/
theorem X_sq_mul_pderiv_twice_monomial
    {σ : Type*} [Fintype σ] (m : σ →₀ ℕ) (j : σ) :
    (MvPolynomial.X j : MvPolynomial σ ℝ) ^ 2 *
        MvPolynomial.pderiv j
          (MvPolynomial.pderiv j (MvPolynomial.monomial m 1)) =
      ((m j : ℝ) * ((m j : ℝ) - 1)) •
        MvPolynomial.monomial m 1 := by
  let M : MvPolynomial σ ℝ := MvPolynomial.monomial m 1
  have hfirst :
      (MvPolynomial.X j : MvPolynomial σ ℝ) *
          MvPolynomial.pderiv j M = (m j : ℝ) • M := by
    simpa [M, nsmul_eq_mul] using
      (MvPolynomial.X_mul_pderiv_monomial
        (R := ℝ) (i := j) (m := m) (r := (1 : ℝ)))
  have hder := congrArg (MvPolynomial.pderiv j) hfirst
  have hsecond :
      (MvPolynomial.X j : MvPolynomial σ ℝ) *
          MvPolynomial.pderiv j (MvPolynomial.pderiv j M) =
        ((m j : ℝ) - 1) • MvPolynomial.pderiv j M := by
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
      one_mul, map_smul] at hder
    module at hder ⊢
  calc
    (MvPolynomial.X j : MvPolynomial σ ℝ) ^ 2 *
          MvPolynomial.pderiv j (MvPolynomial.pderiv j
            (MvPolynomial.monomial m 1)) =
        (MvPolynomial.X j : MvPolynomial σ ℝ) *
          ((MvPolynomial.X j : MvPolynomial σ ℝ) *
            MvPolynomial.pderiv j (MvPolynomial.pderiv j M)) := by
      simp [M, pow_two, mul_assoc]
    _ = (MvPolynomial.X j : MvPolynomial σ ℝ) *
          (((m j : ℝ) - 1) • MvPolynomial.pderiv j M) := by rw [hsecond]
    _ = ((m j : ℝ) - 1) •
          ((MvPolynomial.X j : MvPolynomial σ ℝ) *
            MvPolynomial.pderiv j M) := by
      simp [smul_mul_assoc, mul_smul_comm]
    _ = ((m j : ℝ) - 1) • ((m j : ℝ) • M) := by rw [hfirst]
    _ = ((m j : ℝ) * ((m j : ℝ) - 1)) •
          MvPolynomial.monomial m 1 := by
      simp [M, smul_smul, mul_comm]

/-- Second partial derivative of a power of the barycentric-coordinate sum. -/
theorem pderiv_twice_sum_X_pow
    (d n : ℕ) (j : Fin (d + 1)) :
    MvPolynomial.pderiv j
        (MvPolynomial.pderiv j
          ((∑ i : Fin (d + 1),
              (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ)) ^ n)) =
      (((n : ℝ) * ((n : ℝ) - 1)) :
          MvPolynomial (Fin (d + 1)) ℝ) *
        (∑ i : Fin (d + 1),
          (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ)) ^ (n - 2) := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp [pderiv_sum_X_eq_one]
      | succ n =>
          rw [pderiv_sum_X_pow]
          simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
            pderiv_sum_X_eq_one, Nat.cast_succ]
          ring

/-- Twice differentiating the multinomial expansion weights each monomial by
`alpha_j (alpha_j - 1)`. -/
theorem X_sq_mul_pderiv_twice_simplexMultinomialExpansion
    (d n : ℕ) (j : Fin (d + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (d + 1)) ℝ) ^ 2 *
        MvPolynomial.pderiv j
          (MvPolynomial.pderiv j
            ((∑ i : Fin (d + 1),
                (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) ℝ)) ^ n)) =
      ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          (((α j : ℝ) * ((α j : ℝ) - 1)) •
            MvPolynomial.monomial (fullSimplexExponent d α) 1) := by
  rw [simplexMultinomialPolynomialExpansion]
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C_mul]
  calc
    (MvPolynomial.X j : MvPolynomial (Fin (d + 1)) ℝ) ^ 2 *
          (MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
            MvPolynomial.pderiv j
              (MvPolynomial.pderiv j
                (MvPolynomial.monomial (fullSimplexExponent d α) 1))) =
        MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          ((MvPolynomial.X j : MvPolynomial (Fin (d + 1)) ℝ) ^ 2 *
            MvPolynomial.pderiv j
              (MvPolynomial.pderiv j
                (MvPolynomial.monomial (fullSimplexExponent d α) 1))) := by ring
    _ = MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          ((((fullSimplexExponent d α j : ℕ) : ℝ) *
              (((fullSimplexExponent d α j : ℕ) : ℝ) - 1)) •
            MvPolynomial.monomial (fullSimplexExponent d α) 1) := by
      rw [X_sq_mul_pderiv_twice_monomial]
    _ = MvPolynomial.C (Nat.multinomial Finset.univ α : ℝ) *
          (((α j : ℝ) * ((α j : ℝ) - 1)) •
            MvPolynomial.monomial (fullSimplexExponent d α) 1) := by simp

/-- Unnormalized simplicial second factorial moment. -/
theorem simplexBasisNat_secondFactorialMoment_unnormalized
    (d n : ℕ) (j : Fin (d + 1)) (x : BarycentricPoint d) :
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
      (((α j * (α j - 1) : ℕ) : ℝ)) * simplexBasisNat d n α x) =
      quadraticMomentDenominator n * (x.1 j) ^ 2 := by
  have hpoly := X_sq_mul_pderiv_twice_simplexMultinomialExpansion d n j
  rw [pderiv_twice_sum_X_pow] at hpoly
  have heval := congrArg (MvPolynomial.eval x.1) hpoly
  simpa [simplexBasisNat, eval_fullSimplexMonomial, x.2.2,
    quadraticMomentDenominator, natCast_mul_pred,
    mul_assoc, mul_left_comm, mul_comm] using heval.symm

/-- Degree-`n` coefficients of the fitted normal profile `a * lambda_j^2`. -/
def simplexQuadraticNormalCoeff
    (n : ℕ) (j : Fin (d + 1)) (a : ℝ)
    (α : Fin (d + 1) → ℕ) : ℝ :=
  a * (((α j * (α j - 1) : ℕ) : ℝ) / quadraticMomentDenominator n)

/-- Fitted quadratic normal coefficients are nonnegative. -/
theorem simplexQuadraticNormalCoeff_nonneg
    (d n : ℕ) (j : Fin (d + 1)) (a : ℝ)
    (α : Fin (d + 1) → ℕ) (hn : 2 ≤ n) (ha : 0 ≤ a) :
    0 ≤ simplexQuadraticNormalCoeff n j a α := by
  unfold simplexQuadraticNormalCoeff
  exact mul_nonneg ha
    (div_nonneg (by positivity) (quadraticMomentDenominator_pos n hn).le)

/-- Exact simplicial representation of a fitted quadratic contact profile. -/
theorem simplexQuadraticNormal_exact
    (d n : ℕ) (j : Fin (d + 1)) (a : ℝ)
    (hn : 2 ≤ n) (x : BarycentricPoint d) :
    simplexFieldNat d n (simplexQuadraticNormalCoeff n j a) x =
      a * (x.1 j) ^ 2 := by
  have hD : quadraticMomentDenominator n ≠ 0 :=
    ne_of_gt (quadraticMomentDenominator_pos n hn)
  have hmoment := simplexBasisNat_secondFactorialMoment_unnormalized d n j x
  unfold simplexFieldNat simplexQuadraticNormalCoeff
  calc
    (∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (d + 1))) n,
        (a * (((α j * (α j - 1) : ℕ) : ℝ) /
          quadraticMomentDenominator n)) * simplexBasisNat d n α x) =
        (a / quadraticMomentDenominator n) *
          ∑ α ∈ Finset.piAntidiag
            (Finset.univ : Finset (Fin (d + 1))) n,
            (((α j * (α j - 1) : ℕ) : ℝ)) *
              simplexBasisNat d n α x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α hα
      ring
    _ = (a / quadraticMomentDenominator n) *
          (quadraticMomentDenominator n * (x.1 j) ^ 2) := by rw [hmoment]
    _ = a * (x.1 j) ^ 2 := by field_simp [hD]

/-- Complete local fitted-contact certificate: coefficient feasibility and exact
reproduction hold simultaneously. -/
theorem simplexQuadraticNormal_exact_and_nonnegative
    (d n : ℕ) (j : Fin (d + 1)) (a : ℝ)
    (hn : 2 ≤ n) (ha : 0 ≤ a) :
    (∀ α, 0 ≤ simplexQuadraticNormalCoeff n j a α) ∧
      (∀ x : BarycentricPoint d,
        simplexFieldNat d n (simplexQuadraticNormalCoeff n j a) x =
          a * (x.1 j) ^ 2) := by
  constructor
  · intro α
    exact simplexQuadraticNormalCoeff_nonneg d n j a α hn ha
  · intro x
    exact simplexQuadraticNormal_exact d n j a hn x

end

end BernsteinObstacle
