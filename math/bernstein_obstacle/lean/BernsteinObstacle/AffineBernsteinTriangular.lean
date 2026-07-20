import BernsteinObstacle.AffineBernsteinPolynomial
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Triangular structure of the affine Bernstein family

The first `d` components of a simplex multi-index define the lowest affine
monomial appearing in the corresponding Bernstein polynomial.  Its coefficient
is the nonzero multinomial constant.  These facts are the triangular input for
proving that the Bernstein family is a basis of `P_n`.
-/

/-- The exponent vector of the first `d` barycentric coordinates. -/
def affineBernsteinExponent (d n : ℕ) (α : MultiIndex d n) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α.1 i.castSucc : ℕ))

@[simp]
theorem affineBernsteinExponent_apply (d n : ℕ) (α : MultiIndex d n)
    (i : Fin d) :
    affineBernsteinExponent d n α i = (α.1 i.castSucc : ℕ) := by
  simp [affineBernsteinExponent]

/-- The total exponent of the independent affine variables is the sum of the
first `d` barycentric components. -/
theorem affineBernsteinExponent_sum (d n : ℕ) (α : MultiIndex d n) :
    (affineBernsteinExponent d n α).sum (fun _ e => e) =
      ∑ i : Fin d, (α.1 i.castSucc : ℕ) := by
  rw [Finsupp.sum_fintype (affineBernsteinExponent d n α)
    (fun _ e => e) (fun _ => rfl)]
  simp

/-- The multinomial coefficient multiplying a Bernstein monomial is positive. -/
theorem affineBernsteinCoefficient_pos (d n : ℕ) (α : MultiIndex d n) :
    0 < affineBernsteinCoefficient d n α := by
  unfold affineBernsteinCoefficient
  positivity

/-- In particular, the multinomial coefficient is nonzero. -/
theorem affineBernsteinCoefficient_ne_zero (d n : ℕ) (α : MultiIndex d n) :
    affineBernsteinCoefficient d n α ≠ 0 :=
  ne_of_gt (affineBernsteinCoefficient_pos d n α)

/-- The product of the independent coordinate powers is the monic monomial
with exponent `affineBernsteinExponent`. -/
theorem prod_X_pow_eq_affineBernsteinMonomial (d n : ℕ)
    (α : MultiIndex d n) :
    (∏ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ (α.1 i.castSucc : ℕ)) =
      MvPolynomial.monomial (affineBernsteinExponent d n α) 1 := by
  calc
    (∏ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ (α.1 i.castSucc : ℕ)) =
        ∏ i : Fin d,
          (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^
            (affineBernsteinExponent d n α i) := by simp
    _ = (affineBernsteinExponent d n α).prod
          (fun i e => (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ e) :=
      (Finsupp.prod_pow (affineBernsteinExponent d n α)
        (fun i => (MvPolynomial.X i : MvPolynomial (Fin d) ℝ))).symm
    _ = MvPolynomial.monomial (affineBernsteinExponent d n α) 1 :=
      (MvPolynomial.monic_monomial_eq (affineBernsteinExponent d n α)).symm

/-- Factor a Bernstein polynomial into its lowest monomial and a power of the
remaining affine barycentric coordinate. -/
theorem affineBernsteinPolynomial_factor (d n : ℕ)
    (α : MultiIndex d n) :
    affineBernsteinPolynomial d n α =
      MvPolynomial.C (affineBernsteinCoefficient d n α) *
        (MvPolynomial.monomial (affineBernsteinExponent d n α) 1 *
          (affineBarycentric d (Fin.last d)) ^
            (α.1 (Fin.last d) : ℕ)) := by
  unfold affineBernsteinPolynomial
  rw [Fin.prod_univ_castSucc]
  simp only [affineBarycentric, Fin.snoc_castSucc, Fin.snoc_last]
  rw [prod_X_pow_eq_affineBernsteinMonomial]

end

end BernsteinObstacle
