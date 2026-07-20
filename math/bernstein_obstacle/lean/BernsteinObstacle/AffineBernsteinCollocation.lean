import BernsteinObstacle.AffineBernsteinBasis
import BernsteinObstacle.NodalUnisolvence
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Invertibility of the full Bernstein lattice-collocation operator

Bernstein coefficients determine a unique polynomial through the verified
Bernstein basis, and complete simplex-lattice values determine a unique
polynomial through the verified nodal equivalence.  Composing these two linear
equivalences gives the full Bernstein collocation operator as an explicit
linear equivalence.
-/

/-- Coordinate equivalence associated with the complete affine Bernstein
basis. -/
def affineBernsteinCoefficientEquiv (d n : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin d) ℝ n ≃ₗ[ℝ]
      (MultiIndex d n → ℝ) :=
  (affineBernsteinBasis d n).equivFun

/-- The full matrix-free Bernstein coefficient-to-lattice-value collocation
operator.  Its type as a linear equivalence certifies invertibility. -/
def affineBernsteinCollocationEquiv (d n : ℕ) :
    (MultiIndex d n → ℝ) ≃ₗ[ℝ] (MultiIndex d n → ℝ) :=
  (affineBernsteinCoefficientEquiv d n).symm.trans
    (affineNodalEvaluationEquiv d n)

/-- Applying the collocation equivalence means reconstructing the Bernstein
polynomial and evaluating it on the complete simplex lattice. -/
theorem affineBernsteinCollocationEquiv_apply (d n : ℕ)
    (c : MultiIndex d n → ℝ) (β : MultiIndex d n) :
    affineBernsteinCollocationEquiv d n c β =
      MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ))
        (((affineBernsteinCoefficientEquiv d n).symm c).1) := by
  change affineNodalEvaluationEquiv d n
      ((affineBernsteinCoefficientEquiv d n).symm c) β = _
  exact affineNodalEvaluationEquiv_apply d n
    ((affineBernsteinCoefficientEquiv d n).symm c) β

/-- The full Bernstein collocation operator is injective. -/
theorem affineBernsteinCollocation_injective (d n : ℕ) :
    Function.Injective (affineBernsteinCollocationEquiv d n) :=
  (affineBernsteinCollocationEquiv d n).injective

/-- The full Bernstein collocation operator is surjective. -/
theorem affineBernsteinCollocation_surjective (d n : ℕ) :
    Function.Surjective (affineBernsteinCollocationEquiv d n) :=
  (affineBernsteinCollocationEquiv d n).surjective

/-- Every assignment of complete simplex-lattice values has a unique vector of
Bernstein coefficients. -/
theorem existsUnique_bernsteinCoefficients_with_latticeValues (d n : ℕ)
    (values : MultiIndex d n → ℝ) :
    ∃! c : MultiIndex d n → ℝ,
      affineBernsteinCollocationEquiv d n c = values := by
  refine ⟨(affineBernsteinCollocationEquiv d n).symm values, ?_, ?_⟩
  · exact (affineBernsteinCollocationEquiv d n).apply_symm_apply values
  · intro c hc
    exact (affineBernsteinCollocationEquiv d n).injective
      (hc.trans
        ((affineBernsteinCollocationEquiv d n).apply_symm_apply values).symm)

end

end BernsteinObstacle
