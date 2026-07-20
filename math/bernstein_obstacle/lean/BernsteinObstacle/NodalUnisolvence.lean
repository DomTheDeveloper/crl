import BernsteinObstacle.Unisolvence
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Nodal evaluation equivalence

The coordinate functional of the cardinal basis is exactly evaluation at the
corresponding degree-`n` simplex lattice point.  Consequently nodal evaluation
is a linear equivalence between `P_n` and arbitrary lattice data.
-/

/-- Evaluation at one degree-`n` simplex lattice point, restricted to `P_n`. -/
def affineNodeFunctional (d n : ℕ) (β : MultiIndex d n) :
    MvPolynomial.restrictTotalDegree (Fin d) ℝ n →ₗ[ℝ] ℝ where
  toFun := fun p =>
    MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ)) p.1
  map_add' := by
    intro p q
    simp
  map_smul' := by
    intro c p
    simp

/-- Evaluation at node `β` is the `β`th coordinate functional of the cardinal
basis. -/
theorem affineNodeFunctional_eq_cardinalBasis_coord (d n : ℕ)
    (β : MultiIndex d n) :
    affineNodeFunctional d n β = (affineLatticeCardinalBasis d n).coord β := by
  apply (affineLatticeCardinalBasis d n).ext
  intro α
  rw [affineLatticeCardinalBasis_apply]
  change MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ))
      (affineLatticeCardinalPolynomial d n α) =
    (affineLatticeCardinalBasis d n).repr
      (affineLatticeCardinalVector d n α) β
  rw [eval_affineLatticeCardinalPolynomial_eq_ite]
  rw [← affineLatticeCardinalBasis_apply d n α]
  exact ((affineLatticeCardinalBasis d n).repr_self_apply α β).symm

/-- Nodal evaluation on the complete simplex lattice is a linear equivalence. -/
def affineNodalEvaluationEquiv (d n : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin d) ℝ n ≃ₗ[ℝ]
      (MultiIndex d n → ℝ) :=
  (affineLatticeCardinalBasis d n).equivFun

/-- The abstract basis-coordinate equivalence is literally nodal evaluation. -/
theorem affineNodalEvaluationEquiv_apply (d n : ℕ)
    (p : MvPolynomial.restrictTotalDegree (Fin d) ℝ n)
    (β : MultiIndex d n) :
    affineNodalEvaluationEquiv d n p β =
      MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ)) p.1 := by
  change (affineLatticeCardinalBasis d n).coord β p = _
  rw [← affineNodeFunctional_eq_cardinalBasis_coord d n β]
  rfl

/-- Two degree-bounded polynomials agreeing on the complete degree-`n` simplex
lattice are equal. -/
theorem polynomial_eq_of_eq_on_simplex_lattice (d n : ℕ)
    {p q : MvPolynomial.restrictTotalDegree (Fin d) ℝ n}
    (h : ∀ β : MultiIndex d n,
      MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ)) p.1 =
        MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ)) q.1) :
    p = q := by
  apply (affineNodalEvaluationEquiv d n).injective
  funext β
  simpa [affineNodalEvaluationEquiv_apply] using h β

/-- Every assignment of values on the degree-`n` simplex lattice has a unique
interpolating polynomial of total degree at most `n`. -/
theorem existsUnique_polynomial_with_simplex_lattice_values (d n : ℕ)
    (values : MultiIndex d n → ℝ) :
    ∃! p : MvPolynomial.restrictTotalDegree (Fin d) ℝ n,
      ∀ β : MultiIndex d n,
        MvPolynomial.eval (fun j : Fin d => (β.1 j.castSucc : ℝ)) p.1 = values β := by
  let p := (affineNodalEvaluationEquiv d n).symm values
  refine ⟨p, ?_, ?_⟩
  · intro β
    have h := congrFun
      ((affineNodalEvaluationEquiv d n).apply_symm_apply values) β
    simpa [p, affineNodalEvaluationEquiv_apply] using h
  · intro q hq
    apply (affineNodalEvaluationEquiv d n).injective
    funext β
    have hp := congrFun
      ((affineNodalEvaluationEquiv d n).apply_symm_apply values) β
    rw [affineNodalEvaluationEquiv_apply, affineNodalEvaluationEquiv_apply]
    rw [hq β]
    simpa [p, affineNodalEvaluationEquiv_apply] using hp.symm

end

end BernsteinObstacle
