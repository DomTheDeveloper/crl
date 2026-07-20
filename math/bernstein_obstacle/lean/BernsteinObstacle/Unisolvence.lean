import BernsteinObstacle.AffineLatticePolynomial
import BernsteinObstacle.PolynomialDimension
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# All-degree simplex lattice unisolvence

The affine cardinal polynomials lie in the degree-bounded polynomial space,
are linearly independent, and are indexed by exactly as many lattice points as
the dimension of that space.  Therefore they form a basis of `P_n`.
-/

/-- An affine cardinal polynomial regarded as an element of the total-degree
polynomial subspace. -/
def affineLatticeCardinalVector (d n : ℕ) (α : MultiIndex d n) :
    MvPolynomial.restrictTotalDegree (Fin d) ℝ n :=
  ⟨affineLatticeCardinalPolynomial d n α,
    affineLatticeCardinalPolynomial_mem_restrictTotalDegree d n α⟩

/-- The subspace-valued cardinal family is linearly independent. -/
theorem affineLatticeCardinalVector_linearIndependent (d n : ℕ) :
    LinearIndependent ℝ (affineLatticeCardinalVector d n) := by
  apply LinearIndependent.of_comp
    (MvPolynomial.restrictTotalDegree (Fin d) ℝ n).subtype
  simpa [Function.comp_def, affineLatticeCardinalVector] using
    affineLatticeCardinalPolynomial_linearIndependent d n

/-- The complete affine cardinal family is a basis of all polynomials in `d`
variables having total degree at most `n`. -/
def affineLatticeCardinalBasis (d n : ℕ) :
    Module.Basis (MultiIndex d n) ℝ
      (MvPolynomial.restrictTotalDegree (Fin d) ℝ n) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (affineLatticeCardinalVector d n)
    (affineLatticeCardinalVector_linearIndependent d n)
    (finrank_restrictTotalDegree_eq_card_multiIndex d n).symm

@[simp]
theorem affineLatticeCardinalBasis_apply (d n : ℕ) (α : MultiIndex d n) :
    affineLatticeCardinalBasis d n α = affineLatticeCardinalVector d n α := by
  change basisOfLinearIndependentOfCardEqFinrank'
      (affineLatticeCardinalVector d n)
      (affineLatticeCardinalVector_linearIndependent d n)
      (finrank_restrictTotalDegree_eq_card_multiIndex d n).symm α = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']

/-- The affine cardinal polynomials span the entire degree-bounded polynomial
space. -/
theorem span_affineLatticeCardinalVector_eq_top (d n : ℕ) :
    Submodule.span ℝ (Set.range (affineLatticeCardinalVector d n)) = ⊤ := by
  simpa [affineLatticeCardinalBasis_apply] using
    (affineLatticeCardinalBasis d n).span_eq

/-- Every degree-bounded polynomial has a unique expansion in the cardinal
polynomial basis. -/
theorem affineLatticeCardinalBasis_sum_repr (d n : ℕ)
    (p : MvPolynomial.restrictTotalDegree (Fin d) ℝ n) :
    ∑ α, (((affineLatticeCardinalBasis d n).repr p α : ℝ)) •
      affineLatticeCardinalVector d n α = p := by
  simpa [affineLatticeCardinalBasis_apply] using
    (affineLatticeCardinalBasis d n).sum_repr p

end

end BernsteinObstacle
