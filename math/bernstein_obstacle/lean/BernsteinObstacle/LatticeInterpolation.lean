import BernsteinObstacle.LatticeCardinal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open scoped BigOperators Matrix

namespace BernsteinObstacle

noncomputable section

/-!
# Exact interpolation on the barycentric lattice

The normalized falling-factorial cardinal values form the identity collocation
matrix on the complete degree-`n` barycentric lattice.  Consequently every set
of nodal values has an explicit cardinal interpolant whose values at all lattice
nodes are exactly the prescribed data, and the resulting nodal evaluation map
is injective.

This closes the finite collocation-matrix part of general lattice unisolvence.
The remaining polynomial-space step is to package the cardinal expressions as
multivariate polynomials of total degree at most `n` and identify their span with
`P_n`.
-/

section LatticeInterpolation

/-- The cardinal collocation matrix on the degree-`n` lattice of a `d`-simplex. -/
def latticeCardinalMatrix (d n : ℕ) :
    Matrix (MultiIndex d n) (MultiIndex d n) ℝ :=
  fun α β => latticeCardinalValue
    (fun i => (α.1 i : ℕ)) (fun i => (β.1 i : ℕ))

/-- Each entry of the cardinal collocation matrix is a Kronecker delta. -/
theorem latticeCardinalMatrix_apply (d n : ℕ)
    (α β : MultiIndex d n) :
    latticeCardinalMatrix d n α β = if α = β then 1 else 0 := by
  have hsum :
      (∑ i, (α.1 i : ℕ)) = ∑ i, (β.1 i : ℕ) := by
    rw [α.2, β.2]
  by_cases hαβ : α = β
  · subst β
    simp [latticeCardinalMatrix]
  · have hfun :
        (fun i => (α.1 i : ℕ)) ≠ (fun i => (β.1 i : ℕ)) := by
      intro h
      apply hαβ
      apply Subtype.ext
      funext i
      exact Fin.ext (congrFun h i)
    rw [latticeCardinalMatrix, latticeCardinalValue_eq_ite _ _ hsum]
    simp [hαβ, hfun]

/-- The cardinal collocation matrix is exactly the identity matrix. -/
theorem latticeCardinalMatrix_eq_one (d n : ℕ) :
    latticeCardinalMatrix d n = 1 := by
  classical
  ext α β
  rw [latticeCardinalMatrix_apply]
  simp [Matrix.one_apply]

/-- In particular, the cardinal collocation matrix has determinant one. -/
theorem latticeCardinalMatrix_det (d n : ℕ) :
    (latticeCardinalMatrix d n).det = 1 := by
  rw [latticeCardinalMatrix_eq_one, Matrix.det_one]

/-- Cardinal interpolation of nodal data, evaluated at a lattice node. -/
def latticeCardinalInterpolantValue (d n : ℕ)
    (c : MultiIndex d n → ℝ) (β : MultiIndex d n) : ℝ :=
  ∑ α, c α * latticeCardinalMatrix d n α β

/-- Cardinal interpolation reproduces every prescribed nodal value exactly. -/
theorem latticeCardinalInterpolantValue_eq (d n : ℕ)
    (c : MultiIndex d n → ℝ) (β : MultiIndex d n) :
    latticeCardinalInterpolantValue d n c β = c β := by
  classical
  simp [latticeCardinalInterpolantValue, latticeCardinalMatrix_apply]

/-- The complete nodal evaluation operator defined by the cardinal family. -/
def latticeCardinalEvaluation (d n : ℕ) :
    (MultiIndex d n → ℝ) → (MultiIndex d n → ℝ) :=
  fun c β => latticeCardinalInterpolantValue d n c β

/-- The cardinal nodal evaluation operator is the identity. -/
theorem latticeCardinalEvaluation_eq_id (d n : ℕ) :
    latticeCardinalEvaluation d n = id := by
  funext c β
  exact latticeCardinalInterpolantValue_eq d n c β

/-- Therefore cardinal coefficients are uniquely determined by all lattice-node
values. -/
theorem latticeCardinalEvaluation_injective (d n : ℕ) :
    Function.Injective (latticeCardinalEvaluation d n) := by
  rw [latticeCardinalEvaluation_eq_id]
  exact Function.injective_id

end LatticeInterpolation

end

end BernsteinObstacle
