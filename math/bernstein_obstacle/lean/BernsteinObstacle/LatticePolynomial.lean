import BernsteinObstacle.LatticeInterpolation
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Polynomial realization of the barycentric lattice cardinal family

The finite cardinal-value layer is now packaged as actual multivariate
polynomials.  Each coordinate factor is the falling-factorial polynomial
`descPochhammer`, embedded into the corresponding multivariate variable and
normalized by the factorial of the cardinal index.  Evaluation at an integer
lattice point recovers the exact cardinal values from `LatticeCardinal.lean`.
-/

section LatticePolynomial

variable {ι : Type*} [Fintype ι]

/-- The falling-factorial polynomial in one selected multivariate coordinate. -/
def coordinateDescPochhammer (i : ι) (a : ℕ) : MvPolynomial ι ℝ :=
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) (descPochhammer ℝ a)

/-- Evaluating the embedded coordinate falling-factorial polynomial at an
integer point gives the corresponding natural falling factorial. -/
theorem eval_coordinateDescPochhammer (i : ι) (a : ℕ) (β : ι → ℕ) :
    MvPolynomial.eval (fun j => (β j : ℝ))
      (coordinateDescPochhammer i a) = (β i).descFactorial a := by
  unfold coordinateDescPochhammer MvPolynomial.eval
  rw [Polynomial.hom_eval₂]
  simp [descPochhammer_eval_eq_descFactorial]

/-- One normalized cardinal factor, now as an actual multivariate polynomial. -/
def coordinateLatticeCardinalPolynomial (i : ι) (a : ℕ) :
    MvPolynomial ι ℝ :=
  MvPolynomial.C ((a.factorial : ℝ)⁻¹) * coordinateDescPochhammer i a

/-- Evaluation of one normalized coordinate factor agrees with
`latticeFactor`. -/
theorem eval_coordinateLatticeCardinalPolynomial
    (i : ι) (a : ℕ) (β : ι → ℕ) :
    MvPolynomial.eval (fun j => (β j : ℝ))
      (coordinateLatticeCardinalPolynomial i a) = latticeFactor a (β i) := by
  simp [coordinateLatticeCardinalPolynomial, eval_coordinateDescPochhammer,
    latticeFactor, div_eq_mul_inv, mul_comm]

/-- The complete cardinal polynomial attached to a degree-`n` simplex
multi-index.  The variables are the scaled barycentric coordinates `n * λᵢ`. -/
def latticeCardinalPolynomial (d n : ℕ) (α : MultiIndex d n) :
    MvPolynomial (Fin (d + 1)) ℝ :=
  ∏ i, coordinateLatticeCardinalPolynomial i (α.1 i)

/-- Evaluation of the cardinal polynomial at an integer lattice index agrees
with the previously verified cardinal-value product. -/
theorem eval_latticeCardinalPolynomial (d n : ℕ)
    (α β : MultiIndex d n) :
    MvPolynomial.eval (fun i => ((β.1 i : ℕ) : ℝ))
      (latticeCardinalPolynomial d n α) =
        latticeCardinalValue
          (fun i => (α.1 i : ℕ)) (fun i => (β.1 i : ℕ)) := by
  simp [latticeCardinalPolynomial, latticeCardinalValue,
    eval_coordinateLatticeCardinalPolynomial]

/-- The polynomial cardinal family has the exact Kronecker-delta values on the
complete degree-`n` barycentric lattice. -/
theorem eval_latticeCardinalPolynomial_eq_ite (d n : ℕ)
    (α β : MultiIndex d n) :
    MvPolynomial.eval (fun i => ((β.1 i : ℕ) : ℝ))
      (latticeCardinalPolynomial d n α) = if α = β then 1 else 0 := by
  rw [eval_latticeCardinalPolynomial]
  exact latticeCardinalMatrix_apply d n α β

end LatticePolynomial

end

end BernsteinObstacle
