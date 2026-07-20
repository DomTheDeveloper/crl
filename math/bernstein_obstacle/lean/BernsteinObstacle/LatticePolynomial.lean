import BernsteinObstacle.LatticeInterpolation
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Basic
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

/-- The embedded falling-factorial polynomial is the expected product of
linear factors in the selected coordinate. -/
theorem coordinateDescPochhammer_eq_prod (i : ι) (a : ℕ) :
    coordinateDescPochhammer i a =
      ∏ m in Finset.range a,
        (MvPolynomial.X i - MvPolynomial.C (m : ℝ)) := by
  induction a with
  | zero =>
      simp [coordinateDescPochhammer]
  | succ a ih =>
      simp [coordinateDescPochhammer, descPochhammer_succ_right,
        Finset.prod_range_succ, ih]

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

/-- A coordinate falling-factorial polynomial has total degree at most its
falling-factorial order. -/
theorem totalDegree_coordinateDescPochhammer_le (i : ι) (a : ℕ) :
    (coordinateDescPochhammer i a).totalDegree ≤ a := by
  rw [coordinateDescPochhammer_eq_prod]
  calc
    (∏ m in Finset.range a,
        (MvPolynomial.X i - MvPolynomial.C (m : ℝ))).totalDegree
        ≤ ∑ m in Finset.range a,
            (MvPolynomial.X i - MvPolynomial.C (m : ℝ)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _m in Finset.range a, 1 := by
      apply Finset.sum_le_sum
      intro m hm
      simpa using MvPolynomial.totalDegree_sub_C_le
        (MvPolynomial.X i : MvPolynomial ι ℝ) (m : ℝ)
    _ = a := by simp

/-- Normalization by a scalar does not increase the coordinate cardinal
factor's degree. -/
theorem totalDegree_coordinateLatticeCardinalPolynomial_le
    (i : ι) (a : ℕ) :
    (coordinateLatticeCardinalPolynomial i a).totalDegree ≤ a := by
  unfold coordinateLatticeCardinalPolynomial
  calc
    (MvPolynomial.C ((a.factorial : ℝ)⁻¹) *
        coordinateDescPochhammer i a).totalDegree
        ≤ (MvPolynomial.C ((a.factorial : ℝ)⁻¹) : MvPolynomial ι ℝ).totalDegree +
            (coordinateDescPochhammer i a).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + a := by
      exact Nat.add_le_add (by simp) (totalDegree_coordinateDescPochhammer_le i a)
    _ = a := by simp

/-- The complete cardinal polynomial attached to a degree-`n` simplex
multi-index.  The variables are the scaled barycentric coordinates `n * λᵢ`. -/
def latticeCardinalPolynomial (d n : ℕ) (α : MultiIndex d n) :
    MvPolynomial (Fin (d + 1)) ℝ :=
  ∏ i, coordinateLatticeCardinalPolynomial i (α.1 i)

/-- Every complete cardinal polynomial has total degree at most `n`. -/
theorem totalDegree_latticeCardinalPolynomial_le (d n : ℕ)
    (α : MultiIndex d n) :
    (latticeCardinalPolynomial d n α).totalDegree ≤ n := by
  unfold latticeCardinalPolynomial
  calc
    (∏ i, coordinateLatticeCardinalPolynomial i (α.1 i)).totalDegree
        ≤ ∑ i, (coordinateLatticeCardinalPolynomial i (α.1 i)).totalDegree := by
      simpa using MvPolynomial.totalDegree_finsetProd
        (Finset.univ : Finset (Fin (d + 1)))
        (fun i => coordinateLatticeCardinalPolynomial i (α.1 i))
    _ ≤ ∑ i, (α.1 i : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact totalDegree_coordinateLatticeCardinalPolynomial_le i (α.1 i)
    _ = n := α.2

/-- Hence every cardinal polynomial belongs to the multivariate polynomial
space of total degree at most `n`. -/
theorem latticeCardinalPolynomial_mem_restrictTotalDegree (d n : ℕ)
    (α : MultiIndex d n) :
    latticeCardinalPolynomial d n α ∈
      MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ n := by
  rw [MvPolynomial.mem_restrictTotalDegree]
  exact totalDegree_latticeCardinalPolynomial_le d n α

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

/-- The full family of cardinal polynomials is linearly independent. -/
theorem latticeCardinalPolynomial_linearIndependent (d n : ℕ) :
    LinearIndependent ℝ (latticeCardinalPolynomial d n) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h α
  have heval := congrArg
    (MvPolynomial.eval (fun i => ((α.1 i : ℕ) : ℝ))) h
  simpa [eval_latticeCardinalPolynomial_eq_ite] using heval

end LatticePolynomial

end

end BernsteinObstacle
