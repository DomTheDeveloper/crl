import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace BernsteinObstacle

section QuadraticLineRestriction

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure QuadraticPolynomialData (E : Type*) [AddCommGroup E] [Module ℝ E] where
  constant : ℝ
  linear : E →ₗ[ℝ] ℝ
  quadratic : E →ₗ[ℝ] E →ₗ[ℝ] ℝ

def QuadraticPolynomialData.eval
    (q : QuadraticPolynomialData E) (x : E) : ℝ :=
  q.constant + q.linear x + q.quadratic x x

def QuadraticPolynomialData.lineQuadraticCoefficient
    (q : QuadraticPolynomialData E) (direction : E) : ℝ :=
  q.quadratic direction direction

def QuadraticPolynomialData.lineLinearCoefficient
    (q : QuadraticPolynomialData E) (base direction : E) : ℝ :=
  q.linear direction + q.quadratic base direction +
    q.quadratic direction base

def QuadraticPolynomialData.lineConstantCoefficient
    (q : QuadraticPolynomialData E) (base : E) : ℝ :=
  q.constant + q.linear base + q.quadratic base base

theorem QuadraticPolynomialData.eval_affineLine
    (q : QuadraticPolynomialData E) (base direction : E) (t : ℝ) :
    q.eval (base + t • direction) =
      q.lineQuadraticCoefficient direction * t ^ 2 +
        q.lineLinearCoefficient base direction * t +
        q.lineConstantCoefficient base := by
  simp [QuadraticPolynomialData.eval,
    QuadraticPolynomialData.lineQuadraticCoefficient,
    QuadraticPolynomialData.lineLinearCoefficient,
    QuadraticPolynomialData.lineConstantCoefficient,
    map_add, map_smul]
  ring

def QuadraticPolynomialData.lineDerivativeSlope
    (q : QuadraticPolynomialData E) (direction : E) : ℝ :=
  2 * q.lineQuadraticCoefficient direction

def QuadraticPolynomialData.lineDerivativeIntercept
    (q : QuadraticPolynomialData E) (base direction : E) : ℝ :=
  q.lineLinearCoefficient base direction

def QuadraticPolynomialData.lineDerivative
    (q : QuadraticPolynomialData E) (base direction : E) (t : ℝ) : ℝ :=
  q.lineDerivativeSlope direction * t +
    q.lineDerivativeIntercept base direction

theorem hasDerivAt_quadraticPolynomial
    (A B C t : ℝ) :
    HasDerivAt (fun s : ℝ => A * s ^ 2 + B * s + C)
      (2 * A * t + B) t := by
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id' t).pow 2 using 1
    · funext s
      rfl
    · norm_num
  have hA : HasDerivAt (fun s : ℝ => A * s ^ 2) (A * (2 * t)) t :=
    hsq.const_mul A
  have hB : HasDerivAt (fun s : ℝ => B * s) B t := by
    simpa using (hasDerivAt_id' t).const_mul B
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (hA.add hB).add_const C

theorem QuadraticPolynomialData.hasDerivAt_eval_affineLine
    (q : QuadraticPolynomialData E) (base direction : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => q.eval (base + s • direction))
      (q.lineDerivative base direction t) t := by
  have hfun :
      (fun s : ℝ => q.eval (base + s • direction)) =
        (fun s : ℝ =>
          q.lineQuadraticCoefficient direction * s ^ 2 +
            q.lineLinearCoefficient base direction * s +
            q.lineConstantCoefficient base) := by
    funext s
    exact q.eval_affineLine base direction s
  rw [hfun]
  simpa [QuadraticPolynomialData.lineDerivative,
    QuadraticPolynomialData.lineDerivativeSlope,
    QuadraticPolynomialData.lineDerivativeIntercept] using
    hasDerivAt_quadraticPolynomial
      (q.lineQuadraticCoefficient direction)
      (q.lineLinearCoefficient base direction)
      (q.lineConstantCoefficient base) t

theorem QuadraticPolynomialData.lineDerivative_eq_affine
    (q : QuadraticPolynomialData E) (base direction : E) (t : ℝ) :
    q.lineDerivative base direction t =
      q.lineDerivativeSlope direction * t +
        q.lineDerivativeIntercept base direction :=
  rfl

theorem QuadraticPolynomialData.lineDerivative_explicit
    (q : QuadraticPolynomialData E) (base direction : E) (t : ℝ) :
    q.lineDerivative base direction t =
      (2 * q.quadratic direction direction) * t +
        (q.linear direction + q.quadratic base direction +
          q.quadratic direction base) := by
  rfl

end QuadraticLineRestriction

end BernsteinObstacle
