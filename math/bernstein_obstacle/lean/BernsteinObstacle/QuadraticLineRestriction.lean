import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Quadratic polynomial restriction to an affine line

A degree-two scalar polynomial is represented coordinate-free by a constant, a
linear form, and a bilinear form.  Its restriction to `base + t • direction`
is an ordinary scalar quadratic in `t`; consequently its formal line derivative
is affine.  This supplies the `alpha` and `beta` fiber coefficients used by the
transverse-prism saturation theorem.
-/

section QuadraticLineRestriction

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Coordinate-free data for a scalar polynomial of degree at most two. No
symmetry is required of the bilinear coefficient. -/
structure QuadraticPolynomialData (E : Type*) [AddCommGroup E] [Module ℝ E] where
  constant : ℝ
  linear : E →ₗ[ℝ] ℝ
  quadratic : E →ₗ[ℝ] E →ₗ[ℝ] ℝ

/-- Evaluation of the coordinate-free quadratic polynomial. -/
def QuadraticPolynomialData.eval
    (q : QuadraticPolynomialData E) (x : E) : ℝ :=
  q.constant + q.linear x + q.quadratic x x

/-- Quadratic coefficient after restriction to an affine line. -/
def QuadraticPolynomialData.lineQuadraticCoefficient
    (q : QuadraticPolynomialData E) (direction : E) : ℝ :=
  q.quadratic direction direction

/-- Linear coefficient after restriction to an affine line. -/
def QuadraticPolynomialData.lineLinearCoefficient
    (q : QuadraticPolynomialData E) (base direction : E) : ℝ :=
  q.linear direction + q.quadratic base direction +
    q.quadratic direction base

/-- Constant coefficient after restriction to an affine line. -/
def QuadraticPolynomialData.lineConstantCoefficient
    (q : QuadraticPolynomialData E) (base : E) : ℝ :=
  q.constant + q.linear base + q.quadratic base base

/-- Exact restriction identity: every coordinate-free quadratic becomes a
univariate quadratic on every affine line. -/
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

/-- Slope of the affine derivative of the line restriction. -/
def QuadraticPolynomialData.lineDerivativeSlope
    (q : QuadraticPolynomialData E) (direction : E) : ℝ :=
  2 * q.lineQuadraticCoefficient direction

/-- Intercept of the affine derivative of the line restriction. -/
def QuadraticPolynomialData.lineDerivativeIntercept
    (q : QuadraticPolynomialData E) (base direction : E) : ℝ :=
  q.lineLinearCoefficient base direction

/-- The formal derivative polynomial of the line restriction. -/
def QuadraticPolynomialData.lineDerivative
    (q : QuadraticPolynomialData E) (base direction : E) (t : ℝ) : ℝ :=
  q.lineDerivativeSlope direction * t +
    q.lineDerivativeIntercept base direction

/-- The normal derivative supplied by a quadratic restriction is affine with
explicit slope and intercept. -/
theorem QuadraticPolynomialData.lineDerivative_eq_affine
    (q : QuadraticPolynomialData E) (base direction : E) (t : ℝ) :
    q.lineDerivative base direction t =
      q.lineDerivativeSlope direction * t +
        q.lineDerivativeIntercept base direction :=
  rfl

/-- Expanded formula for the affine normal derivative coefficients. -/
theorem QuadraticPolynomialData.lineDerivative_explicit
    (q : QuadraticPolynomialData E) (base direction : E) (t : ℝ) :
    q.lineDerivative base direction t =
      (2 * q.quadratic direction direction) * t +
        (q.linear direction + q.quadratic base direction +
          q.quadratic direction base) := by
  rfl

end QuadraticLineRestriction

end BernsteinObstacle
