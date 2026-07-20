import Checkerboard.LP.CubicField

/-!
# Bivariate quadratic expressions over the cubic field

The generated dual certificate repeatedly substitutes affine coordinates into
piecewise quadratic dual functions. This file provides a small exact algebra
for representing the resulting bivariate quadratics over `ℚ(p)`.
-/

namespace Checkerboard

noncomputable section

/-- A linear expression in two real variables with coefficients in `ℚ(p)`. -/
structure CubicLinearRep where
  constant : CubicRep
  uCoeff : CubicRep
  vCoeff : CubicRep
  deriving DecidableEq

namespace CubicLinearRep

instance : Zero CubicLinearRep := ⟨⟨0, 0, 0⟩⟩

instance : Add CubicLinearRep where
  add L M :=
    { constant := L.constant + M.constant
      uCoeff := L.uCoeff + M.uCoeff
      vCoeff := L.vCoeff + M.vCoeff }

instance : Neg CubicLinearRep where
  neg L :=
    { constant := -L.constant
      uCoeff := -L.uCoeff
      vCoeff := -L.vCoeff }

instance : Sub CubicLinearRep where
  sub L M := L + -M

/-- Evaluate a linear expression at the exact root and real coordinates. -/
def eval (L : CubicLinearRep) (u v : ℝ) : ℝ :=
  L.constant.eval + L.uCoeff.eval * u + L.vCoeff.eval * v

@[simp] theorem zero_eval (u v : ℝ) : (0 : CubicLinearRep).eval u v = 0 := by
  simp [eval]

@[simp] theorem add_eval (L M : CubicLinearRep) (u v : ℝ) :
    (L + M).eval u v = L.eval u v + M.eval u v := by
  simp [HAdd.hAdd, Add.add, eval]
  ring

@[simp] theorem neg_eval (L : CubicLinearRep) (u v : ℝ) :
    (-L).eval u v = -L.eval u v := by
  simp [Neg.neg, eval]
  ring

@[simp] theorem sub_eval (L M : CubicLinearRep) (u v : ℝ) :
    (L - M).eval u v = L.eval u v - M.eval u v := by
  simp [Sub.sub, eval]
  ring

end CubicLinearRep

/-- A quadratic expression in two variables over `ℚ(p)`. -/
structure CubicQuadraticRep where
  constant : CubicRep
  uCoeff : CubicRep
  vCoeff : CubicRep
  uuCoeff : CubicRep
  uvCoeff : CubicRep
  vvCoeff : CubicRep
  deriving DecidableEq

namespace CubicQuadraticRep

instance : Zero CubicQuadraticRep :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- Exact evaluation of the bivariate quadratic. -/
def eval (Q : CubicQuadraticRep) (u v : ℝ) : ℝ :=
  Q.constant.eval + Q.uCoeff.eval * u + Q.vCoeff.eval * v +
    Q.uuCoeff.eval * u ^ 2 + Q.uvCoeff.eval * u * v + Q.vvCoeff.eval * v ^ 2

/-- Addition of bivariate quadratics. -/
def add (Q R : CubicQuadraticRep) : CubicQuadraticRep :=
  { constant := Q.constant + R.constant
    uCoeff := Q.uCoeff + R.uCoeff
    vCoeff := Q.vCoeff + R.vCoeff
    uuCoeff := Q.uuCoeff + R.uuCoeff
    uvCoeff := Q.uvCoeff + R.uvCoeff
    vvCoeff := Q.vvCoeff + R.vvCoeff }

/-- Negation of a bivariate quadratic. -/
def neg (Q : CubicQuadraticRep) : CubicQuadraticRep :=
  { constant := -Q.constant
    uCoeff := -Q.uCoeff
    vCoeff := -Q.vCoeff
    uuCoeff := -Q.uuCoeff
    uvCoeff := -Q.uvCoeff
    vvCoeff := -Q.vvCoeff }

/-- Subtraction of bivariate quadratics. -/
def sub (Q R : CubicQuadraticRep) : CubicQuadraticRep := add Q (neg R)

/-- Scalar multiplication by an element of the cubic field. -/
def scale (a : CubicRep) (Q : CubicQuadraticRep) : CubicQuadraticRep :=
  { constant := a * Q.constant
    uCoeff := a * Q.uCoeff
    vCoeff := a * Q.vCoeff
    uuCoeff := a * Q.uuCoeff
    uvCoeff := a * Q.uvCoeff
    vvCoeff := a * Q.vvCoeff }

/-- Regard a linear expression as a quadratic. -/
def ofLinear (L : CubicLinearRep) : CubicQuadraticRep :=
  { constant := L.constant
    uCoeff := L.uCoeff
    vCoeff := L.vCoeff
    uuCoeff := 0
    uvCoeff := 0
    vvCoeff := 0 }

/-- Product of two linear expressions. -/
def mulLinear (L M : CubicLinearRep) : CubicQuadraticRep :=
  { constant := L.constant * M.constant
    uCoeff := L.constant * M.uCoeff + L.uCoeff * M.constant
    vCoeff := L.constant * M.vCoeff + L.vCoeff * M.constant
    uuCoeff := L.uCoeff * M.uCoeff
    uvCoeff := L.uCoeff * M.vCoeff + L.vCoeff * M.uCoeff
    vvCoeff := L.vCoeff * M.vCoeff }

/-- Substitute a linear expression into a univariate quadratic. -/
def composeUnivariate (a b c : CubicRep) (L : CubicLinearRep) : CubicQuadraticRep :=
  add
    { constant := a
      uCoeff := 0
      vCoeff := 0
      uuCoeff := 0
      uvCoeff := 0
      vvCoeff := 0 }
    (add (scale b (ofLinear L)) (scale c (mulLinear L L)))

@[simp] theorem eval_zero (u v : ℝ) : (0 : CubicQuadraticRep).eval u v = 0 := by
  simp [eval]

@[simp] theorem eval_add (Q R : CubicQuadraticRep) (u v : ℝ) :
    (add Q R).eval u v = Q.eval u v + R.eval u v := by
  simp [add, eval]
  ring

@[simp] theorem eval_neg (Q : CubicQuadraticRep) (u v : ℝ) :
    (neg Q).eval u v = -Q.eval u v := by
  simp [neg, eval]
  ring

@[simp] theorem eval_sub (Q R : CubicQuadraticRep) (u v : ℝ) :
    (sub Q R).eval u v = Q.eval u v - R.eval u v := by
  simp [sub]
  ring

@[simp] theorem eval_scale (a : CubicRep) (Q : CubicQuadraticRep) (u v : ℝ) :
    (scale a Q).eval u v = a.eval * Q.eval u v := by
  simp [scale, eval]
  ring

@[simp] theorem eval_ofLinear (L : CubicLinearRep) (u v : ℝ) :
    (ofLinear L).eval u v = L.eval u v := by
  simp [ofLinear, eval, CubicLinearRep.eval]

@[simp] theorem eval_mulLinear (L M : CubicLinearRep) (u v : ℝ) :
    (mulLinear L M).eval u v = L.eval u v * M.eval u v := by
  simp [mulLinear, eval, CubicLinearRep.eval]
  ring

@[simp] theorem eval_composeUnivariate
    (a b c : CubicRep) (L : CubicLinearRep) (u v : ℝ) :
    (composeUnivariate a b c L).eval u v =
      a.eval + b.eval * L.eval u v + c.eval * (L.eval u v) ^ 2 := by
  simp [composeUnivariate]
  ring_nf

/-- Coefficientwise extensionality is convenient for generated exact checks. -/
@[ext] theorem ext {Q R : CubicQuadraticRep}
    (h0 : Q.constant = R.constant)
    (hu : Q.uCoeff = R.uCoeff)
    (hv : Q.vCoeff = R.vCoeff)
    (huu : Q.uuCoeff = R.uuCoeff)
    (huv : Q.uvCoeff = R.uvCoeff)
    (hvv : Q.vvCoeff = R.vvCoeff) : Q = R := by
  cases Q
  cases R
  simp_all

end CubicQuadraticRep

end

end Checkerboard
