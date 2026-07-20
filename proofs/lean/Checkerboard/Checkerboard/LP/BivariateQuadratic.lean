import Checkerboard.LP.CubicField

/-!
# Bivariate quadratic arithmetic over the checkerboard cubic field

The dual obstacle is quadratic in the transformed coordinates `(u,v)`. This
module provides a tiny exact algebra for linear and quadratic polynomials whose
coefficients lie in `ℚ(p)`. Generated Handelman certificates are then checked
coefficientwise by the Lean kernel.
-/

namespace Checkerboard

noncomputable section

/-- An affine-linear polynomial `c + au*u + av*v`. -/
structure CubicLinearRep where
  constant : CubicRep
  uCoeff : CubicRep
  vCoeff : CubicRep
  deriving DecidableEq, Repr

/-- A quadratic polynomial in the basis `1,u,v,u²,uv,v²`. -/
structure CubicQuadraticRep where
  constant : CubicRep
  uCoeff : CubicRep
  vCoeff : CubicRep
  uuCoeff : CubicRep
  uvCoeff : CubicRep
  vvCoeff : CubicRep
  deriving DecidableEq, Repr

namespace CubicLinearRep

/-- Real evaluation. -/
def eval (L : CubicLinearRep) (u v : ℝ) : ℝ :=
  L.constant.eval + L.uCoeff.eval * u + L.vCoeff.eval * v

/-- Addition, negation, and cubic-field scalar multiplication. -/
def add (L M : CubicLinearRep) : CubicLinearRep :=
  ⟨CubicRep.add L.constant M.constant,
   CubicRep.add L.uCoeff M.uCoeff,
   CubicRep.add L.vCoeff M.vCoeff⟩

def neg (L : CubicLinearRep) : CubicLinearRep :=
  ⟨CubicRep.neg L.constant, CubicRep.neg L.uCoeff, CubicRep.neg L.vCoeff⟩

def sub (L M : CubicLinearRep) : CubicLinearRep := add L (neg M)

def scale (a : CubicRep) (L : CubicLinearRep) : CubicLinearRep :=
  ⟨CubicRep.mul a L.constant,
   CubicRep.mul a L.uCoeff,
   CubicRep.mul a L.vCoeff⟩

@[simp] theorem eval_add (L M : CubicLinearRep) (u v : ℝ) :
    (add L M).eval u v = L.eval u v + M.eval u v := by
  simp [add, eval]
  ring

@[simp] theorem eval_neg (L : CubicLinearRep) (u v : ℝ) :
    (neg L).eval u v = -L.eval u v := by
  simp [neg, eval]
  ring

@[simp] theorem eval_sub (L M : CubicLinearRep) (u v : ℝ) :
    (sub L M).eval u v = L.eval u v - M.eval u v := by
  simp [sub]
  ring

@[simp] theorem eval_scale (a : CubicRep) (L : CubicLinearRep) (u v : ℝ) :
    (scale a L).eval u v = a.eval * L.eval u v := by
  simp [scale, eval]
  ring

end CubicLinearRep

namespace CubicQuadraticRep

/-- Real evaluation. -/
def eval (Q : CubicQuadraticRep) (u v : ℝ) : ℝ :=
  Q.constant.eval + Q.uCoeff.eval * u + Q.vCoeff.eval * v +
    Q.uuCoeff.eval * u ^ 2 + Q.uvCoeff.eval * u * v +
      Q.vvCoeff.eval * v ^ 2

/-- Zero, addition, negation, and cubic-field scaling. -/
def zero : CubicQuadraticRep :=
  ⟨CubicRep.zero, CubicRep.zero, CubicRep.zero,
   CubicRep.zero, CubicRep.zero, CubicRep.zero⟩

def add (Q R : CubicQuadraticRep) : CubicQuadraticRep :=
  ⟨CubicRep.add Q.constant R.constant,
   CubicRep.add Q.uCoeff R.uCoeff,
   CubicRep.add Q.vCoeff R.vCoeff,
   CubicRep.add Q.uuCoeff R.uuCoeff,
   CubicRep.add Q.uvCoeff R.uvCoeff,
   CubicRep.add Q.vvCoeff R.vvCoeff⟩

def neg (Q : CubicQuadraticRep) : CubicQuadraticRep :=
  ⟨CubicRep.neg Q.constant, CubicRep.neg Q.uCoeff,
   CubicRep.neg Q.vCoeff, CubicRep.neg Q.uuCoeff,
   CubicRep.neg Q.uvCoeff, CubicRep.neg Q.vvCoeff⟩

def sub (Q R : CubicQuadraticRep) : CubicQuadraticRep := add Q (neg R)

def scale (a : CubicRep) (Q : CubicQuadraticRep) : CubicQuadraticRep :=
  ⟨CubicRep.mul a Q.constant,
   CubicRep.mul a Q.uCoeff,
   CubicRep.mul a Q.vCoeff,
   CubicRep.mul a Q.uuCoeff,
   CubicRep.mul a Q.uvCoeff,
   CubicRep.mul a Q.vvCoeff⟩

/-- Embed a linear polynomial as a quadratic one. -/
def ofLinear (L : CubicLinearRep) : CubicQuadraticRep :=
  ⟨L.constant, L.uCoeff, L.vCoeff,
   CubicRep.zero, CubicRep.zero, CubicRep.zero⟩

/-- Product of two affine-linear polynomials. -/
def mulLinear (L M : CubicLinearRep) : CubicQuadraticRep :=
  ⟨CubicRep.mul L.constant M.constant,
   CubicRep.add (CubicRep.mul L.constant M.uCoeff)
     (CubicRep.mul L.uCoeff M.constant),
   CubicRep.add (CubicRep.mul L.constant M.vCoeff)
     (CubicRep.mul L.vCoeff M.constant),
   CubicRep.mul L.uCoeff M.uCoeff,
   CubicRep.add (CubicRep.mul L.uCoeff M.vCoeff)
     (CubicRep.mul L.vCoeff M.uCoeff),
   CubicRep.mul L.vCoeff M.vCoeff⟩

/-- Compose a univariate quadratic `a + bt + ct²` with an affine-linear form. -/
def composeUnivariate (a b c : CubicRep) (L : CubicLinearRep) : CubicQuadraticRep :=
  add (ofLinear (CubicLinearRep.add
      ⟨a, CubicRep.zero, CubicRep.zero⟩
      (CubicLinearRep.scale b L)))
    (scale c (mulLinear L L))

@[simp] theorem eval_zero (u v : ℝ) : zero.eval u v = 0 := by
  simp [zero, eval]

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
