import Checkerboard.LP.AlgebraicParameter

/-!
# Exact arithmetic in the checkerboard cubic field

Certificate generators work with coefficient triples in the basis `1,p,p²`.
This file defines their normalized multiplication modulo

`401 p³ - 331 p² + 19 p + 7 = 0`

and proves that evaluation at the isolated real root respects every operation.
Generated certificate files may therefore reduce large identities to rational
coefficient checks without trusting the generator's quotient-ring arithmetic.
-/

namespace Checkerboard

noncomputable section

/-- A rational representative `a + b*p + c*p²`. -/
structure CubicRep where
  constant : ℚ
  linear : ℚ
  quadratic : ℚ
  deriving DecidableEq, Repr

namespace CubicRep

/-- Evaluation at the exact isolated checkerboard root. -/
def eval (x : CubicRep) : ℝ :=
  (x.constant : ℝ) + (x.linear : ℝ) * checkerboardP +
    (x.quadratic : ℝ) * checkerboardP ^ 2

/-- Coefficientwise zero and one. -/
def zero : CubicRep := ⟨0, 0, 0⟩

def one : CubicRep := ⟨1, 0, 0⟩

/-- Coefficientwise addition and negation. -/
def add (x y : CubicRep) : CubicRep :=
  ⟨x.constant + y.constant, x.linear + y.linear,
    x.quadratic + y.quadratic⟩

def neg (x : CubicRep) : CubicRep :=
  ⟨-x.constant, -x.linear, -x.quadratic⟩

def sub (x y : CubicRep) : CubicRep := add x (neg y)

/-- Rational scalar multiplication. -/
def scale (q : ℚ) (x : CubicRep) : CubicRep :=
  ⟨q * x.constant, q * x.linear, q * x.quadratic⟩

/-- Normalized multiplication modulo the defining cubic. -/
def mul (x y : CubicRep) : CubicRep :=
  let d0 := x.constant * y.constant
  let d1 := x.constant * y.linear + x.linear * y.constant
  let d2 := x.constant * y.quadratic + x.linear * y.linear +
    x.quadratic * y.constant
  let d3 := x.linear * y.quadratic + x.quadratic * y.linear
  let d4 := x.quadratic * y.quadratic
  ⟨d0 - (7 / 401) * d3 - (2317 / 160801) * d4,
   d1 - (19 / 401) * d3 - (9096 / 160801) * d4,
   d2 + (331 / 401) * d3 + (101942 / 160801) * d4⟩

/-- The defining cubic solved for `p³`. -/
theorem checkerboardP_cube :
    checkerboardP ^ 3 =
      (-7 / 401 : ℝ) + (-19 / 401 : ℝ) * checkerboardP +
        (331 / 401 : ℝ) * checkerboardP ^ 2 := by
  have hp := checkerboardP_root
  simp [pPoly] at hp
  nlinarith

/-- The corresponding reduction of `p⁴`. -/
theorem checkerboardP_fourth :
    checkerboardP ^ 4 =
      (-2317 / 160801 : ℝ) + (-9096 / 160801 : ℝ) * checkerboardP +
        (101942 / 160801 : ℝ) * checkerboardP ^ 2 := by
  calc
    checkerboardP ^ 4 = checkerboardP * checkerboardP ^ 3 := by ring
    _ = checkerboardP *
        ((-7 / 401 : ℝ) + (-19 / 401 : ℝ) * checkerboardP +
          (331 / 401 : ℝ) * checkerboardP ^ 2) := by
      rw [checkerboardP_cube]
    _ = (-7 / 401 : ℝ) * checkerboardP +
        (-19 / 401 : ℝ) * checkerboardP ^ 2 +
        (331 / 401 : ℝ) * checkerboardP ^ 3 := by ring
    _ = (-2317 / 160801 : ℝ) + (-9096 / 160801 : ℝ) * checkerboardP +
        (101942 / 160801 : ℝ) * checkerboardP ^ 2 := by
      rw [checkerboardP_cube]
      ring

@[simp] theorem eval_zero : zero.eval = 0 := by
  norm_num [zero, eval]

@[simp] theorem eval_one : one.eval = 1 := by
  norm_num [one, eval]

@[simp] theorem eval_add (x y : CubicRep) :
    (add x y).eval = x.eval + y.eval := by
  simp [add, eval]
  ring

@[simp] theorem eval_neg (x : CubicRep) :
    (neg x).eval = -x.eval := by
  simp [neg, eval]
  ring

@[simp] theorem eval_sub (x y : CubicRep) :
    (sub x y).eval = x.eval - y.eval := by
  simp [sub]
  ring

@[simp] theorem eval_scale (q : ℚ) (x : CubicRep) :
    (scale q x).eval = (q : ℝ) * x.eval := by
  simp [scale, eval]
  ring

/-- Evaluation respects the normalized quotient-ring product. -/
@[simp] theorem eval_mul (x y : CubicRep) :
    (mul x y).eval = x.eval * y.eval := by
  let d0 : ℚ := x.constant * y.constant
  let d1 : ℚ := x.constant * y.linear + x.linear * y.constant
  let d2 : ℚ := x.constant * y.quadratic + x.linear * y.linear +
    x.quadratic * y.constant
  let d3 : ℚ := x.linear * y.quadratic + x.quadratic * y.linear
  let d4 : ℚ := x.quadratic * y.quadratic
  change
    (((d0 - (7 / 401) * d3 - (2317 / 160801) * d4 : ℚ) : ℝ) +
      ((d1 - (19 / 401) * d3 - (9096 / 160801) * d4 : ℚ) : ℝ) * checkerboardP +
      ((d2 + (331 / 401) * d3 + (101942 / 160801) * d4 : ℚ) : ℝ) *
        checkerboardP ^ 2) = x.eval * y.eval
  calc
    _ = (d0 : ℝ) + (d1 : ℝ) * checkerboardP +
        (d2 : ℝ) * checkerboardP ^ 2 +
        (d3 : ℝ) * checkerboardP ^ 3 +
        (d4 : ℝ) * checkerboardP ^ 4 := by
      rw [checkerboardP_cube, checkerboardP_fourth]
      push_cast
      ring
    _ = x.eval * y.eval := by
      dsimp [d0, d1, d2, d3, d4]
      simp only [eval]
      push_cast
      ring

/-- Coefficient equality implies equality after evaluation. -/
theorem eval_eq_of_eq {x y : CubicRep} (h : x = y) : x.eval = y.eval := by
  simpa [h]

/-- A coefficientwise zero certificate proves exact vanishing at `p`. -/
theorem eval_eq_zero_of_coefficients
    {x : CubicRep} (h0 : x.constant = 0) (h1 : x.linear = 0)
    (h2 : x.quadratic = 0) : x.eval = 0 := by
  simp [eval, h0, h1, h2]

/-- A coefficientwise one certificate proves exact value one at `p`. -/
theorem eval_eq_one_of_coefficients
    {x : CubicRep} (h0 : x.constant = 1) (h1 : x.linear = 0)
    (h2 : x.quadratic = 0) : x.eval = 1 := by
  simp [eval, h0, h1, h2]

end CubicRep

end

end Checkerboard
