import Checkerboard.LP.PrimalParameters

/-!
# Exact definitions of Prellberg's odd-fat continuum dual pair

This file transcribes equations (2)--(6) of the published certificate exactly.
It contains definitions and algebraic identities only.  Positivity, breakpoint
ordering, obstacle coverage, and the integral objective are proved in the
separate generated certificate module.
-/

namespace Checkerboard

noncomputable section

/-- Coefficients of the two-by-two system defining the quadratic curvature and
linear term of the dual profile. -/
def dualSystemC : ℝ :=
  - primalC^2 + (1/2 : ℝ) * primalC * primalE + (1/2 : ℝ) * primalC * primalF +
    primalD^2 - (1/2 : ℝ) * primalD * primalE - (1/2 : ℝ) * primalD * primalF -
    2 * primalD - primalG^2 + 2 * checkerboardP^2 + 1

def dualSystemD : ℝ :=
  - primalC - primalD - 2 * primalG + 4 * checkerboardP

def dualSystemE : ℝ :=
  - 2 * primalC^2 + primalC * primalE + primalC * primalF -
    (1/2 : ℝ) * primalE * primalF - (1/2 : ℝ) * primalE -
    (1/2 : ℝ) * primalF - (1/2 : ℝ) * primalG^2 + 2 * checkerboardP^2

def dualSystemH : ℝ :=
  - 2 * primalC - primalG + 4 * checkerboardP - 1

/-- Determinant of the exact linear system `K*C+r*D=1`, `K*E+r*H=1`. -/
def dualSystemDet : ℝ := dualSystemC * dualSystemH - dualSystemE * dualSystemD

/-- Exact Cramer-rule solution of the dual coefficient system. -/
def dualK : ℝ := (dualSystemH - dualSystemD) / dualSystemDet

def dualR : ℝ := (dualSystemC - dualSystemE) / dualSystemDet

lemma dual_linear_system_first (hdet : dualSystemDet ≠ 0) :
    dualK * dualSystemC + dualR * dualSystemD = 1 := by
  field_simp [dualK, dualR, dualSystemDet, hdet]
  ring

lemma dual_linear_system_second (hdet : dualSystemDet ≠ 0) :
    dualK * dualSystemE + dualR * dualSystemH = 1 := by
  field_simp [dualK, dualR, dualSystemDet, hdet]
  ring

/-- Remaining exact constants from equation (4). -/
def dualS : ℝ := -(dualK / 2) * primalG^2 - dualR * primalG

def dualEll : ℝ := -((dualK / 2) * (primalE + primalF) + dualR)

def dualQ : ℝ :=
  -(dualK / 2) * primalE * primalF - (dualK / 2) * primalG^2 - dualR * primalG

def dualN1 : ℝ := dualK * checkerboardP^2 + 2 * dualR * checkerboardP

def dualNu : ℝ :=
  (-2 * dualK * primalC^2 + dualK * primalC * primalE +
      dualK * primalC * primalF + 2 * dualK * checkerboardP^2 -
      2 * primalC * dualR + 4 * checkerboardP * dualR) / 2

def dualN2 : ℝ :=
  (-2 * dualK * primalC^2 + dualK * primalC * primalE +
      dualK * primalC * primalF + 2 * dualK * primalD^2 -
      dualK * primalD * primalE - dualK * primalD * primalF -
      4 * dualK * primalD + 2 * dualK * checkerboardP^2 -
      2 * primalC * dualR - 2 * primalD * dualR +
      4 * checkerboardP * dualR) / 2

/-- Elementary polynomial pieces from equation (5). -/
def dualBQ (t : ℝ) : ℝ := (dualK / 2) * t^2 + dualR * t + dualS

def dualBL (t : ℝ) : ℝ := -dualEll * t + dualQ

def dualA1 (t : ℝ) : ℝ := -dualK * t^2 - 2 * dualR * t + dualN1

def dualAL (t : ℝ) : ℝ := dualEll * t + dualNu

def dualA2 (t : ℝ) : ℝ := -dualK * t^2 + 2 * dualK * t + dualN2

/-- Piecewise quadratic-linear row/column profile from equation (6).
It is extended by zero outside `[0,1]`; only values on `[0,1]` occur in the
continuum obstacle problem. -/
def dualAReal (t : ℝ) : ℝ :=
  if t < 0 then 0
  else if t ≤ checkerboardP then 0
  else if t ≤ primalC then dualA1 t
  else if t ≤ primalD then dualAL t
  else if t ≤ 1 then dualA2 t
  else 0

/-- Piecewise quadratic-linear diagonal profile from equation (6), extended by
zero outside `[0,1]`. -/
def dualBReal (t : ℝ) : ℝ :=
  if t < 0 then 0
  else if t ≤ primalE then dualBQ t
  else if t ≤ primalF then dualBL t
  else if t ≤ primalG then dualBQ t
  else 0

/-- The real-valued obstacle slack whose exact Bernstein certificate is checked
on the 40 certificate triangles. -/
def dualObstacleSlack (x y : ℝ) : ℝ :=
  dualAReal x + dualAReal (1-y) + dualBReal (x+y) + dualBReal (x-y) - 1

lemma dualA1_at_p : dualA1 checkerboardP = 0 := by
  simp [dualA1, dualN1]
  ring

lemma dualBQ_at_g : dualBQ primalG = 0 := by
  simp [dualBQ, dualS]
  ring

lemma dualBQ_at_e_eq_dualBL : dualBQ primalE = dualBL primalE := by
  simp [dualBQ, dualBL, dualQ, dualEll, dualS]
  ring

lemma dualBQ_at_f_eq_dualBL : dualBQ primalF = dualBL primalF := by
  simp [dualBQ, dualBL, dualQ, dualEll, dualS]
  ring

end

end Checkerboard
