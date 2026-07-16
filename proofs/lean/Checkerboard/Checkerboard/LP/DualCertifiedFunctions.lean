import Checkerboard.LP.CubicField
import Checkerboard.LP.PrimalParameterBounds
import Checkerboard.LP.ContinuumModel

/-!
# Reduced exact dual certificate functions

These constants are the normalized `1,p,p²` representatives reconstructed from
the displayed dual system.  The certificate is defined directly from their
kernel-checkable evaluations; no floating-point constant and no unproved
rational-function simplification enters the definition.
-/

namespace Checkerboard

noncomputable section

/-- Reduced dual curvature coefficient. -/
def certifiedDualKRep : CubicRep :=
  ⟨(-1098531 / 144400 : ℚ), (13195599 / 288800 : ℚ), (-22897171 / 577600 : ℚ)⟩

/-- Reduced dual linear coefficient. -/
def certifiedDualRRep : CubicRep :=
  ⟨(810789 / 288800 : ℚ), (-12744461 / 577600 : ℚ), (1294527 / 57760 : ℚ)⟩

def certifiedDualSRep : CubicRep :=
  ⟨(489993 / 144400 : ℚ), (-420003 / 14440 : ℚ), (4499223 / 144400 : ℚ)⟩

def certifiedDualEllRep : CubicRep :=
  ⟨(-1230561 / 577600 : ℚ), (4736889 / 288800 : ℚ), (-7718857 / 577600 : ℚ)⟩

def certifiedDualQRep : CubicRep :=
  ⟨(1317747 / 577600 : ℚ), (-3032869 / 144400 : ℚ), (31570701 / 1155200 : ℚ)⟩

def certifiedDualN1Rep : CubicRep :=
  ⟨(-204729 / 144400 : ℚ), (335581 / 36100 : ℚ), (-5146329 / 577600 : ℚ)⟩

def certifiedDualNuRep : CubicRep :=
  ⟨(-128871 / 288800 : ℚ), (4580837 / 577600 : ℚ), (-5000067 / 577600 : ℚ)⟩

def certifiedDualN2Rep : CubicRep :=
  ⟨(-625473 / 144400 : ℚ), (4681961 / 144400 : ℚ), (-19965051 / 577600 : ℚ)⟩

/-- Real evaluations of the exact cubic representatives. -/
def certifiedDualK : ℝ := certifiedDualKRep.eval

def certifiedDualR : ℝ := certifiedDualRRep.eval

def certifiedDualS : ℝ := certifiedDualSRep.eval

def certifiedDualEll : ℝ := certifiedDualEllRep.eval

def certifiedDualQ : ℝ := certifiedDualQRep.eval

def certifiedDualN1 : ℝ := certifiedDualN1Rep.eval

def certifiedDualNu : ℝ := certifiedDualNuRep.eval

def certifiedDualN2 : ℝ := certifiedDualN2Rep.eval

/-- Polynomial pieces of the reconstructed dual certificate. -/
def certifiedDualBQ (t : ℝ) : ℝ :=
  (certifiedDualK / 2) * t ^ 2 + certifiedDualR * t + certifiedDualS

def certifiedDualBL (t : ℝ) : ℝ :=
  -certifiedDualEll * t + certifiedDualQ

def certifiedDualA1 (t : ℝ) : ℝ :=
  -certifiedDualK * t ^ 2 - 2 * certifiedDualR * t + certifiedDualN1

def certifiedDualAL (t : ℝ) : ℝ :=
  certifiedDualEll * t + certifiedDualNu

def certifiedDualA2 (t : ℝ) : ℝ :=
  -certifiedDualK * t ^ 2 + 2 * certifiedDualK * t + certifiedDualN2

/-- Piecewise real row/column profile, extended by zero outside `[0,1]`. -/
def certifiedDualAReal (t : ℝ) : ℝ :=
  if t < 0 then 0
  else if t ≤ checkerboardP then 0
  else if t ≤ primalC then certifiedDualA1 t
  else if t ≤ primalD then certifiedDualAL t
  else if t ≤ 1 then certifiedDualA2 t
  else 0

/-- Piecewise real diagonal profile, extended by zero outside `[0,1]`. -/
def certifiedDualBReal (t : ℝ) : ℝ :=
  if t < 0 then 0
  else if t ≤ primalE then certifiedDualBQ t
  else if t ≤ primalF then certifiedDualBL t
  else if t ≤ primalG then certifiedDualBQ t
  else 0

/-- Nonnegative extended-real profiles used in the continuum dual. -/
def certifiedDualA (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (certifiedDualAReal t)

def certifiedDualB (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (certifiedDualBReal t)

/-- The transformed real obstacle slack in variables `u=x+y`, `v=x-y`. -/
def certifiedDualSlackUV (u v : ℝ) : ℝ :=
  certifiedDualAReal ((u + v) / 2) +
    certifiedDualAReal ((2 - u + v) / 2) +
    certifiedDualBReal u + certifiedDualBReal v - 1

/-- The same real obstacle slack in the original triangular coordinates. -/
def certifiedDualSlackXY (z : ContinuumPoint) : ℝ :=
  certifiedDualAReal z.1 + certifiedDualAReal (1 - z.2) +
    certifiedDualBReal (z.1 + z.2) + certifiedDualBReal (z.1 - z.2) - 1

/-- Change of variables connecting the two obstacle presentations. -/
theorem certifiedDualSlackUV_change (z : ContinuumPoint) :
    certifiedDualSlackUV (z.1 + z.2) (z.1 - z.2) = certifiedDualSlackXY z := by
  simp [certifiedDualSlackUV, certifiedDualSlackXY]
  ring

lemma measurable_certifiedDualAReal : Measurable certifiedDualAReal := by
  unfold certifiedDualAReal certifiedDualA1 certifiedDualAL certifiedDualA2
  fun_prop

lemma measurable_certifiedDualBReal : Measurable certifiedDualBReal := by
  unfold certifiedDualBReal certifiedDualBQ certifiedDualBL
  fun_prop

lemma measurable_certifiedDualA : Measurable certifiedDualA := by
  exact ENNReal.measurable_ofReal.comp measurable_certifiedDualAReal

lemma measurable_certifiedDualB : Measurable certifiedDualB := by
  exact ENNReal.measurable_ofReal.comp measurable_certifiedDualBReal

end

end Checkerboard
