import Checkerboard.LP.AlgebraicParameter

/-!
# Exact algebraic parameters for the continuum primal certificate

The outer and middle transport blocks use the following elements of `ℚ(p)`.
The structural mass identities below are exact ring identities; they do not
come from floating-point reconstruction.
-/

namespace Checkerboard

noncomputable section

/-- The first internal breakpoint of the primal transport certificate. -/
def primalC : ℝ :=
  (187 * checkerboardP^3 - 211 * checkerboardP^2 + 61 * checkerboardP - 5) /
    (2 * (71 * checkerboardP^2 - 66 * checkerboardP + 11))

/-- The reflected breakpoint. -/
def primalD : ℝ := 1 + checkerboardP - primalC

/-- Lower middle-block endpoint. -/
def primalE : ℝ := (2 * primalC + 3 * checkerboardP - 1) / 4

/-- Upper middle-block endpoint. -/
def primalF : ℝ := (-2 * primalC + 5 * checkerboardP + 1) / 4

/-- Outer diagonal endpoint. -/
def primalG : ℝ := (1 - 3 * checkerboardP + 2 * primalC) / 2

/-- Length scale of the outer transport block. -/
def outerLength : ℝ := primalC - checkerboardP

/-- Length scale of the middle transport block. -/
def middleLength : ℝ := primalD - primalC

/-- Normalized outer transport parameters. -/
def outerR : ℝ := checkerboardP / outerLength

def outerQ : ℝ := (primalF - checkerboardP) / outerLength

def outerH : ℝ := (primalG - checkerboardP) / outerLength

lemma outerLength_eq_one_sub_primalD : outerLength = 1 - primalD := by
  simp [outerLength, primalD]
  ring

lemma middleLength_eq_four_mul_primalF_sub_p :
    middleLength = 4 * (primalF - checkerboardP) := by
  simp [middleLength, primalD, primalF]
  ring

lemma p_sub_primalE_eq_primalF_sub_p :
    checkerboardP - primalE = primalF - checkerboardP := by
  simp [primalE, primalF]
  ring

/-- The outer block has mass `4L`, the middle block has mass `2M`, and their
sum is exactly the checkerboard constant. -/
lemma primal_block_mass_identity :
    4 * outerLength + 2 * middleLength = checkerboardAlpha := by
  simp [outerLength, middleLength, primalD, checkerboardAlpha]
  ring

lemma primal_block_mass_identity' :
    checkerboardAlpha = 4 * outerLength + 2 * middleLength :=
  primal_block_mass_identity.symm

end

end Checkerboard
