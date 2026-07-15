import A387471Trig

/-!
# Explicit solution-family identities for A387471

This module proves the ordinary cancellation identity and the two exceptional
fifth-root trigonometric identities used by the proposed complete
classification.
-/

namespace A387471

/-- The ordinary family is the elementary cancellation `sin 0 + sin t + sin (-t)`. -/
theorem ordinary_sine_identity (t : ℝ) :
    Real.sin 0 + Real.sin t + Real.sin (-t) = 0 := by
  simp

/-- The first exceptional fifth-root identity. -/
theorem exceptional_sine_identity_one :
    Real.sin (-Real.pi / 6) + Real.sin (-Real.pi / 10) +
      Real.sin (3 * Real.pi / 10) = 0 := by
  have hsin3 : Real.sin (3 * Real.pi / 10) = Real.cos (Real.pi / 5) := by
    rw [← Real.cos_pi_div_two_sub]
    congr 1
    ring
  have hsin1 : Real.sin (Real.pi / 10) = 2 * Real.cos (Real.pi / 5) ^ 2 - 1 := by
    calc
      Real.sin (Real.pi / 10) = Real.cos (Real.pi / 2 - Real.pi / 10) := by
        rw [Real.cos_pi_div_two_sub]
      _ = Real.cos (2 * (Real.pi / 5)) := by
        congr 1
        ring
      _ = 2 * Real.cos (Real.pi / 5) ^ 2 - 1 := by
        rw [Real.cos_two_mul]
  have hquad :
      4 * Real.cos (Real.pi / 5) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1 = 0 := by
    simpa using Real.quadratic_root_cos_pi_div_five
  rw [show -Real.pi / 6 = -(Real.pi / 6) by ring,
    show -Real.pi / 10 = -(Real.pi / 10) by ring,
    Real.sin_neg, Real.sin_neg, Real.sin_pi_div_six, hsin1, hsin3]
  linarith

/-- The conjugate exceptional fifth-root identity. -/
theorem exceptional_sine_identity_two :
    Real.sin (-3 * Real.pi / 10) + Real.sin (Real.pi / 10) +
      Real.sin (Real.pi / 6) = 0 := by
  have h := exceptional_sine_identity_one
  rw [show -Real.pi / 6 = -(Real.pi / 6) by ring,
    show -Real.pi / 10 = -(Real.pi / 10) by ring,
    Real.sin_neg, Real.sin_neg, Real.sin_pi_div_six] at h
  rw [show -3 * Real.pi / 10 = -(3 * Real.pi / 10) by ring,
    Real.sin_neg, Real.sin_pi_div_six]
  linarith

#print axioms ordinary_sine_identity
#print axioms exceptional_sine_identity_one
#print axioms exceptional_sine_identity_two

end A387471
