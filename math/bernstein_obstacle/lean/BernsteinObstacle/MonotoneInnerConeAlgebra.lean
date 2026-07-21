import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Strongly monotone inner-cone Falk algebra

The operator-specific analytical proof reduces the nonlinear/nonsymmetric
variational inequality to one scalar estimate. This file certifies the Young-
inequality endgame that converts that estimate into the standard recovery plus
consistency bound.
-/

/-- **Bernstein–Bézier Inner-Cone Falk inequality (scalar endgame).**
If strong monotonicity gives
`α e² ≤ L e r + residual`, then the solution error is controlled by the square
of the recovery error and the complementarity residual. -/
theorem monotoneInnerCone_falk_sq
    (e r residual α L : ℝ)
    (hα : 0 < α)
    (hcore : α * e ^ 2 ≤ L * e * r + residual) :
    e ^ 2 ≤ (L ^ 2 / α ^ 2) * r ^ 2 + (2 / α) * residual := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hαsq : 0 < α ^ 2 := sq_pos_of_pos hα
  have hyoung : 0 ≤ (α * e - L * r) ^ 2 := sq_nonneg (α * e - L * r)
  have hscaled :
      α ^ 2 * e ^ 2 ≤ L ^ 2 * r ^ 2 + 2 * α * residual := by
    nlinarith
  have hdiv :
      e ^ 2 ≤ (L ^ 2 * r ^ 2 + 2 * α * residual) / α ^ 2 := by
    apply (le_div_iff₀ hαsq).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  calc
    e ^ 2 ≤ (L ^ 2 * r ^ 2 + 2 * α * residual) / α ^ 2 := hdiv
    _ = (L ^ 2 / α ^ 2) * r ^ 2 + (2 / α) * residual := by
      field_simp [hα0] <;> ring

/-- Exact recovery (`residual = 0`) gives a Céa/Falk-type estimate for certified
inner approximations. -/
theorem monotoneInnerCone_exactRecovery_sq
    (e r α L : ℝ)
    (hα : 0 < α)
    (hcore : α * e ^ 2 ≤ L * e * r) :
    e ^ 2 ≤ (L ^ 2 / α ^ 2) * r ^ 2 := by
  have h := monotoneInnerCone_falk_sq e r 0 α L hα
    (by simpa using hcore)
  simpa using h

end BernsteinObstacle
