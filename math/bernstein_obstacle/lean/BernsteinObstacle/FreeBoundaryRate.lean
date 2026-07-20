import Mathlib.Tactic

open Filter

namespace BernsteinObstacle

/-!
# Codimension-one free-boundary rate arithmetic

This file formalizes the scale calculation behind the regular-interface repair.
If the repair gradient is `O(h)` on a patch of measure `O(h)`, then its squared
`H¹` contribution is `O(h³)`, corresponding to an `H¹` contribution of order
`h^(3/2)`.  Geometry and interpolation are deliberately separate obligations.
-/

section FreeBoundaryRate

/-- Pointwise gradient scale `g ≤ Cg h`, patch measure `m ≤ Cm h`, and an
energy bound `costSq ≤ g² m` imply the cubic squared-error estimate. -/
theorem codimOne_patch_gradient_sq_le_cubic
    (h g m costSq Cg Cm : ℝ)
    (hh : 0 ≤ h) (hg : 0 ≤ g) (hm : 0 ≤ m)
    (hCg : 0 ≤ Cg) (hCm : 0 ≤ Cm)
    (hgBound : g ≤ Cg * h)
    (hmBound : m ≤ Cm * h)
    (hcost : costSq ≤ g ^ 2 * m) :
    costSq ≤ Cg ^ 2 * Cm * h ^ 3 := by
  have hfactor : 0 ≤ (Cg * h - g) * (Cg * h + g) :=
    mul_nonneg (sub_nonneg.mpr hgBound)
      (add_nonneg (mul_nonneg hCg hh) hg)
  have hgSq : g ^ 2 ≤ (Cg * h) ^ 2 := by
    nlinarith
  calc
    costSq ≤ g ^ 2 * m := hcost
    _ ≤ (Cg * h) ^ 2 * m := mul_le_mul_of_nonneg_right hgSq hm
    _ ≤ (Cg * h) ^ 2 * (Cm * h) :=
      mul_le_mul_of_nonneg_left hmBound (sq_nonneg (Cg * h))
    _ = Cg ^ 2 * Cm * h ^ 3 := by ring

/-- Any nonnegative squared cost bounded by a fixed multiple of `h³` tends to
zero when the local mesh scale tends to zero. -/
theorem cubic_squared_cost_tendsto_zero
    (h costSq : ℕ → ℝ) (C : ℝ)
    (hcostNonneg : ∀ k, 0 ≤ costSq k)
    (hcost : ∀ k, costSq k ≤ C * h k ^ 3)
    (hh : Tendsto h atTop (nhds 0)) :
    Tendsto costSq atTop (nhds 0) := by
  have hupper : Tendsto (fun k => C * h k ^ 3) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hh.pow 3)
  exact squeeze_zero'
    (Eventually.of_forall hcostNonneg)
    (Eventually.of_forall hcost)
    hupper

/-- Bulk and free-boundary contributions that vanish separately also vanish in
the combined error majorant. -/
theorem combined_bulk_strip_rate_tendsto_zero
    (bulk strip : ℕ → ℝ)
    (hbulk : Tendsto bulk atTop (nhds 0))
    (hstrip : Tendsto strip atTop (nhds 0)) :
    Tendsto (fun k => bulk k + strip k) atTop (nhds 0) :=
  hbulk.add hstrip

end FreeBoundaryRate

end BernsteinObstacle
