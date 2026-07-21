import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Codimension–growth and balanced-contact exponent algebra

The analytical clipping proof supplies three parameters:

* `q`: the energy/Bregman power;
* `β`: the coefficient-defect or contact-growth order;
* `κ`: the patch-measure exponent.

This file formalizes the exponent bookkeeping independently of the geometric
and Sobolev estimates that provide those parameters.
-/

/-- Exponent produced by the coefficient clipping repair. -/
def repairExponent (q β κ : ℝ) : ℝ := β - 1 + κ / q

/-- Exponent produced after taking the `q`-root of multiplier consistency. -/
def multiplierExponent (q β κ : ℝ) : ℝ := (β + κ) / q

/-- The interface rate is governed by the slower of repair and multiplier
consistency. -/
def grandInterfaceExponent (q β κ : ℝ) : ℝ :=
  min (repairExponent q β κ) (multiplierExponent q β κ)

/-- Quadratic contact on a codimension-one patch has repair exponent `3/2` in
a quadratic energy. -/
theorem quadratic_hypersurface_repairExponent :
    repairExponent 2 2 1 = (3 : ℝ) / 2 := by
  norm_num [repairExponent]

/-- The multiplier mechanism has the same `3/2` exponent in the classical
quadratic hypersurface case. -/
theorem quadratic_hypersurface_multiplierExponent :
    multiplierExponent 2 2 1 = (3 : ℝ) / 2 := by
  norm_num [multiplierExponent]

/-- **Three-Halves Contact Law (algebraic specialization).** -/
theorem threeHalvesContactLaw :
    grandInterfaceExponent 2 2 1 = (3 : ℝ) / 2 := by
  norm_num [grandInterfaceExponent, repairExponent, multiplierExponent]

/-- The contact-growth order that balances repair and multiplier mechanisms. -/
def balancedContactOrder (q : ℝ) : ℝ := q / (q - 1)

/-- **Balanced Contact Exponent Principle.** For `q ≠ 0,1`, the order
`β = q/(q-1)` makes the geometric repair and multiplier exponents coincide. -/
theorem balancedContactOrder_equalizes
    (q κ : ℝ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    repairExponent q (balancedContactOrder q) κ =
      multiplierExponent q (balancedContactOrder q) κ := by
  have hqsub : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  unfold repairExponent multiplierExponent balancedContactOrder
  field_simp [hq0, hqsub]
  ring

/-- Quadratic energy has balanced contact order two. -/
theorem balancedContactOrder_two :
    balancedContactOrder 2 = (2 : ℝ) := by
  norm_num [balancedContactOrder]

end

end BernsteinObstacle
