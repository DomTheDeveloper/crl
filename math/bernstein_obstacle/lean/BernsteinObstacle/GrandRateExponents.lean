import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace BernsteinObstacle

noncomputable section

/-!
# Codimension–growth and balanced-contact exponent algebra

The analytical clipping proof supplies four parameters:

* `q`: the energy/Bregman power;
* `β`: the coefficient-defect or contact-growth order;
* `κ`: the patch-measure exponent;
* `σ`: the vanishing order of the multiplier or normal residual.

This file formalizes the exponent bookkeeping independently of the geometric,
multiplier-pairing, and Sobolev estimates that provide those parameters.
-/

/-- Exponent produced by the coefficient clipping repair. -/
def repairExponent (q β κ : ℝ) : ℝ := β - 1 + κ / q

/-- Exponent produced after taking the `q`-root of multiplier consistency when
the multiplier density does not contribute an additional vanishing order. -/
def multiplierExponent (q β κ : ℝ) : ℝ := (β + κ) / q

/-- Multiplier exponent including an additional multiplier/residual vanishing
order `σ`. -/
def multiplierVanishingExponent (q β κ σ : ℝ) : ℝ :=
  (β + κ + σ) / q

/-- The interface rate is governed by the slower of repair and multiplier
consistency. -/
def grandInterfaceExponent (q β κ : ℝ) : ℝ :=
  min (repairExponent q β κ) (multiplierExponent q β κ)

/-- Full defect–geometry–duality interface exponent with multiplier vanishing. -/
def grandInterfaceVanishingExponent (q β κ σ : ℝ) : ℝ :=
  min (repairExponent q β κ) (multiplierVanishingExponent q β κ σ)

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

/-- The full vanishing-aware law specializes to `3/2` when `σ = 0`. -/
theorem threeHalvesContactLaw_with_zero_multiplierVanishing :
    grandInterfaceVanishingExponent 2 2 1 0 = (3 : ℝ) / 2 := by
  norm_num [grandInterfaceVanishingExponent, repairExponent,
    multiplierVanishingExponent]

/-- The contact-growth order balancing the two mechanisms when `σ = 0`. -/
def balancedContactOrder (q : ℝ) : ℝ := q / (q - 1)

/-- The contact-growth order balancing repair and multiplier consistency when
the multiplier/residual vanishes to order `σ`. -/
def balancedContactOrderWithVanishing (q σ : ℝ) : ℝ :=
  (q + σ) / (q - 1)

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

/-- **Vanishing-aware Balanced Contact Exponent Principle.** For `q ≠ 0,1`,
`β = (q+σ)/(q-1)` equalizes the repair exponent and the multiplier exponent
with vanishing order `σ`. The patch exponent `κ` cancels. -/
theorem balancedContactOrderWithVanishing_equalizes
    (q κ σ : ℝ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    repairExponent q (balancedContactOrderWithVanishing q σ) κ =
      multiplierVanishingExponent q
        (balancedContactOrderWithVanishing q σ) κ σ := by
  have hqsub : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  unfold repairExponent multiplierVanishingExponent
    balancedContactOrderWithVanishing
  field_simp [hq0, hqsub]
  ring

/-- Quadratic energy has balanced contact order two when `σ = 0`. -/
theorem balancedContactOrder_two :
    balancedContactOrder 2 = (2 : ℝ) := by
  norm_num [balancedContactOrder]

/-- The vanishing-aware balanced order reduces to the original balanced order
when `σ = 0`. -/
theorem balancedContactOrderWithVanishing_zero (q : ℝ) :
    balancedContactOrderWithVanishing q 0 = balancedContactOrder q := by
  simp [balancedContactOrderWithVanishing, balancedContactOrder]

end

end BernsteinObstacle
