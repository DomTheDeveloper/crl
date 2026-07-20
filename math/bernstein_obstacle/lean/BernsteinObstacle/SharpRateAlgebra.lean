import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Algebra of the sharp free-boundary rate

The analytical estimates in the manuscript produce a bulk squared error of
order `h^(2*r)` and a free-boundary-strip squared error of order `hΓ^3`.
This file certifies the dimension-independent exponent cancellation and the
final coercive square-root transfer to

`h^r + hΓ * sqrt hΓ`,

which is the real-power expression for `h^r + hΓ^(3/2)`.
-/

/-- The codimension-one strip count cancels the ambient dimension:
`h^(d+2) / h^(d-1) = h^3`. -/
theorem strip_power_cancellation (h : ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hh : h ≠ 0) :
    h ^ (d + 2) / h ^ (d - 1) = h ^ 3 := by
  have hexp : d + 2 = (d - 1) + 3 := by omega
  rw [hexp, pow_add]
  field_simp [pow_ne_zero _ hh]

/-- The square of the three-halves scale is the cubic strip scale. -/
theorem threeHalvesScale_sq (g : ℝ) (hg : 0 ≤ g) :
    (g * Real.sqrt g) ^ 2 = g ^ 3 := by
  rw [mul_pow, Real.sq_sqrt hg]
  ring

/-- Equivalently, the square root of the cubic strip scale is the
three-halves scale. -/
theorem sqrt_cubic_eq_threeHalvesScale (g : ℝ) (hg : 0 ≤ g) :
    Real.sqrt (g ^ 3) = g * Real.sqrt g := by
  have hcubic : 0 ≤ g ^ 3 := pow_nonneg hg _
  have hsquare := Real.sq_sqrt hcubic
  have hscale := threeHalvesScale_sq g hg
  have hsqrt : 0 ≤ Real.sqrt (g ^ 3) := Real.sqrt_nonneg _
  have hright : 0 ≤ g * Real.sqrt g :=
    mul_nonneg hg (Real.sqrt_nonneg _)
  nlinarith

/-- Squaring the bulk scale `h^r` produces `h^(2*r)`. -/
theorem bulkScale_sq (h : ℝ) (r : ℕ) :
    (h ^ r) ^ 2 = h ^ (2 * r) := by
  calc
    (h ^ r) ^ 2 = h ^ (r + r) := by rw [pow_two, ← pow_add]
    _ = h ^ (2 * r) := by congr 1 <;> omega

/-- For nonnegative scales, the sum of squares is bounded by the square of the
sum. -/
theorem add_sq_le_sq_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith

/-- Bulk and strip squared-energy contributions imply the sharp norm rate.
The constant is explicit: `sqrt(max A B / α)`. -/
theorem sharpRate_of_energy_components
    (e α A B h g : ℝ) (r : ℕ)
    (he : 0 ≤ e) (hα : 0 < α)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (henergy :
      α * e ^ 2 ≤ A * h ^ (2 * r) + B * g ^ 3) :
    e ≤ Real.sqrt (max A B / α) *
      (h ^ r + g * Real.sqrt g) := by
  let a : ℝ := h ^ r
  let b : ℝ := g * Real.sqrt g
  let M : ℝ := max A B
  have ha : 0 ≤ a := by
    dsimp [a]
    exact pow_nonneg hh _
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg hg (Real.sqrt_nonneg _)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact hA.trans (le_max_left A B)
  have hbulk : h ^ (2 * r) = a ^ 2 := by
    dsimp [a]
    exact (bulkScale_sq h r).symm
  have hstrip : g ^ 3 = b ^ 2 := by
    dsimp [b]
    exact (threeHalvesScale_sq g hg).symm
  have hweighted :
      A * a ^ 2 + B * b ^ 2 ≤ M * (a ^ 2 + b ^ 2) := by
    calc
      A * a ^ 2 + B * b ^ 2 ≤ M * a ^ 2 + M * b ^ 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left A B) (sq_nonneg a))
          (mul_le_mul_of_nonneg_right (le_max_right A B) (sq_nonneg b))
      _ = M * (a ^ 2 + b ^ 2) := by ring
  have hsquares : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 :=
    add_sq_le_sq_add a b ha hb
  have hcoercive : α * e ^ 2 ≤ M * (a + b) ^ 2 := by
    calc
      α * e ^ 2 ≤ A * a ^ 2 + B * b ^ 2 := by
        simpa [hbulk, hstrip] using henergy
      _ ≤ M * (a ^ 2 + b ^ 2) := hweighted
      _ ≤ M * (a + b) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquares hM
  have hdiv : e ^ 2 ≤ (M / α) * (a + b) ^ 2 := by
    have htmp : e ^ 2 ≤ (M * (a + b) ^ 2) / α := by
      apply (le_div_iff₀ hα).2
      simpa [mul_comm] using hcoercive
    calc
      e ^ 2 ≤ (M * (a + b) ^ 2) / α := htmp
      _ = (M / α) * (a + b) ^ 2 := by ring
  have hratio : 0 ≤ M / α :=
    div_nonneg hM (le_of_lt hα)
  have hsqrtSq : (Real.sqrt (M / α)) ^ 2 = M / α :=
    Real.sq_sqrt hratio
  have hrhsNonneg :
      0 ≤ Real.sqrt (M / α) * (a + b) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg ha hb)
  have hsquareBound :
      e ^ 2 ≤ (Real.sqrt (M / α) * (a + b)) ^ 2 := by
    calc
      e ^ 2 ≤ (M / α) * (a + b) ^ 2 := hdiv
      _ = (Real.sqrt (M / α) * (a + b)) ^ 2 := by
        rw [mul_pow, hsqrtSq]
  have hfinal : e ≤ Real.sqrt (M / α) * (a + b) := by
    nlinarith
  simpa [a, b, M] using hfinal

end BernsteinObstacle
