import BernsteinObstacle.ContactAwareRecovery
import BernsteinObstacle.GlobalSmoothSaturation
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

noncomputable section

/-!
# Physical one-dimensional quadratic contact on mapped cells

This file instantiates the coefficient algebra on the physical affine cell
`x = a + h t`.  It proves the exact degree-`p` Bernstein representation of
`x^2`, identifies the phase-locked negative coefficient on the central cell of
an odd uniform mesh, and constructs the globally conforming inward repair
`(x^2+d)/(1+d)`.
-/

/-- Affine reference-to-physical map for a one-dimensional cell. -/
def affineCellMap (a h t : ℝ) : ℝ := a + h * t

/-- Exact degree-`p` Bernstein coefficients of `x^2` on the physical cell
`x = a + h t`. -/
def xSquaredCellCoeff (p k : ℕ) (a h : ℝ) : ℝ :=
  a ^ 2 + 2 * a * h * ((k : ℝ) / (p : ℝ)) +
    h ^ 2 * quadraticMonomialCoeff p k

/-- The physical coefficient formula represents the actual function `x ↦ x^2`
exactly on every affine cell. -/
theorem xSquaredCellCoeff_curve_eq
    (p : ℕ) (hp : 2 ≤ p) (a h t : ℝ) :
    curve p (fun k => xSquaredCellCoeff p k a h) t =
      (affineCellMap a h t) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have h0 := basis_sum_eq_one p t
  have h1 := basis_firstMoment p t
  have h2 :
      (∑ k ∈ Finset.range (p + 1),
        quadraticMonomialCoeff p k * basis p k t) = t ^ 2 := by
    simpa [curve] using quadraticMonomial_eq_bernsteinCurve p hp t
  unfold curve xSquaredCellCoeff affineCellMap
  calc
    (∑ k ∈ Finset.range (p + 1),
        (a ^ 2 + 2 * a * h * ((k : ℝ) / (p : ℝ)) +
          h ^ 2 * quadraticMonomialCoeff p k) * basis p k t) =
        a ^ 2 * (∑ k ∈ Finset.range (p + 1), basis p k t) +
          (2 * a * h / (p : ℝ)) *
            (∑ k ∈ Finset.range (p + 1), (k : ℝ) * basis p k t) +
          h ^ 2 *
            (∑ k ∈ Finset.range (p + 1),
              quadraticMonomialCoeff p k * basis p k t) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = a ^ 2 * 1 + (2 * a * h / (p : ℝ)) * ((p : ℝ) * t) +
          h ^ 2 * t ^ 2 := by rw [h0, h1, h2]
    _ = (a + h * t) ^ 2 := by field_simp [hp0]; ring

/-- Physical central-cell coefficients on `[-h/2,h/2]`. -/
def centralPhysicalCoeff (p k : ℕ) (h : ℝ) : ℝ :=
  xSquaredCellCoeff p k (-h / 2) h

/-- The central physical coefficient is `h^2` times the normalized centered
quadratic coefficient. -/
theorem centralPhysicalCoeff_eq
    (p k : ℕ) (h : ℝ) :
    centralPhysicalCoeff p k h = h ^ 2 * centeredQuadraticCoeff p k := by
  unfold centralPhysicalCoeff xSquaredCellCoeff centeredQuadraticCoeff
  ring

/-- Even-degree phase-locked central coefficient. -/
theorem centralPhysicalCoeff_even_center
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) :
    centralPhysicalCoeff (2 * m) m h =
      -(h ^ 2) / (4 * (((2 * m : ℕ) : ℝ) - 1)) := by
  rw [centralPhysicalCoeff_eq, centeredQuadraticCoeff_even_center m hm]
  ring

/-- Odd-degree phase-locked central coefficient. -/
theorem centralPhysicalCoeff_odd_center
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) :
    centralPhysicalCoeff (2 * m + 1) m h =
      -(h ^ 2) / (4 * ((2 * m + 1 : ℕ) : ℝ)) := by
  rw [centralPhysicalCoeff_eq, centeredQuadraticCoeff_odd_center m hm]
  ring

/-- The even-degree physical central coefficient is strictly negative on every
nondegenerate cell. -/
theorem centralPhysicalCoeff_even_center_neg
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) (hh : h ≠ 0) :
    centralPhysicalCoeff (2 * m) m h < 0 := by
  rw [centralPhysicalCoeff_even_center m hm h]
  have hnum : 0 < h ^ 2 := sq_pos_of_ne_zero hh
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 4 * (((2 * m : ℕ) : ℝ) - 1) := by
    push_cast
    nlinarith
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden

/-- The odd-degree physical central coefficient is strictly negative on every
nondegenerate cell. -/
theorem centralPhysicalCoeff_odd_center_neg
    (m : ℕ) (hm : 1 ≤ m) (h : ℝ) (hh : h ≠ 0) :
    centralPhysicalCoeff (2 * m + 1) m h < 0 := by
  rw [centralPhysicalCoeff_odd_center m hm h]
  have hnum : 0 < h ^ 2 := sq_pos_of_ne_zero hh
  have hden : 0 < 4 * ((2 * m + 1 : ℕ) : ℝ) := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden

/-- Coefficients of the global inward-repair polynomial. -/
def physicalRepairCoeff (p k : ℕ) (a h d : ℝ) : ℝ :=
  inwardBlend d (xSquaredCellCoeff p k a h)

/-- The inward-repaired coefficients represent the same global polynomial
`(x^2+d)/(1+d)` on every cell.  Therefore the construction is conforming across
all interfaces automatically. -/
theorem physicalRepairCoeff_curve_eq
    (p : ℕ) (hp : 2 ≤ p) (a h d t : ℝ) (hd : 0 ≤ d) :
    curve p (fun k => physicalRepairCoeff p k a h d) t =
      ((affineCellMap a h t) ^ 2 + d) / (1 + d) := by
  have hden : 1 + d ≠ 0 := by positivity
  have hx := xSquaredCellCoeff_curve_eq p hp a h t
  have h0 := basis_sum_eq_one p t
  unfold curve physicalRepairCoeff
  simp_rw [inwardBlend_eq _ _ hd]
  calc
    (∑ k ∈ Finset.range (p + 1),
        ((xSquaredCellCoeff p k a h + d) / (1 + d)) * basis p k t) =
        (1 / (1 + d)) *
          ((∑ k ∈ Finset.range (p + 1),
              xSquaredCellCoeff p k a h * basis p k t) +
            d * (∑ k ∈ Finset.range (p + 1), basis p k t)) := by
      rw [Finset.mul_add, Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      field_simp [hden]
      ring
    _ = (1 / (1 + d)) * ((affineCellMap a h t) ^ 2 + d * 1) := by
      rw [hx, h0]
    _ = ((affineCellMap a h t) ^ 2 + d) / (1 + d) := by
      field_simp [hden]

/-- Every coefficient in `[-d,1]` is mapped into `[0,1]` by the physical repair. -/
theorem physicalRepairCoeff_mem_Icc
    (p k : ℕ) (a h d : ℝ) (hd : 0 ≤ d)
    (hb : xSquaredCellCoeff p k a h ∈ Set.Icc (-d) 1) :
    physicalRepairCoeff p k a h d ∈ Set.Icc 0 1 := by
  exact inwardBlend_mem_Icc d (xSquaredCellCoeff p k a h) hd hb

/-- The global repair preserves the exact Dirichlet values at both endpoints. -/
theorem physicalQuadraticRepair_endpoint
    (d x : ℝ) (hd : 0 ≤ d) (hx : x = -1 ∨ x = 1) :
    (x ^ 2 + d) / (1 + d) = 1 := by
  have hden : 1 + d ≠ 0 := by positivity
  rcases hx with rfl | rfl <;> field_simp [hden]

end

end BernsteinObstacle
