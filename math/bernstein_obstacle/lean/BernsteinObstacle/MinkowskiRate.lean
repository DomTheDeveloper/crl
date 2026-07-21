import BernsteinObstacle.StripScaling
import Mathlib.Tactic

open scoped BigOperators

namespace BernsteinObstacle

/-!
# Vanishing-order/codimension repair law

Suppose a clipping correction has coefficient amplitude `O(h^q)` near a
geometric defect set of codimension `c`. On a shape-regular `d`-simplex its
squared `H^1` cost scales like `h^(2*(q-1)+d)`. A locally quasi-uniform patch
around a codimension-`c` set contains `O(h^(-(d-c)))` elements. Consequently
the global squared repair cost is `O(h^(2*(q-1)+c))`.
-/

noncomputable def vanishingCodimensionScale (h : ℝ) (q c : ℕ) : ℝ :=
  h ^ (q - 1) * Real.sqrt (h ^ c)

theorem vanishingCodimensionScale_nonneg (h : ℝ) (q c : ℕ) (hh : 0 ≤ h) :
    0 ≤ vanishingCodimensionScale h q c := by
  exact mul_nonneg (pow_nonneg hh _) (Real.sqrt_nonneg _)

theorem vanishingCodimensionScale_sq (h : ℝ) (q c : ℕ) (hh : 0 ≤ h) :
    (vanishingCodimensionScale h q c) ^ 2 =
      h ^ (2 * (q - 1) + c) := by
  unfold vanishingCodimensionScale
  rw [mul_pow, Real.sq_sqrt (pow_nonneg hh _), bulkScale_sq]
  rw [← pow_add]

theorem vanishingCodimension_power_cancellation
    (h : ℝ) (d q c : ℕ) (hc : c ≤ d) (hh : h ≠ 0) :
    h ^ (2 * (q - 1) + d) / h ^ (d - c) =
      h ^ (2 * (q - 1) + c) := by
  have hexp :
      2 * (q - 1) + d = (d - c) + (2 * (q - 1) + c) := by
    omega
  rw [hexp, pow_add]
  field_simp [pow_ne_zero _ hh]

theorem strip_sum_energy_le_vanishingCodimension
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (C N h : ℝ) (d q c : ℕ)
    (hc : c ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (henergy :
      ∀ i ∈ S, energy i ≤ C * h ^ (2 * (q - 1) + d))
    (hcard : (S.card : ℝ) ≤ N / h ^ (d - c)) :
    ∑ i ∈ S, energy i ≤ C * N * h ^ (2 * (q - 1) + c) := by
  have hpow : 0 ≤ h ^ (2 * (q - 1) + d) :=
    pow_nonneg (le_of_lt hh) _
  have hq : 0 ≤ C * h ^ (2 * (q - 1) + d) := mul_nonneg hC hpow
  calc
    ∑ i ∈ S, energy i ≤
        (S.card : ℝ) * (C * h ^ (2 * (q - 1) + d)) :=
      sum_le_card_mul_of_le S energy
        (C * h ^ (2 * (q - 1) + d)) henergy
    _ ≤ (N / h ^ (d - c)) *
        (C * h ^ (2 * (q - 1) + d)) :=
      mul_le_mul_of_nonneg_right hcard hq
    _ = C * N *
        (h ^ (2 * (q - 1) + d) / h ^ (d - c)) := by ring
    _ = C * N * h ^ (2 * (q - 1) + c) := by
      rw [vanishingCodimension_power_cancellation h d q c hc (ne_of_gt hh)]

theorem repair_norm_le_vanishingCodimension
    (e C N h : ℝ) (q c : ℕ)
    (he : 0 ≤ e) (hC : 0 ≤ C) (hN : 0 ≤ N) (hh : 0 ≤ h)
    (hsq : e ^ 2 ≤ C * N * h ^ (2 * (q - 1) + c)) :
    e ≤ Real.sqrt (C * N) * vanishingCodimensionScale h q c := by
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  have hscale : 0 ≤ vanishingCodimensionScale h q c :=
    vanishingCodimensionScale_nonneg h q c hh
  have hrhs :
      0 ≤ Real.sqrt (C * N) * vanishingCodimensionScale h q c :=
    mul_nonneg (Real.sqrt_nonneg _) hscale
  have hsquare :
      (Real.sqrt (C * N) * vanishingCodimensionScale h q c) ^ 2 =
        C * N * h ^ (2 * (q - 1) + c) := by
    rw [mul_pow, Real.sq_sqrt hCN, vanishingCodimensionScale_sq h q c hh]
  have hbound :
      e ^ 2 ≤
        (Real.sqrt (C * N) * vanishingCodimensionScale h q c) ^ 2 := by
    calc
      e ^ 2 ≤ C * N * h ^ (2 * (q - 1) + c) := hsq
      _ = (Real.sqrt (C * N) * vanishingCodimensionScale h q c) ^ 2 :=
        hsquare.symm
  nlinarith

theorem repair_norm_le_vanishingCodimension_of_element_bounds
    {ι : Type*} (S : Finset ι) (energy : ι → ℝ)
    (e C N h : ℝ) (d q c : ℕ)
    (he : 0 ≤ e) (hc : c ≤ d) (hh : 0 < h)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (herror : e ^ 2 ≤ ∑ i ∈ S, energy i)
    (henergy :
      ∀ i ∈ S, energy i ≤ C * h ^ (2 * (q - 1) + d))
    (hcard : (S.card : ℝ) ≤ N / h ^ (d - c)) :
    e ≤ Real.sqrt (C * N) * vanishingCodimensionScale h q c := by
  have hsum := strip_sum_energy_le_vanishingCodimension
    S energy C N h d q c hc hh hC hN henergy hcard
  exact repair_norm_le_vanishingCodimension
    e C N h q c he hC hN (le_of_lt hh) (herror.trans hsum)

theorem vanishingCodimensionScale_quadratic_codimOne
    (h : ℝ) :
    vanishingCodimensionScale h 2 1 = h * Real.sqrt h := by
  simp [vanishingCodimensionScale]

theorem sharpRate_of_vanishingCodimension_components
    (e α A B h g : ℝ) (r q c : ℕ)
    (he : 0 ≤ e) (hα : 0 < α)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 ≤ h) (hg : 0 ≤ g)
    (henergy :
      α * e ^ 2 ≤
        A * h ^ (2 * r) + B * g ^ (2 * (q - 1) + c)) :
    e ≤ Real.sqrt (max A B / α) *
      (h ^ r + vanishingCodimensionScale g q c) := by
  let a : ℝ := h ^ r
  let b : ℝ := vanishingCodimensionScale g q c
  let M : ℝ := max A B
  have ha : 0 ≤ a := by
    dsimp [a]
    exact pow_nonneg hh _
  have hb : 0 ≤ b := by
    dsimp [b]
    exact vanishingCodimensionScale_nonneg g q c hg
  have hM : 0 ≤ M := by
    dsimp [M]
    exact hA.trans (le_max_left A B)
  have hbulk : h ^ (2 * r) = a ^ 2 := by
    dsimp [a]
    exact (bulkScale_sq h r).symm
  have hdefect : g ^ (2 * (q - 1) + c) = b ^ 2 := by
    dsimp [b]
    exact (vanishingCodimensionScale_sq g q c hg).symm
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
        simpa [hbulk, hdefect] using henergy
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
  have hratio : 0 ≤ M / α := div_nonneg hM (le_of_lt hα)
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
