import BernsteinObstacle.CoefficientCone
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

namespace BernsteinObstacle

/-!
# Strict coefficient clearance certificates

A smooth recovery used in the obstacle argument is first given a strict
coefficient margin.  If every recovered coefficient stays closer than that
margin to the target coefficient, exact Bernstein feasibility follows.  These
lemmas provide the concrete finite-dimensional discharge of the clearance
premise used by `ClearanceSobolevFEMRecoveryData`.
-/

section CoefficientClearance

variable {ι : Type*}

/-- A coefficient vector with lower margin `delta` remains in the nonnegative
orthant under any coordinatewise perturbation of absolute size less than
`delta`. -/
theorem mem_coefficientCone_of_margin_of_abs_sub_lt
    (target candidate : ι → ℝ) (delta : ℝ)
    (hmargin : ∀ i, delta ≤ target i)
    (hclose : ∀ i, |candidate i - target i| < delta) :
    candidate ∈ coefficientCone ι := by
  intro i
  have hlower : -delta < candidate i - target i :=
    (abs_lt.mp (hclose i)).1
  linarith [hmargin i]

/-- A strict lower and upper coefficient margin survives every coordinatewise
perturbation smaller than that margin.  This is the bilateral box analogue of
the nonnegative-cone clearance lemma. -/
theorem coefficient_mem_Icc_of_margin_of_abs_sub_lt
    (lower upper target candidate : ι → ℝ) (delta : ℝ)
    (hlower : ∀ i, lower i + delta ≤ target i)
    (hupper : ∀ i, target i + delta ≤ upper i)
    (hclose : ∀ i, |candidate i - target i| < delta) :
    ∀ i, candidate i ∈ Set.Icc (lower i) (upper i) := by
  intro i
  have hneg : -delta < candidate i - target i :=
    (abs_lt.mp (hclose i)).1
  have hpos : candidate i - target i < delta :=
    (abs_lt.mp (hclose i)).2
  constructor <;> linarith [hlower i, hupper i]

/-- Constant lower and upper coefficient barriers are preserved by a strict
interior margin and a smaller coordinatewise perturbation. -/
theorem coefficient_mem_Icc_const_of_margin_of_abs_sub_lt
    (lower upper : ℝ) (target candidate : ι → ℝ) (delta : ℝ)
    (hlower : ∀ i, lower + delta ≤ target i)
    (hupper : ∀ i, target i + delta ≤ upper)
    (hclose : ∀ i, |candidate i - target i| < delta) :
    ∀ i, candidate i ∈ Set.Icc lower upper := by
  exact coefficient_mem_Icc_of_margin_of_abs_sub_lt
    (fun _ => lower) (fun _ => upper) target candidate delta
    hlower hupper hclose

end CoefficientClearance

section FiniteCoefficientClearance

variable {ι : Type*} [Fintype ι]

/-- For a finite Bernstein coefficient vector, a strict sup-norm recovery bound
below the positive coefficient margin certifies exact nonnegativity. -/
theorem mem_coefficientCone_of_margin_of_norm_sub_lt
    (target candidate : ι → ℝ) (delta : ℝ)
    (hdelta : 0 < delta)
    (hmargin : ∀ i, delta ≤ target i)
    (hclose : ‖candidate - target‖ < delta) :
    candidate ∈ coefficientCone ι := by
  apply mem_coefficientCone_of_margin_of_abs_sub_lt target candidate delta hmargin
  intro i
  have hi : ‖(candidate - target) i‖ < delta :=
    (pi_norm_lt_iff hdelta).1 hclose i
  simpa [Real.norm_eq_abs] using hi

/-- For finite coefficient vectors, a strict sup-norm recovery bound below a
two-sided margin certifies every bilateral coefficient box constraint. -/
theorem coefficient_mem_Icc_of_margin_of_norm_sub_lt
    (lower upper target candidate : ι → ℝ) (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ i, lower i + delta ≤ target i)
    (hupper : ∀ i, target i + delta ≤ upper i)
    (hclose : ‖candidate - target‖ < delta) :
    ∀ i, candidate i ∈ Set.Icc (lower i) (upper i) := by
  apply coefficient_mem_Icc_of_margin_of_abs_sub_lt
    lower upper target candidate delta hlower hupper
  intro i
  have hi : ‖(candidate - target) i‖ < delta :=
    (pi_norm_lt_iff hdelta).1 hclose i
  simpa [Real.norm_eq_abs] using hi

/-- Constant bilateral Bernstein boxes are preserved whenever the finite
coefficient-vector sup-norm error is smaller than the strict interior margin. -/
theorem coefficient_mem_Icc_const_of_margin_of_norm_sub_lt
    (lower upper : ℝ) (target candidate : ι → ℝ) (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ i, lower + delta ≤ target i)
    (hupper : ∀ i, target i + delta ≤ upper)
    (hclose : ‖candidate - target‖ < delta) :
    ∀ i, candidate i ∈ Set.Icc lower upper := by
  exact coefficient_mem_Icc_of_margin_of_norm_sub_lt
    (fun _ => lower) (fun _ => upper) target candidate delta
    hdelta hlower hupper hclose

/-- A positive margin is required only on movable coefficients.  Coefficients
outside `free` may be trace-fixed or otherwise certified separately.  This is
the physically relevant unilateral clearance theorem for conforming elements
with exact boundary coefficients. -/
theorem mem_coefficientCone_of_margin_on_free_of_norm_sub_lt
    (free : Set ι) (target candidate : ι → ℝ) (delta : ℝ)
    (hdelta : 0 < delta)
    (hmargin : ∀ i, i ∈ free → delta ≤ target i)
    (hfixed : ∀ i, i ∉ free → 0 ≤ candidate i)
    (hclose : ‖candidate - target‖ < delta) :
    candidate ∈ coefficientCone ι := by
  intro i
  by_cases hi : i ∈ free
  · have hcoord : |candidate i - target i| < delta := by
      have hnorm : ‖(candidate - target) i‖ < delta :=
        (pi_norm_lt_iff hdelta).1 hclose i
      simpa [Real.norm_eq_abs] using hnorm
    have hlower : -delta < candidate i - target i :=
      (abs_lt.mp hcoord).1
    linarith [hmargin i hi]
  · exact hfixed i hi

/-- Bilateral free coefficients need strict lower and upper margins, while
trace-fixed or otherwise protected coefficients outside `free` may be certified
separately. -/
theorem coefficient_mem_Icc_of_margin_on_free_of_norm_sub_lt
    (free : Set ι) (lower upper target candidate : ι → ℝ) (delta : ℝ)
    (hdelta : 0 < delta)
    (hlower : ∀ i, i ∈ free → lower i + delta ≤ target i)
    (hupper : ∀ i, i ∈ free → target i + delta ≤ upper i)
    (hfixed : ∀ i, i ∉ free → candidate i ∈ Set.Icc (lower i) (upper i))
    (hclose : ‖candidate - target‖ < delta) :
    ∀ i, candidate i ∈ Set.Icc (lower i) (upper i) := by
  intro i
  by_cases hi : i ∈ free
  · have hcoord : |candidate i - target i| < delta := by
      have hnorm : ‖(candidate - target) i‖ < delta :=
        (pi_norm_lt_iff hdelta).1 hclose i
      simpa [Real.norm_eq_abs] using hnorm
    have hneg : -delta < candidate i - target i :=
      (abs_lt.mp hcoord).1
    have hpos : candidate i - target i < delta :=
      (abs_lt.mp hcoord).2
    constructor <;> linarith [hlower i hi, hupper i hi]
  · exact hfixed i hi

/-- Exact preservation of nonnegative trace-fixed coefficients discharges the
non-free side of the unilateral free-coefficient theorem. -/
theorem mem_coefficientCone_of_margin_on_free_of_fixed_eq
    (free : Set ι) (target candidate : ι → ℝ) (delta : ℝ)
    (hdelta : 0 < delta)
    (hmargin : ∀ i, i ∈ free → delta ≤ target i)
    (htargetFixed : ∀ i, i ∉ free → 0 ≤ target i)
    (hfixed : ∀ i, i ∉ free → candidate i = target i)
    (hclose : ‖candidate - target‖ < delta) :
    candidate ∈ coefficientCone ι := by
  apply mem_coefficientCone_of_margin_on_free_of_norm_sub_lt
    free target candidate delta hdelta hmargin
  · intro i hi
    rw [hfixed i hi]
    exact htargetFixed i hi
  · exact hclose

end FiniteCoefficientClearance

end BernsteinObstacle
