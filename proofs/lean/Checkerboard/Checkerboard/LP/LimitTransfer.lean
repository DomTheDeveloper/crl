import Checkerboard.LP.FiniteModel
import Checkerboard.LP.AlgebraicParameter

/-!
# Normalization and bounded-error limit transfers

These lemmas isolate the elementary limit arguments used after the analytic
continuum-to-finite estimates have been proved.  In particular, an `O(1)`
difference between symmetry classes disappears after division by the side
length, and replacing `2m+1` by `2m` does not change a finite normalized limit.
-/

namespace Checkerboard

noncomputable section

open Filter
open scoped Topology

/-- The odd side length, viewed as a real normalization factor. -/
def oddScale (m : ℕ) : ℝ := 2 * (m : ℝ) + 1

/-- The even side length, viewed as a real normalization factor. -/
def evenScale (m : ℕ) : ℝ := 2 * (m : ℝ)

lemma oddScale_pos (m : ℕ) : 0 < oddScale m := by
  simp [oddScale]
  positivity

lemma oddScale_tendsto_atTop : Tendsto oddScale atTop atTop := by
  have hmul : Tendsto (fun m : ℕ => (2 : ℝ) * (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  simpa [oddScale] using Filter.tendsto_atTop_add_const_right atTop 1 hmul

lemma evenScale_tendsto_atTop : Tendsto evenScale atTop atTop := by
  simpa [evenScale] using
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)

/-- A uniformly bounded numerator divided by an odd side length tends to zero. -/
theorem bounded_div_oddScale_tendsto_zero
    (r : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hr : ∀ m, |r m| ≤ C) :
    Tendsto (fun m => r m / oddScale m) atTop (𝓝 0) := by
  have hupper : Tendsto (fun m => C / oddScale m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop oddScale_tendsto_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hupper.neg hupper ?_ ?_
  · intro m
    have habs := (abs_le.mp (hr m)).1
    exact (div_le_div_iff_of_pos_right (oddScale_pos m)).2 habs
  · intro m
    have habs := (abs_le.mp (hr m)).2
    exact (div_le_div_iff_of_pos_right (oddScale_pos m)).2 habs

/-- An `O(1)` perturbation does not change an odd-side normalized limit. -/
theorem tendsto_div_oddScale_of_bounded_sub
    {f g : ℕ → ℝ} {a C : ℝ}
    (hf : Tendsto (fun m => f m / oddScale m) atTop (𝓝 a))
    (hC : 0 ≤ C) (hfg : ∀ m, |g m - f m| ≤ C) :
    Tendsto (fun m => g m / oddScale m) atTop (𝓝 a) := by
  have hrem : Tendsto (fun m => (g m - f m) / oddScale m) atTop (𝓝 0) :=
    bounded_div_oddScale_tendsto_zero (fun m => g m - f m) C hC hfg
  have hsum := hf.add hrem
  have hcongr :
      (fun m => f m / oddScale m + (g m - f m) / oddScale m) =ᶠ[atTop]
        (fun m => g m / oddScale m) := by
    filter_upwards with m
    ring
  simpa using hsum.congr' hcongr

/-- A uniformly bounded numerator divided by an even side length tends to zero.
The denominator is positive eventually; its value at `m=0` is irrelevant.
-/
theorem bounded_div_evenScale_tendsto_zero
    (r : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hr : ∀ m, |r m| ≤ C) :
    Tendsto (fun m => r m / evenScale m) atTop (𝓝 0) := by
  have hupper : Tendsto (fun m => C / evenScale m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop evenScale_tendsto_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hupper.neg hupper ?_ ?_
  · filter_upwards [evenScale_tendsto_atTop.eventually_gt_atTop 0] with m hm
    have habs := (abs_le.mp (hr m)).1
    exact (div_le_div_iff_of_pos_right hm).2 habs
  · filter_upwards [evenScale_tendsto_atTop.eventually_gt_atTop 0] with m hm
    have habs := (abs_le.mp (hr m)).2
    exact (div_le_div_iff_of_pos_right hm).2 habs

/-- The ratio `(2m+1)/(2m)` tends to one. -/
lemma oddScale_div_evenScale_tendsto_one :
    Tendsto (fun m => oddScale m / evenScale m) atTop (𝓝 1) := by
  have hinv : Tendsto (fun m => (1 : ℝ) / evenScale m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop evenScale_tendsto_atTop
  have hadd : Tendsto (fun m => (1 : ℝ) + 1 / evenScale m) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hinv
  have hcongr :
      (fun m => (1 : ℝ) + 1 / evenScale m) =ᶠ[atTop]
        (fun m => oddScale m / evenScale m) := by
    filter_upwards [evenScale_tendsto_atTop.eventually_ne_atTop 0] with m hm
    field_simp [oddScale, evenScale, hm]
    ring
  simpa using hadd.congr' hcongr

/-- Replacing the odd normalization by the neighbouring even normalization
preserves a finite limit. -/
theorem tendsto_div_evenScale_of_tendsto_div_oddScale
    {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto (fun m => f m / oddScale m) atTop (𝓝 a)) :
    Tendsto (fun m => f m / evenScale m) atTop (𝓝 a) := by
  have hmul := hf.mul oddScale_div_evenScale_tendsto_one
  have hcongr :
      (fun m => (f m / oddScale m) * (oddScale m / evenScale m)) =ᶠ[atTop]
        (fun m => f m / evenScale m) := by
    filter_upwards [evenScale_tendsto_atTop.eventually_ne_atTop 0] with m hm
    have ho : oddScale m ≠ 0 := ne_of_gt (oddScale_pos m)
    field_simp [hm, ho]
    ring
  simpa using hmul.congr' hcongr

/-- An `O(1)` perturbation also disappears with even normalization. -/
theorem tendsto_div_evenScale_of_bounded_sub
    {f g : ℕ → ℝ} {a C : ℝ}
    (hf : Tendsto (fun m => f m / evenScale m) atTop (𝓝 a))
    (hC : 0 ≤ C) (hfg : ∀ m, |g m - f m| ≤ C) :
    Tendsto (fun m => g m / evenScale m) atTop (𝓝 a) := by
  have hrem : Tendsto (fun m => (g m - f m) / evenScale m) atTop (𝓝 0) :=
    bounded_div_evenScale_tendsto_zero (fun m => g m - f m) C hC hfg
  have hsum := hf.add hrem
  have hcongr :
      (fun m => f m / evenScale m + (g m - f m) / evenScale m) =ᶠ[atTop]
        (fun m => g m / evenScale m) := by
    filter_upwards with m
    ring
  simpa using hsum.congr' hcongr

/-- The odd-thin limit follows from the odd-fat limit and a uniform additive
comparison. -/
theorem oddThin_limit_of_oddFat_limit
    {C : ℝ}
    (hfat : Tendsto (fun m => oddFatL4 m / oddScale m) atTop (𝓝 checkerboardAlpha))
    (hC : 0 ≤ C)
    (hcompare : ∀ m, |oddThinL4 m - oddFatL4 m| ≤ C) :
    Tendsto (fun m => oddThinL4 m / oddScale m) atTop (𝓝 checkerboardAlpha) :=
  tendsto_div_oddScale_of_bounded_sub hfat hC hcompare

/-- The even limit follows from the odd-fat limit and a uniform comparison with
the neighbouring odd-fat optimum. -/
theorem even_limit_of_oddFat_limit
    {C : ℝ}
    (hfat : Tendsto (fun m => oddFatL4 m / oddScale m) atTop (𝓝 checkerboardAlpha))
    (hC : 0 ≤ C)
    (hcompare : ∀ m, |evenL4 m - oddFatL4 m| ≤ C) :
    Tendsto (fun m => evenL4 m / evenScale m) atTop (𝓝 checkerboardAlpha) := by
  apply tendsto_div_evenScale_of_bounded_sub
    (tendsto_div_evenScale_of_tendsto_div_oddScale hfat) hC hcompare

end

end Checkerboard
