import Checkerboard.CapacityProfiles
import Checkerboard.MasterAlgebra

/-!
# Deficit moment algebra
-/

namespace Checkerboard

open scoped BigOperators

theorem exists_unique_one_of_sum_eq_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℕ) (hsum : ∑ i in s, w i = 1) :
    ∃ a ∈ s, w a = 1 ∧ ∀ b ∈ s, b ≠ a → w b = 0 := by
  have hex : ∃ a ∈ s, w a ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : ∑ i in s, w i = 0 := Finset.sum_eq_zero fun i hi => h i hi
    omega
  obtain ⟨a, ha, hwa⟩ := hex
  have hle : w a ≤ ∑ i in s, w i :=
    Finset.single_le_sum (fun i hi => Nat.zero_le (w i)) ha
  have hwa1 : w a = 1 := by omega
  have herase : ∑ i in s.erase a, w i = 0 := by
    have hsplit := Finset.sum_erase_add (s := s) (f := w) ha
    omega
  refine ⟨a, ha, hwa1, ?_⟩
  intro b hb hba
  have hbErase : b ∈ s.erase a := by simp [hb, hba]
  have hble : w b ≤ ∑ i in s.erase a, w i :=
    Finset.single_le_sum (fun i hi => Nat.zero_le (w i)) hbErase
  omega

theorem unitDeficit_moments {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℕ) (z : ι → ℝ)
    (hsum : ∑ i in s, w i = 1) :
    (∑ i in s, (w i : ℝ) * z i) ^ 2 =
      ∑ i in s, (w i : ℝ) * z i ^ 2 := by
  obtain ⟨a, ha, hwa, hzero⟩ := exists_unique_one_of_sum_eq_one s w hsum
  have hfirst : (∑ i in s, (w i : ℝ) * z i) = z a := by
    calc
      (∑ i in s, (w i : ℝ) * z i) = (w a : ℝ) * z a := by
        apply Finset.sum_eq_single_of_mem a ha
        intro b hb hba
        simp [hzero b hb hba]
      _ = z a := by simp [hwa]
  have hsecond : (∑ i in s, (w i : ℝ) * z i ^ 2) = z a ^ 2 := by
    calc
      (∑ i in s, (w i : ℝ) * z i ^ 2) = (w a : ℝ) * z a ^ 2 := by
        apply Finset.sum_eq_single_of_mem a ha
        intro b hb hba
        simp [hzero b hb hba]
      _ = z a ^ 2 := by simp [hwa]
  rw [hfirst, hsecond]

theorem unitDeficit_second_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℕ) (z : ι → ℝ) (R : ℝ)
    (hsum : ∑ i in s, w i = 1)
    (hradius : ∀ i ∈ s, z i ^ 2 ≤ R) :
    (∑ i in s, (w i : ℝ) * z i ^ 2) ≤ R := by
  obtain ⟨a, ha, hwa, hzero⟩ := exists_unique_one_of_sum_eq_one s w hsum
  have hsecond : (∑ i in s, (w i : ℝ) * z i ^ 2) = z a ^ 2 := by
    calc
      (∑ i in s, (w i : ℝ) * z i ^ 2) = (w a : ℝ) * z a ^ 2 := by
        apply Finset.sum_eq_single_of_mem a ha
        intro b hb hba
        simp [hzero b hb hba]
      _ = z a ^ 2 := by simp [hwa]
  rw [hsecond]
  exact hradius a ha

theorem q1_master_lower
    {ιc ιr ιu ιv : Type*}
    [DecidableEq ιc] [DecidableEq ιr] [DecidableEq ιu] [DecidableEq ιv]
    (sc : Finset ιc) (sr : Finset ιr) (su : Finset ιu) (sv : Finset ιv)
    (c : ιc → ℕ) (r : ιr → ℕ) (μ : ιu → ℕ) (ν : ιv → ℕ)
    (xc : ιc → ℝ) (yr : ιr → ℝ) (u : ιu → ℝ) (v : ιv → ℝ)
    (A : ℝ)
    (hcsum : ∑ i in sc, c i = 3)
    (hrsum : ∑ i in sr, r i = 3)
    (hmusum : ∑ i in su, μ i = 1)
    (hnusum : ∑ i in sv, ν i = 1)
    (hfirstC : (∑ i in sc, (c i : ℝ) * xc i) =
      (∑ i in su, (μ i : ℝ) * u i) +
      (∑ i in sv, (ν i : ℝ) * v i))
    (hfirstR : (∑ i in sr, (r i : ℝ) * yr i) =
      (∑ i in su, (μ i : ℝ) * u i) -
      (∑ i in sv, (ν i : ℝ) * v i))
    (hsecond :
      (∑ i in sc, (c i : ℝ) * xc i ^ 2) +
      (∑ i in sr, (r i : ℝ) * yr i ^ 2) =
      A + 2 * ((∑ i in su, (μ i : ℝ) * u i ^ 2) +
        (∑ i in sv, (ν i : ℝ) * v i ^ 2))) :
    -3 * A / 4 ≤
      (∑ i in su, (μ i : ℝ) * u i ^ 2) +
      (∑ i in sv, (ν i : ℝ) * v i ^ 2) := by
  have hcauchy := weightedCauchy sc (fun i => (c i : ℝ)) xc (by
    intro i hi
    positivity)
  have rcauchy := weightedCauchy sr (fun i => (r i : ℝ)) yr (by
    intro i hi
    positivity)
  have hccast : (∑ i in sc, (c i : ℝ)) = 3 := by exact_mod_cast hcsum
  have hrcast : (∑ i in sr, (r i : ℝ)) = 3 := by exact_mod_cast hrsum
  rw [hccast, hfirstC] at hcauchy
  rw [hrcast, hfirstR] at rcauchy
  have hmu := unitDeficit_moments su μ u hmusum
  have hnu := unitDeficit_moments sv ν v hnusum
  nlinarith [sumDiffSquares
    (∑ i in su, (μ i : ℝ) * u i)
    (∑ i in sv, (ν i : ℝ) * v i)]

end Checkerboard
