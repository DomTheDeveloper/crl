import Checkerboard.ParityCases
import Mathlib.Data.Finset.Powerset

namespace Checkerboard

theorem monochromatic_noThreeInLine_card_le
    (n ε : ℕ) (hn : 6 ≤ n) (S : Finset (Board n))
    (hmono : Monochromatic ε S) (hntil : NoThreeInLine S) :
    S.card ≤ 2 * n - 4 := by
  classical
  by_contra hbound
  have htarget : 2 * n - 3 ≤ S.card := by omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq htarget
  have hmonoT := hmono.mono hTS
  have hntilT := hntil.mono hTS
  have hepsLt : ε % 2 < 2 := Nat.mod_lt _ (by omega)
  have heps : ε % 2 = 0 ∨ ε % 2 = 1 := by omega
  by_cases hneven : n % 2 = 0
  · obtain ⟨m, hmEq⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    subst n
    have hm : 3 ≤ m := by omega
    rcases heps with heps | heps
    · have hmono0 : Monochromatic 0 T := by
        intro p hp
        have h := hmonoT p hp
        simpa [heps] using h
      exact evenZero_target_impossible m hm T hmono0 hntilT (by simpa using hTcard)
    · have hmono1 : Monochromatic 1 T := by
        intro p hp
        have h := hmonoT p hp
        simpa [heps] using h
      exact evenOne_target_impossible m hm T hmono1 hntilT (by simpa using hTcard)
  · have hnodd : n % 2 = 1 := by omega
    obtain ⟨m, hmEq⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    subst n
    have hm : 3 ≤ m := by omega
    rcases heps with heps | heps
    · have hmono0 : Monochromatic 0 T := by
        intro p hp
        have h := hmonoT p hp
        simpa [heps] using h
      exact oddFat_target_impossible m hm T hmono0 hntilT (by simpa using hTcard)
    · have hmono1 : Monochromatic 1 T := by
        intro p hp
        have h := hmonoT p hp
        simpa [heps] using h
      exact oddThin_target_impossible m hm T hmono1 hntilT (by simpa using hTcard)

noncomputable def DmonoColor (n ε : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).product (Finset.univ : Finset (Fin n))).powerset.sup fun S =>
    if Monochromatic ε S ∧ NoThreeInLine S then S.card else 0

noncomputable def Dmono (n : ℕ) : ℕ :=
  max (DmonoColor n 0) (DmonoColor n 1)

theorem DmonoColor_le (n ε : ℕ) (hn : 6 ≤ n) :
    DmonoColor n ε ≤ 2 * n - 4 := by
  classical
  unfold DmonoColor
  apply Finset.sup_le
  intro S hS
  by_cases hgood : Monochromatic ε S ∧ NoThreeInLine S
  · simp [hgood, monochromatic_noThreeInLine_card_le n ε hn S hgood.1 hgood.2]
  · simp [hgood]

theorem checkerboard_Dmono_le (n : ℕ) (hn : 6 ≤ n) :
    Dmono n ≤ 2 * n - 4 := by
  rw [Dmono, max_le_iff]
  exact ⟨DmonoColor_le n 0 hn, DmonoColor_le n 1 hn⟩

#print axioms Checkerboard.checkerboard_Dmono_le

end Checkerboard
