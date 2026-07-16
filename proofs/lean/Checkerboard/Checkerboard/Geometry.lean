import Checkerboard.ProfileLemmas
import Checkerboard.MomentBridge

/-!
# Checkerboard geometry and four principal line families
-/

namespace Checkerboard

open scoped BigOperators

def lineCount {n : ℕ} (S : Finset (Board n)) (A B C : ℤ) : ℕ :=
  (S.filter fun p => A * (xCoord p : ℤ) + B * (yCoord p : ℤ) = C).card

def NoThreeInLine {n : ℕ} (S : Finset (Board n)) : Prop :=
  ∀ A B C : ℤ, A ≠ 0 ∨ B ≠ 0 → lineCount S A B C ≤ 2

theorem NoThreeInLine.mono {n : ℕ} {S T : Finset (Board n)}
    (hS : NoThreeInLine S) (hTS : T ⊆ S) : NoThreeInLine T := by
  intro A B C hAB
  exact le_trans (Finset.card_le_card (by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hTS hp.1, hp.2⟩)) (hS A B C hAB)

theorem Monochromatic.mono {n ε : ℕ} {S T : Finset (Board n)}
    (hS : Monochromatic ε S) (hTS : T ⊆ S) : Monochromatic ε T := by
  intro p hp
  exact hS p (hTS hp)

def uRaw {n : ℕ} (p : Board n) : ℕ := xCoord p + yCoord p

def vRaw (n : ℕ) (p : Board n) : ℕ := xCoord p + (n - 1) - yCoord p

def rawMax (n : ℕ) : ℕ := 2 * n - 2

theorem uRaw_le_rawMax {n : ℕ} (hn : 1 ≤ n) (p : Board n) :
    uRaw p ≤ rawMax n := by
  have hx := p.1.2
  have hy := p.2.2
  simp only [uRaw, xCoord, yCoord, rawMax]
  omega

theorem vRaw_le_rawMax {n : ℕ} (hn : 1 ≤ n) (p : Board n) :
    vRaw n p ≤ rawMax n := by
  have hx := p.1.2
  have hy := p.2.2
  simp only [vRaw, xCoord, yCoord, rawMax]
  omega

theorem xFiber_le_two {n : ℕ} {S : Finset (Board n)}
    (hS : NoThreeInLine S) (k : ℕ) :
    fiberCard S xCoord k ≤ 2 := by
  have h := hS 1 0 (k : ℤ) (Or.inl (by norm_num))
  simpa [lineCount, fiberCard] using h

theorem yFiber_le_two {n : ℕ} {S : Finset (Board n)}
    (hS : NoThreeInLine S) (k : ℕ) :
    fiberCard S yCoord k ≤ 2 := by
  have h := hS 0 1 (k : ℤ) (Or.inr (by norm_num))
  simpa [lineCount, fiberCard] using h

theorem uRawFiber_le_two {n : ℕ} {S : Finset (Board n)}
    (hS : NoThreeInLine S) (k : ℕ) :
    fiberCard S uRaw k ≤ 2 := by
  have h := hS 1 1 (k : ℤ) (Or.inl (by norm_num))
  have heq :
      S.filter (fun p => uRaw p = k) =
        S.filter (fun p =>
          (1 : ℤ) * (xCoord p : ℤ) + (1 : ℤ) * (yCoord p : ℤ) = (k : ℤ)) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hu⟩
      refine ⟨hp, ?_⟩
      simp only [uRaw, xCoord, yCoord] at hu ⊢
      norm_num
      exact_mod_cast hu
    · rintro ⟨hp, hu⟩
      refine ⟨hp, ?_⟩
      simp only [uRaw, xCoord, yCoord] at hu ⊢
      norm_num at hu
      exact_mod_cast hu
  rw [fiberCard, heq]
  simpa [lineCount] using h

theorem vRawFiber_le_two {n : ℕ} (hn : 1 ≤ n) {S : Finset (Board n)}
    (hS : NoThreeInLine S) (k : ℕ) :
    fiberCard S (vRaw n) k ≤ 2 := by
  have h := hS 1 (-1) ((k : ℤ) - ((n : ℤ) - 1)) (Or.inl (by norm_num))
  have heq :
      S.filter (fun p => vRaw n p = k) =
        S.filter (fun p =>
          (1 : ℤ) * (xCoord p : ℤ) + (-1 : ℤ) * (yCoord p : ℤ) =
            (k : ℤ) - ((n : ℤ) - 1)) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hv⟩
      refine ⟨hp, ?_⟩
      have hx := p.1.2
      have hy := p.2.2
      simp only [vRaw, xCoord, yCoord] at hv ⊢
      omega
    · rintro ⟨hp, hv⟩
      refine ⟨hp, ?_⟩
      have hx := p.1.2
      have hy := p.2.2
      simp only [vRaw, xCoord, yCoord] at hv ⊢
      omega
  rw [fiberCard, heq]
  simpa [lineCount] using h

theorem fiberCard_div_two_eq {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (e k : ℕ) (he : e < 2)
    (hmod : ∀ p ∈ S, f p % 2 = e) :
    fiberCard S (fun p => f p / 2) k = fiberCard S f (2 * k + e) := by
  apply congrArg Finset.card
  ext p
  simp only [fiberCard, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hk⟩
    refine ⟨hp, ?_⟩
    have hm := hmod p hp
    omega
  · rintro ⟨hp, hk⟩
    refine ⟨hp, ?_⟩
    have hm := hmod p hp
    omega

theorem uRaw_zero_fiber_le_one {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (Board n)) : fiberCard S uRaw 0 ≤ 1 := by
  let z : Fin n := ⟨0, by omega⟩
  have hsub : S.filter (fun p => uRaw p = 0) ⊆ ({(z, z)} : Finset (Board n)) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hxy := hp.2
    have hp0 : p = (z, z) := by
      apply Prod.ext
      · apply Fin.ext
        simp only [uRaw, xCoord, yCoord] at hxy
        simp [z]
        omega
      · apply Fin.ext
        simp only [uRaw, xCoord, yCoord] at hxy
        simp [z]
        omega
    simpa [hp0]
  exact le_trans (Finset.card_le_card hsub) (by simp)

theorem uRaw_max_fiber_le_one {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (Board n)) : fiberCard S uRaw (rawMax n) ≤ 1 := by
  let l : Fin n := ⟨n - 1, by omega⟩
  have hsub : S.filter (fun p => uRaw p = rawMax n) ⊆
      ({(l, l)} : Finset (Board n)) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hxy := hp.2
    have hx := p.1.2
    have hy := p.2.2
    have hpl : p = (l, l) := by
      apply Prod.ext
      · apply Fin.ext
        simp only [uRaw, rawMax, xCoord, yCoord] at hxy
        simp [l]
        omega
      · apply Fin.ext
        simp only [uRaw, rawMax, xCoord, yCoord] at hxy
        simp [l]
        omega
    simpa [hpl]
  exact le_trans (Finset.card_le_card hsub) (by simp)

theorem vRaw_zero_fiber_le_one {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (Board n)) : fiberCard S (vRaw n) 0 ≤ 1 := by
  let z : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n - 1, by omega⟩
  have hsub : S.filter (fun p => vRaw n p = 0) ⊆
      ({(z, l)} : Finset (Board n)) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hv := hp.2
    have hx := p.1.2
    have hy := p.2.2
    have hpl : p = (z, l) := by
      apply Prod.ext
      · apply Fin.ext
        simp only [vRaw, xCoord, yCoord] at hv
        simp [z]
        omega
      · apply Fin.ext
        simp only [vRaw, xCoord, yCoord] at hv
        simp [l]
        omega
    simpa [hpl]
  exact le_trans (Finset.card_le_card hsub) (by simp)

theorem vRaw_max_fiber_le_one {n : ℕ} (hn : 1 ≤ n)
    (S : Finset (Board n)) : fiberCard S (vRaw n) (rawMax n) ≤ 1 := by
  let z : Fin n := ⟨0, by omega⟩
  let l : Fin n := ⟨n - 1, by omega⟩
  have hsub : S.filter (fun p => vRaw n p = rawMax n) ⊆
      ({(l, z)} : Finset (Board n)) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    have hv := hp.2
    have hx := p.1.2
    have hy := p.2.2
    have hpl : p = (l, z) := by
      apply Prod.ext
      · apply Fin.ext
        simp only [vRaw, rawMax, xCoord, yCoord] at hv
        simp [l]
        omega
      · apply Fin.ext
        simp only [vRaw, rawMax, xCoord, yCoord] at hv
        simp [z]
        omega
    simpa [hpl]
  exact le_trans (Finset.card_le_card hsub) (by simp)

theorem uEvenProfile_capacity {n : ℕ} (hn : 1 ≤ n)
    {S : Finset (Board n)} (hS : NoThreeInLine S)
    (hmod : ∀ p ∈ S, uRaw p % 2 = 0)
    (k : ℕ) (hk : k ∈ Finset.range n) :
    fiberCard S (fun p => uRaw p / 2) k ≤ endpointCap n k := by
  rw [fiberCard_div_two_eq S uRaw 0 k (by omega) hmod]
  by_cases he : k = 0 ∨ k + 1 = n
  · rw [endpointCap, if_pos he]
    rcases he with rfl | he
    · simpa using uRaw_zero_fiber_le_one hn S
    · have hkLast : k = n - 1 := by omega
      rw [hkLast]
      have hraw : 2 * (n - 1) = rawMax n := by simp [rawMax]; omega
      rw [hraw]
      exact uRaw_max_fiber_le_one hn S
  · rw [endpointCap, if_neg he]
    exact uRawFiber_le_two hS (2 * k)

theorem uOddProfile_capacity {n N : ℕ} {S : Finset (Board n)}
    (hS : NoThreeInLine S)
    (hmod : ∀ p ∈ S, uRaw p % 2 = 1)
    (k : ℕ) (hk : k ∈ Finset.range N) :
    fiberCard S (fun p => uRaw p / 2) k ≤ doubleCap N k := by
  rw [fiberCard_div_two_eq S uRaw 1 k (by omega) hmod]
  simpa [doubleCap] using uRawFiber_le_two hS (2 * k + 1)

theorem vEvenProfile_capacity {n : ℕ} (hn : 1 ≤ n)
    {S : Finset (Board n)} (hS : NoThreeInLine S)
    (hmod : ∀ p ∈ S, vRaw n p % 2 = 0)
    (k : ℕ) (hk : k ∈ Finset.range n) :
    fiberCard S (fun p => vRaw n p / 2) k ≤ endpointCap n k := by
  rw [fiberCard_div_two_eq S (vRaw n) 0 k (by omega) hmod]
  by_cases he : k = 0 ∨ k + 1 = n
  · rw [endpointCap, if_pos he]
    rcases he with rfl | he
    · simpa using vRaw_zero_fiber_le_one hn S
    · have hkLast : k = n - 1 := by omega
      rw [hkLast]
      have hraw : 2 * (n - 1) = rawMax n := by simp [rawMax]; omega
      rw [hraw]
      exact vRaw_max_fiber_le_one hn S
  · rw [endpointCap, if_neg he]
    exact vRawFiber_le_two hn hS (2 * k)

theorem vOddProfile_capacity {n N : ℕ} (hn : 1 ≤ n)
    {S : Finset (Board n)} (hS : NoThreeInLine S)
    (hmod : ∀ p ∈ S, vRaw n p % 2 = 1)
    (k : ℕ) (hk : k ∈ Finset.range N) :
    fiberCard S (fun p => vRaw n p / 2) k ≤ doubleCap N k := by
  rw [fiberCard_div_two_eq S (vRaw n) 1 k (by omega) hmod]
  simpa [doubleCap] using vRawFiber_le_two hn hS (2 * k + 1)

theorem uRaw_mod_two {n ε : ℕ} {S : Finset (Board n)}
    (hmono : Monochromatic ε S) (p : Board n) (hp : p ∈ S) :
    uRaw p % 2 = ε % 2 := by
  simpa [uRaw, pointColor] using hmono p hp

theorem vRaw_mod_two_odd (m : ℕ) (p : Board (2 * m + 1)) :
    vRaw (2 * m + 1) p % 2 = pointColor p := by
  have hx := p.1.2
  have hy := p.2.2
  simp only [vRaw, pointColor, xCoord, yCoord]
  omega

theorem vRaw_mod_two_even (m : ℕ) (p : Board (2 * m)) :
    vRaw (2 * m) p % 2 = (pointColor p + 1) % 2 := by
  have hx := p.1.2
  have hy := p.2.2
  simp only [vRaw, pointColor, xCoord, yCoord]
  omega

def evenOffset (n k : ℕ) : ℝ := 2 * (k : ℝ) - ((n : ℝ) - 1)

def oddOffset (n k : ℕ) : ℝ := 2 * (k : ℝ) + 1 - ((n : ℝ) - 1)

theorem evenOffset_div_two {n a : ℕ} (ha : a % 2 = 0) :
    evenOffset n (a / 2) = (a : ℝ) - ((n : ℝ) - 1) := by
  have hnat : 2 * (a / 2) = a := by omega
  have hreal : 2 * ((a / 2 : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast hnat
  unfold evenOffset
  linarith

theorem oddOffset_div_two {n a : ℕ} (ha : a % 2 = 1) :
    oddOffset n (a / 2) = (a : ℝ) - ((n : ℝ) - 1) := by
  have hnat : 2 * (a / 2) + 1 = a := by omega
  have hreal : 2 * ((a / 2 : ℕ) : ℝ) + 1 = (a : ℝ) := by exact_mod_cast hnat
  unfold oddOffset
  linarith

theorem rawOffsets_add {n : ℕ} (hn : 1 ≤ n) (p : Board n) :
    centered2Nat n (xCoord p) =
      ((uRaw p : ℝ) - ((n : ℝ) - 1)) +
        ((vRaw n p : ℝ) - ((n : ℝ) - 1)) := by
  have hx := p.1.2
  have hy := p.2.2
  have hsub : yCoord p ≤ xCoord p + (n - 1) := by
    simp only [xCoord, yCoord]
    omega
  have hncast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hvcast : (vRaw n p : ℝ) =
      (xCoord p : ℝ) + ((n : ℝ) - 1) - (yCoord p : ℝ) := by
    rw [vRaw, Nat.cast_sub hsub]
    push_cast
    rw [hncast]
  rw [hvcast]
  simp [centered2Nat, uRaw]
  ring

theorem rawOffsets_sub {n : ℕ} (hn : 1 ≤ n) (p : Board n) :
    centered2Nat n (yCoord p) =
      ((uRaw p : ℝ) - ((n : ℝ) - 1)) -
        ((vRaw n p : ℝ) - ((n : ℝ) - 1)) := by
  have hx := p.1.2
  have hy := p.2.2
  have hsub : yCoord p ≤ xCoord p + (n - 1) := by
    simp only [xCoord, yCoord]
    omega
  have hncast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hvcast : (vRaw n p : ℝ) =
      (xCoord p : ℝ) + ((n : ℝ) - 1) - (yCoord p : ℝ) := by
    rw [vRaw, Nat.cast_sub hsub]
    push_cast
    rw [hncast]
  rw [hvcast]
  simp [centered2Nat, uRaw]
  ring

end Checkerboard
