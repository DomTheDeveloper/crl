import Checkerboard.Geometry
import Checkerboard.FiniteContradictions

/-!
# Assembly of the three checkerboard parity cases
-/

namespace Checkerboard

open scoped BigOperators

/-- The odd-board fat color cannot have exactly `2n-3` points. -/
theorem oddFat_target_impossible (m : ℕ) (hm : 3 ≤ m)
    (S : Finset (Board (2 * m + 1)))
    (hmono : Monochromatic 0 S) (hntil : NoThreeInLine S)
    (hcard : S.card = 2 * (2 * m + 1) - 3) : False := by
  let n := 2 * m + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have huMod : ∀ p ∈ S, uRaw p % 2 = 0 := by
    intro p hp
    simpa using uRaw_mod_two hmono p hp
  have hvMod : ∀ p ∈ S, vRaw n p % 2 = 0 := by
    intro p hp
    rw [show n = 2 * m + 1 by rfl, vRaw_mod_two_odd]
    exact huMod p hp
  let D : ℝ := 8 * (m : ℝ) * (2 * (m : ℝ) ^ 2 + 1) / 3
  refine profile_q1_impossible
    n n n S xCoord yCoord
    (fun p => uRaw p / 2) (fun p => vRaw n p / 2)
    (endpointCap n) (endpointCap n)
    (evenOffset n) (evenOffset n)
    D D ((2 * (m : ℝ)) ^ 2) ((2 * (m : ℝ)) ^ 2)
    hn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [n] using hcard
  · intro p hp
    exact p.1.2
  · intro p hp
    exact p.2.2
  · intro p hp
    have hle := uRaw_le_rawMax hn p
    have hmod := huMod p hp
    dsimp [n, rawMax] at hle ⊢
    omega
  · intro p hp
    have hle := vRaw_le_rawMax hn p
    have hmod := hvMod p hp
    dsimp [n, rawMax] at hle ⊢
    omega
  · intro k hk
    simpa using xFiber_le_two hntil k
  · intro k hk
    simpa using yFiber_le_two hntil k
  · exact uEvenProfile_capacity hn hntil huMod
  · exact vEvenProfile_capacity hn hntil hvMod
  · simpa [n] using endpointCap_sum (N := n) (by omega)
  · simpa [n] using endpointCap_sum (N := n) (by omega)
  · simpa [n, evenOffset] using oddFat_capacity_first m (by omega)
  · simpa [n, evenOffset] using oddFat_capacity_first m (by omega)
  · simpa [D, n, evenOffset] using oddFat_capacity_second m (by omega)
  · simpa [D, n, evenOffset] using oddFat_capacity_second m (by omega)
  · intro p hp
    rw [evenOffset_div_two (huMod p hp), evenOffset_div_two (hvMod p hp)]
    exact rawOffsets_add hn p
  · intro p hp
    rw [evenOffset_div_two (huMod p hp), evenOffset_div_two (hvMod p hp)]
    exact rawOffsets_sub hn p
  · intro k hk
    simpa [n, evenOffset] using oddFat_offset_sq_le (Finset.mem_range.mp hk)
  · intro k hk
    simpa [n, evenOffset] using oddFat_offset_sq_le (Finset.mem_range.mp hk)
  · have hg := oddFat_radius_gap (n := 2 * (m : ℝ) + 1) (by
      exact_mod_cast (show 7 ≤ 2 * m + 1 by omega))
    dsimp [D, n]
    push_cast
    convert hg using 1 <;> ring

/-- The odd-board thin color cannot have exactly `2n-3` points. -/
theorem oddThin_target_impossible (m : ℕ) (hm : 3 ≤ m)
    (S : Finset (Board (2 * m + 1)))
    (hmono : Monochromatic 1 S) (hntil : NoThreeInLine S)
    (hcard : S.card = 2 * (2 * m + 1) - 3) : False := by
  let n := 2 * m + 1
  let N := 2 * m
  have hn : 1 ≤ n := by dsimp [n]; omega
  have huMod : ∀ p ∈ S, uRaw p % 2 = 1 := by
    intro p hp
    simpa using uRaw_mod_two hmono p hp
  have hvMod : ∀ p ∈ S, vRaw n p % 2 = 1 := by
    intro p hp
    rw [show n = 2 * m + 1 by rfl, vRaw_mod_two_odd]
    exact huMod p hp
  let D : ℝ :=
    4 * (m : ℝ) * (2 * (m : ℝ) - 1) * (2 * (m : ℝ) + 1) / 3
  refine profile_q1_impossible
    n N N S xCoord yCoord
    (fun p => uRaw p / 2) (fun p => vRaw n p / 2)
    (doubleCap N) (doubleCap N)
    (oddOffset n) (oddOffset n)
    D D ((2 * (m : ℝ) - 1) ^ 2) ((2 * (m : ℝ) - 1) ^ 2)
    hn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [n] using hcard
  · intro p hp
    exact p.1.2
  · intro p hp
    exact p.2.2
  · intro p hp
    have hle := uRaw_le_rawMax hn p
    have hmod := huMod p hp
    dsimp [n, N, rawMax] at hle ⊢
    omega
  · intro p hp
    have hle := vRaw_le_rawMax hn p
    have hmod := hvMod p hp
    dsimp [n, N, rawMax] at hle ⊢
    omega
  · intro k hk
    simpa using xFiber_le_two hntil k
  · intro k hk
    simpa using yFiber_le_two hntil k
  · exact uOddProfile_capacity hntil huMod
  · exact vOddProfile_capacity hn hntil hvMod
  · simpa [n, N] using doubleCap_sum N
  · simpa [n, N] using doubleCap_sum N
  · simpa [N, n, oddOffset] using oddThin_capacity_first m
  · simpa [N, n, oddOffset] using oddThin_capacity_first m
  · simpa [D, N, n, oddOffset] using oddThin_capacity_second m
  · simpa [D, N, n, oddOffset] using oddThin_capacity_second m
  · intro p hp
    rw [oddOffset_div_two (huMod p hp), oddOffset_div_two (hvMod p hp)]
    exact rawOffsets_add hn p
  · intro p hp
    rw [oddOffset_div_two (huMod p hp), oddOffset_div_two (hvMod p hp)]
    exact rawOffsets_sub hn p
  · intro k hk
    simpa [N, n, oddOffset] using oddThin_offset_sq_le (Finset.mem_range.mp hk)
  · intro k hk
    simpa [N, n, oddOffset] using oddThin_offset_sq_le (Finset.mem_range.mp hk)
  · have hg := oddThin_radius_gap (n := 2 * (m : ℝ) + 1) (by
      exact_mod_cast (show 7 ≤ 2 * m + 1 by omega))
    dsimp [D, N, n]
    push_cast
    convert hg using 1 <;> ring

/-- On an even board, color zero has endpoint `U` and all-double `V`. -/
theorem evenZero_target_impossible (m : ℕ) (hm : 3 ≤ m)
    (S : Finset (Board (2 * m)))
    (hmono : Monochromatic 0 S) (hntil : NoThreeInLine S)
    (hcard : S.card = 2 * (2 * m) - 3) : False := by
  let n := 2 * m
  let Nodd := 2 * m - 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have huMod : ∀ p ∈ S, uRaw p % 2 = 0 := by
    intro p hp
    simpa using uRaw_mod_two hmono p hp
  have hvMod : ∀ p ∈ S, vRaw n p % 2 = 1 := by
    intro p hp
    rw [show n = 2 * m by rfl, vRaw_mod_two_even]
    have hc := hmono p hp
    simp [pointColor] at hc
    omega
  let DE : ℝ :=
    2 * (2 * (m : ℝ) - 1) *
      (4 * (m : ℝ) ^ 2 - 4 * (m : ℝ) + 3) / 3
  let DO : ℝ :=
    8 * (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 3
  refine profile_q1_impossible
    n n Nodd S xCoord yCoord
    (fun p => uRaw p / 2) (fun p => vRaw n p / 2)
    (endpointCap n) (doubleCap Nodd)
    (evenOffset n) (oddOffset n)
    DE DO ((2 * (m : ℝ) - 1) ^ 2) ((2 * (m : ℝ) - 2) ^ 2)
    hn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [n] using hcard
  · intro p hp
    exact p.1.2
  · intro p hp
    exact p.2.2
  · intro p hp
    have hle := uRaw_le_rawMax hn p
    have hmod := huMod p hp
    dsimp [n, rawMax] at hle ⊢
    omega
  · intro p hp
    have hle := vRaw_le_rawMax hn p
    have hmod := hvMod p hp
    dsimp [n, Nodd, rawMax] at hle ⊢
    omega
  · intro k hk
    simpa using xFiber_le_two hntil k
  · intro k hk
    simpa using yFiber_le_two hntil k
  · exact uEvenProfile_capacity hn hntil huMod
  · exact vOddProfile_capacity hn hntil hvMod
  · simpa [n] using endpointCap_sum (N := n) (by omega)
  · simpa [n, Nodd] using doubleCap_sum Nodd
  · simpa [n, evenOffset] using evenEndpoint_capacity_first m (by omega)
  · simpa [n, Nodd, oddOffset] using evenDouble_capacity_first m (by omega)
  · simpa [DE, n, evenOffset] using evenEndpoint_capacity_second m (by omega)
  · simpa [DO, n, Nodd, oddOffset] using evenDouble_capacity_second m (by omega)
  · intro p hp
    rw [evenOffset_div_two (huMod p hp), oddOffset_div_two (hvMod p hp)]
    exact rawOffsets_add hn p
  · intro p hp
    rw [evenOffset_div_two (huMod p hp), oddOffset_div_two (hvMod p hp)]
    exact rawOffsets_sub hn p
  · intro k hk
    simpa [n, evenOffset] using evenEndpoint_offset_sq_le (Finset.mem_range.mp hk)
  · intro k hk
    simpa [n, Nodd, oddOffset] using
      evenDouble_offset_sq_le (m := m) (by omega) (Finset.mem_range.mp hk)
  · have hg := even_radius_gap (n := 2 * (m : ℝ)) (by
      exact_mod_cast (show 6 ≤ 2 * m by omega))
    dsimp [DE, DO, Nodd, n]
    push_cast
    convert hg using 1 <;> ring

/-- On an even board, color one has all-double `U` and endpoint `V`. -/
theorem evenOne_target_impossible (m : ℕ) (hm : 3 ≤ m)
    (S : Finset (Board (2 * m)))
    (hmono : Monochromatic 1 S) (hntil : NoThreeInLine S)
    (hcard : S.card = 2 * (2 * m) - 3) : False := by
  let n := 2 * m
  let Nodd := 2 * m - 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have huMod : ∀ p ∈ S, uRaw p % 2 = 1 := by
    intro p hp
    simpa using uRaw_mod_two hmono p hp
  have hvMod : ∀ p ∈ S, vRaw n p % 2 = 0 := by
    intro p hp
    rw [show n = 2 * m by rfl, vRaw_mod_two_even]
    have hc := hmono p hp
    simp [pointColor] at hc
    omega
  let DE : ℝ :=
    2 * (2 * (m : ℝ) - 1) *
      (4 * (m : ℝ) ^ 2 - 4 * (m : ℝ) + 3) / 3
  let DO : ℝ :=
    8 * (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 3
  refine profile_q1_impossible
    n Nodd n S xCoord yCoord
    (fun p => uRaw p / 2) (fun p => vRaw n p / 2)
    (doubleCap Nodd) (endpointCap n)
    (oddOffset n) (evenOffset n)
    DO DE ((2 * (m : ℝ) - 2) ^ 2) ((2 * (m : ℝ) - 1) ^ 2)
    hn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [n] using hcard
  · intro p hp
    exact p.1.2
  · intro p hp
    exact p.2.2
  · intro p hp
    have hle := uRaw_le_rawMax hn p
    have hmod := huMod p hp
    dsimp [n, Nodd, rawMax] at hle ⊢
    omega
  · intro p hp
    have hle := vRaw_le_rawMax hn p
    have hmod := hvMod p hp
    dsimp [n, rawMax] at hle ⊢
    omega
  · intro k hk
    simpa using xFiber_le_two hntil k
  · intro k hk
    simpa using yFiber_le_two hntil k
  · exact uOddProfile_capacity hntil huMod
  · exact vEvenProfile_capacity hn hntil hvMod
  · simpa [n, Nodd] using doubleCap_sum Nodd
  · simpa [n] using endpointCap_sum (N := n) (by omega)
  · simpa [n, Nodd, oddOffset] using evenDouble_capacity_first m (by omega)
  · simpa [n, evenOffset] using evenEndpoint_capacity_first m (by omega)
  · simpa [DO, n, Nodd, oddOffset] using evenDouble_capacity_second m (by omega)
  · simpa [DE, n, evenOffset] using evenEndpoint_capacity_second m (by omega)
  · intro p hp
    rw [oddOffset_div_two (huMod p hp), evenOffset_div_two (hvMod p hp)]
    exact rawOffsets_add hn p
  · intro p hp
    rw [oddOffset_div_two (huMod p hp), evenOffset_div_two (hvMod p hp)]
    exact rawOffsets_sub hn p
  · intro k hk
    simpa [n, Nodd, oddOffset] using
      evenDouble_offset_sq_le (m := m) (by omega) (Finset.mem_range.mp hk)
  · intro k hk
    simpa [n, evenOffset] using evenEndpoint_offset_sq_le (Finset.mem_range.mp hk)
  · have hg := even_radius_gap (n := 2 * (m : ℝ)) (by
      exact_mod_cast (show 6 ≤ 2 * m by omega))
    dsimp [DE, DO, Nodd, n]
    push_cast
    convert hg using 1 <;> ring

end Checkerboard
