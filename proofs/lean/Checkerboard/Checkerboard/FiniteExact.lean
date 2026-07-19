import Checkerboard.Model

/-!
# Exact finite checkerboard certificates

The explicit constructions and exact rational four-direction dual profiles are
replayed inside Lean.  All arithmetic checks use `decide`; no external solver,
floating-point arithmetic, `native_decide`, or unfinished proof marker is used.
-/

namespace Checkerboard

private def axisWeight (n : ℕ) (axis : List ℕ) (index : ℕ) : ℕ :=
  if index < n then axis.getD (min index (n - 1 - index)) 0 else 0

/-- Lift a symmetric odd-board axis/diagonal profile to all principal lines. -/
private def oddProfileWeight (n parity : ℕ) (axis diagonal : List ℕ)
    (line : PrincipalLine n) : ℕ :=
  let index := line.2.1
  let p := parity % 2
  match line.1 with
  | .row => axisWeight n axis index
  | .column => axisWeight n axis index
  | .sum =>
      let folded := min index (2 * n - 2 - index)
      if index % 2 = p then diagonal.getD ((folded - p) / 2) 0 else 0
  | .difference =>
      let distance := Nat.dist index (n - 1)
      if distance % 2 = p then
        diagonal.getD ((n - 1) / 2 - (distance + p) / 2) 0
      else 0

private def n17p0Weight : PrincipalLine 17 → ℕ :=
  oddProfileWeight 17 0
    [20, 14, 9, 5, 2, 0, 0, 0, 0]
    [0, 0, 10, 18, 24, 29, 35, 38, 39]

private def n17p1Weight : PrincipalLine 17 → ℕ :=
  oddProfileWeight 17 1
    [12, 9, 6, 4, 2, 1, 0, 0, 0]
    [0, 0, 5, 9, 12, 15, 17, 18]

private theorem n17p0_cost : certificateCost n17p0Weight = 1788 := by decide
private theorem n17p1_cost : certificateCost n17p1Weight = 880 := by decide

private theorem n17p0_cover :
    ∀ p : Point 17, InColor 0 p → 67 ≤ coverage n17p0Weight p := by
  decide

private theorem n17p1_cover :
    ∀ p : Point 17, InColor 1 p → 33 ≤ coverage n17p1Weight p := by
  decide

/-- The stored 26-point construction in the fat color class of the 17-board. -/
def n17p0Construction : Finset (Point 17) :=
  {((0 : Fin 17), (10 : Fin 17)),
   ((0 : Fin 17), (12 : Fin 17)),
   ((1 : Fin 17), (3 : Fin 17)),
   ((1 : Fin 17), (15 : Fin 17)),
   ((2 : Fin 17), (4 : Fin 17)),
   ((2 : Fin 17), (8 : Fin 17)),
   ((3 : Fin 17), (11 : Fin 17)),
   ((4 : Fin 17), (0 : Fin 17)),
   ((4 : Fin 17), (16 : Fin 17)),
   ((5 : Fin 17), (1 : Fin 17)),
   ((5 : Fin 17), (3 : Fin 17)),
   ((6 : Fin 17), (14 : Fin 17)),
   ((6 : Fin 17), (16 : Fin 17)),
   ((7 : Fin 17), (1 : Fin 17)),
   ((7 : Fin 17), (11 : Fin 17)),
   ((11 : Fin 17), (15 : Fin 17)),
   ((12 : Fin 17), (0 : Fin 17)),
   ((12 : Fin 17), (2 : Fin 17)),
   ((13 : Fin 17), (5 : Fin 17)),
   ((13 : Fin 17), (13 : Fin 17)),
   ((14 : Fin 17), (2 : Fin 17)),
   ((14 : Fin 17), (14 : Fin 17)),
   ((15 : Fin 17), (9 : Fin 17)),
   ((15 : Fin 17), (13 : Fin 17)),
   ((16 : Fin 17), (6 : Fin 17)),
   ((16 : Fin 17), (8 : Fin 17))}

/-- The stored 26-point construction in the thin color class of the 17-board. -/
def n17p1Construction : Finset (Point 17) :=
  {((0 : Fin 17), (3 : Fin 17)),
   ((0 : Fin 17), (5 : Fin 17)),
   ((1 : Fin 17), (10 : Fin 17)),
   ((1 : Fin 17), (12 : Fin 17)),
   ((2 : Fin 17), (5 : Fin 17)),
   ((2 : Fin 17), (9 : Fin 17)),
   ((3 : Fin 17), (14 : Fin 17)),
   ((3 : Fin 17), (16 : Fin 17)),
   ((4 : Fin 17), (1 : Fin 17)),
   ((5 : Fin 17), (2 : Fin 17)),
   ((5 : Fin 17), (12 : Fin 17)),
   ((7 : Fin 17), (16 : Fin 17)),
   ((8 : Fin 17), (1 : Fin 17)),
   ((9 : Fin 17), (0 : Fin 17)),
   ((10 : Fin 17), (11 : Fin 17)),
   ((10 : Fin 17), (15 : Fin 17)),
   ((11 : Fin 17), (4 : Fin 17)),
   ((12 : Fin 17), (13 : Fin 17)),
   ((13 : Fin 17), (0 : Fin 17)),
   ((13 : Fin 17), (2 : Fin 17)),
   ((14 : Fin 17), (9 : Fin 17)),
   ((14 : Fin 17), (13 : Fin 17)),
   ((15 : Fin 17), (4 : Fin 17)),
   ((15 : Fin 17), (6 : Fin 17)),
   ((16 : Fin 17), (11 : Fin 17)),
   ((16 : Fin 17), (15 : Fin 17))}

private theorem n17p0Construction_valid :
    Monochromatic 0 n17p0Construction ∧
      NoThreeInLine n17p0Construction ∧ n17p0Construction.card = 26 := by
  decide

private theorem n17p1Construction_valid :
    Monochromatic 1 n17p1Construction ∧
      NoThreeInLine n17p1Construction ∧ n17p1Construction.card = 26 := by
  decide

/-- Exact upper bound for the fat color class of the 17-board. -/
theorem n17p0_upper (s : Finset (Point 17))
    (hcolor : Monochromatic 0 s) (hntil : NoThreeInLine s) : s.card ≤ 26 := by
  apply card_le_of_certificate n17p0Weight (q := 67) (parity := 0)
      (k := 26) (by decide) ?_ n17p0_cover hcolor hntil
  rw [n17p0_cost]
  norm_num

/-- Exact upper bound for the thin color class of the 17-board. -/
theorem n17p1_upper (s : Finset (Point 17))
    (hcolor : Monochromatic 1 s) (hntil : NoThreeInLine s) : s.card ≤ 26 := by
  apply card_le_of_certificate n17p1Weight (q := 33) (parity := 1)
      (k := 26) (by decide) ?_ n17p1_cover hcolor hntil
  rw [n17p1_cost]
  norm_num

/-- `D_mono(17,0)=26`, stated as an exact maximum theorem. -/
theorem exact_n17_p0 : IsExactMaximum 17 0 26 := by
  constructor
  · exact ⟨n17p0Construction, n17p0Construction_valid.1,
      n17p0Construction_valid.2.1, n17p0Construction_valid.2.2⟩
  · intro s hcolor hntil
    exact n17p0_upper s hcolor hntil

/-- `D_mono(17,1)=26`, stated as an exact maximum theorem. -/
theorem exact_n17_p1 : IsExactMaximum 17 1 26 := by
  constructor
  · exact ⟨n17p1Construction, n17p1Construction_valid.1,
      n17p1Construction_valid.2.1, n17p1Construction_valid.2.2⟩
  · intro s hcolor hntil
    exact n17p1_upper s hcolor hntil

end Checkerboard
