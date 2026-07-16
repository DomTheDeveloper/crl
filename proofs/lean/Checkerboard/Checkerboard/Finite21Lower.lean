import Checkerboard.Model

/-!
# Explicit 21×21 lower-bound certificates

These are the two 32-point constructions from the exact finite certificate
package. Lean checks checkerboard parity, cardinality, and every selected triple
using the integer determinant from `Checkerboard.Model`.
-/

namespace Checkerboard

/-- A 32-point no-three-in-line set in the fat color class of the 21-board. -/
def n21p0Construction : Finset (Point 21) :=
  {((0 : Fin 21), (6 : Fin 21)),
   ((0 : Fin 21), (10 : Fin 21)),
   ((1 : Fin 21), (13 : Fin 21)),
   ((1 : Fin 21), (15 : Fin 21)),
   ((2 : Fin 21), (0 : Fin 21)),
   ((2 : Fin 21), (18 : Fin 21)),
   ((3 : Fin 21), (1 : Fin 21)),
   ((3 : Fin 21), (9 : Fin 21)),
   ((4 : Fin 21), (4 : Fin 21)),
   ((4 : Fin 21), (8 : Fin 21)),
   ((5 : Fin 21), (17 : Fin 21)),
   ((6 : Fin 21), (2 : Fin 21)),
   ((6 : Fin 21), (20 : Fin 21)),
   ((7 : Fin 21), (15 : Fin 21)),
   ((7 : Fin 21), (17 : Fin 21)),
   ((9 : Fin 21), (1 : Fin 21)),
   ((11 : Fin 21), (19 : Fin 21)),
   ((13 : Fin 21), (3 : Fin 21)),
   ((13 : Fin 21), (5 : Fin 21)),
   ((14 : Fin 21), (0 : Fin 21)),
   ((14 : Fin 21), (18 : Fin 21)),
   ((15 : Fin 21), (3 : Fin 21)),
   ((16 : Fin 21), (12 : Fin 21)),
   ((16 : Fin 21), (16 : Fin 21)),
   ((17 : Fin 21), (11 : Fin 21)),
   ((17 : Fin 21), (19 : Fin 21)),
   ((18 : Fin 21), (2 : Fin 21)),
   ((18 : Fin 21), (20 : Fin 21)),
   ((19 : Fin 21), (5 : Fin 21)),
   ((19 : Fin 21), (7 : Fin 21)),
   ((20 : Fin 21), (10 : Fin 21)),
   ((20 : Fin 21), (14 : Fin 21))}

/-- A 32-point no-three-in-line set in the thin color class of the 21-board. -/
def n21p1Construction : Finset (Point 21) :=
  {((0 : Fin 21), (9 : Fin 21)),
   ((0 : Fin 21), (13 : Fin 21)),
   ((1 : Fin 21), (4 : Fin 21)),
   ((1 : Fin 21), (14 : Fin 21)),
   ((2 : Fin 21), (5 : Fin 21)),
   ((2 : Fin 21), (17 : Fin 21)),
   ((3 : Fin 21), (2 : Fin 21)),
   ((4 : Fin 21), (9 : Fin 21)),
   ((4 : Fin 21), (19 : Fin 21)),
   ((5 : Fin 21), (4 : Fin 21)),
   ((5 : Fin 21), (10 : Fin 21)),
   ((6 : Fin 21), (15 : Fin 21)),
   ((6 : Fin 21), (17 : Fin 21)),
   ((7 : Fin 21), (0 : Fin 21)),
   ((9 : Fin 21), (2 : Fin 21)),
   ((9 : Fin 21), (20 : Fin 21)),
   ((11 : Fin 21), (0 : Fin 21)),
   ((11 : Fin 21), (18 : Fin 21)),
   ((13 : Fin 21), (20 : Fin 21)),
   ((14 : Fin 21), (3 : Fin 21)),
   ((14 : Fin 21), (5 : Fin 21)),
   ((15 : Fin 21), (10 : Fin 21)),
   ((15 : Fin 21), (16 : Fin 21)),
   ((16 : Fin 21), (1 : Fin 21)),
   ((16 : Fin 21), (11 : Fin 21)),
   ((17 : Fin 21), (18 : Fin 21)),
   ((18 : Fin 21), (3 : Fin 21)),
   ((18 : Fin 21), (15 : Fin 21)),
   ((19 : Fin 21), (6 : Fin 21)),
   ((19 : Fin 21), (16 : Fin 21)),
   ((20 : Fin 21), (7 : Fin 21)),
   ((20 : Fin 21), (11 : Fin 21))}

/-- Fully kernel-checked validity of the fat 21×21 construction. -/
theorem n21p0Construction_valid :
    Monochromatic 0 n21p0Construction ∧
      NoThreeInLine n21p0Construction ∧ n21p0Construction.card = 32 := by
  decide

/-- Fully kernel-checked validity of the thin 21×21 construction. -/
theorem n21p1Construction_valid :
    Monochromatic 1 n21p1Construction ∧
      NoThreeInLine n21p1Construction ∧ n21p1Construction.card = 32 := by
  decide

/-- Constructive lower bound `32 ≤ D_mono(21,0)`. -/
theorem n21p0_lower :
    ∃ s : Finset (Point 21),
      Monochromatic 0 s ∧ NoThreeInLine s ∧ s.card = 32 := by
  exact ⟨n21p0Construction, n21p0Construction_valid.1,
    n21p0Construction_valid.2.1, n21p0Construction_valid.2.2⟩

/-- Constructive lower bound `32 ≤ D_mono(21,1)`. -/
theorem n21p1_lower :
    ∃ s : Finset (Point 21),
      Monochromatic 1 s ∧ NoThreeInLine s ∧ s.card = 32 := by
  exact ⟨n21p1Construction, n21p1Construction_valid.1,
    n21p1Construction_valid.2.1, n21p1Construction_valid.2.2⟩

end Checkerboard
