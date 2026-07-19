import Checkerboard.AllNTheorem
import Checkerboard.FiniteExact
import Checkerboard.N21Exact

/-!
# Axiom audit

Expected output for each theorem is limited to Mathlib's standard foundational
axioms (`propext`, `Quot.sound`, and `Classical.choice` where used). In
particular, `sorryAx` must not occur.
-/

#print axioms Checkerboard.exact_n17_p0
#print axioms Checkerboard.exact_n17_p1
#print axioms Checkerboard.exact_n21_p0
#print axioms Checkerboard.exact_n21_p1
#print axioms Checkerboard.checkerboard_upper_all_n
