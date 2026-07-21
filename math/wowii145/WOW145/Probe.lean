import WOW146.ExceptionalTheorem
import FormalConjectures.WrittenOnTheWallII.GraphConjecture145

/-! API probes used by the WOWII 145 proof package. -/

open Classical SimpleGraph
open WrittenOnTheWallII.GraphConjecture145

#check Finset.inf'_le
#check Finset.le_inf'
#check Finset.exists_mem_eq_inf'
#check SimpleGraph.IsIndepSet.card_le_indepNum
#check WOW146.exceptional_case
#check SimpleGraph.eccSet_periphery_add_one_le_diam
#check SimpleGraph.diam_succ_le_largestInducedTreeSize
#check SimpleGraph.diam_le_two_mul_radius_toNat
#check SimpleGraph.Connected.dist_triangle
#check SimpleGraph.dist_le
