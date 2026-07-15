import FormalConjectures.ErdosProblems.«1150»
import Erdos1150Final

open Complex
open scoped Polynomial

namespace Erdos1150Proof

/-- Exact signature check against `Erdos1150.erdos_1150.variants.parseval_lower_bound`. -/
theorem exact_formal_conjectures_statement (P : ℂ[X]) (n : ℕ)
    (hcoeff : ∀ i ≤ P.natDegree, P.coeff i = -1 ∨ P.coeff i = 1)
    (hdeg : P.natDegree = n) :
    ⨆ z : Metric.sphere (0 : ℂ) 1, ‖P.eval (z : ℂ)‖ ≥ Real.sqrt (n + 1) :=
  parseval_lower_bound P n hcoeff hdeg

#print axioms exact_formal_conjectures_statement

end Erdos1150Proof
