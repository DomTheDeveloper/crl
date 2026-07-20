import BernsteinObstacle.AssemblyConvex
import BernsteinObstacle.MoscoTools
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Order.OrderClosed

open Filter

namespace BernsteinObstacle

noncomputable section

/-!
# Mosco convergence of an assembled Bernstein feasible set

This file upgrades the concrete finite-dimensional Mosco theorem from the bare
nonnegative orthant to the actual assembled feasible set.  Weak limits preserve
each nonnegative coefficient and each homogeneous boundary equation, so the
assembled set is weakly sequentially closed.  Its constant family therefore
Mosco-converges to itself.
-/

section AssemblyMosco

variable {Element Dof : Type*} [Fintype Dof] {d n : ℕ}

/-- The assembled feasible set is weakly sequentially closed. -/
theorem assemblyFeasibleSet_weaklySequentiallyClosed
    (A : BernsteinAssembly Element Dof d n) :
    WeaklySequentiallyClosed (assemblyFeasibleSet A) := by
  intro u x hu hweak
  constructor
  · intro i
    have hcoord : Tendsto (fun k => u k i) atTop (nhds (x i)) := by
      simpa using hweak (ContinuousLinearMap.proj (R := ℝ) i)
    exact ge_of_tendsto' hcoord (fun k => (hu k).1 i)
  · intro i hi
    have hcoord : Tendsto (fun k => u k i) atTop (nhds (x i)) := by
      simpa using hweak (ContinuousLinearMap.proj (R := ℝ) i)
    have hzero : Tendsto (fun k => u k i) atTop (nhds 0) := by
      have hseq : (fun k => u k i) = (fun _ : ℕ => (0 : ℝ)) := by
        funext k
        exact (hu k).2 i hi
      rw [hseq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hcoord hzero

/-- The constant family of assembled feasible sets Mosco-converges to itself. -/
theorem assemblyFeasibleSet_mosco_const
    (A : BernsteinAssembly Element Dof d n) :
    MoscoConverges (fun _ => assemblyFeasibleSet A) (assemblyFeasibleSet A) := by
  exact mosco_const_of_weaklyClosed
    (assemblyFeasibleSet A) (assemblyFeasibleSet_weaklySequentiallyClosed A)

/-- Every assembled feasible vector has the constant strong recovery sequence. -/
theorem assemblyFeasibleSet_identity_recovery
    (A : BernsteinAssembly Element Dof d n)
    (c : Dof → ℝ) (hc : c ∈ assemblyFeasibleSet A) :
    (∀ _k : ℕ, c ∈ assemblyFeasibleSet A) ∧
      StronglyConverges (fun _ : ℕ => c) c := by
  constructor
  · intro k
    exact hc
  · exact tendsto_const_nhds

end AssemblyMosco

end

end BernsteinObstacle
