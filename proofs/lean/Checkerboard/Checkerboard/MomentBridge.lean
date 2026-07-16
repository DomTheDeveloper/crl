import Checkerboard.DeficitAlgebra

/-!
# Finite-fiber bridge for the checkerboard moment argument

The theorem in this file derives the first moments, second moment, total
deficits, weighted Cauchy bound, unit-deficit classification, and geometric
contradiction from concrete finite fibers.  Parity-specific checkerboard files
only have to supply their explicit capacity profiles and coordinate maps.
-/

namespace Checkerboard

open scoped BigOperators

/-- Natural unused capacity. -/
def natDeficit (cap count : ℕ → ℕ) (k : ℕ) : ℕ := cap k - count k

/-- Total unused capacity is total capacity minus total occupancy. -/
theorem sum_natDeficit (N : ℕ) (cap count : ℕ → ℕ)
    (hle : ∀ k ∈ Finset.range N, count k ≤ cap k) :
    (∑ k in Finset.range N, natDeficit cap count k) =
      (∑ k in Finset.range N, cap k) - ∑ k in Finset.range N, count k := by
  simpa [natDeficit] using
    (Finset.sum_tsub_distrib (Finset.range N) hle)

/-- Casted weighted unused capacity equals capacity moment minus occupancy moment. -/
theorem sum_natDeficit_mul (N : ℕ) (cap count : ℕ → ℕ) (z : ℕ → ℝ)
    (hle : ∀ k ∈ Finset.range N, count k ≤ cap k) :
    (∑ k in Finset.range N, (natDeficit cap count k : ℝ) * z k) =
      (∑ k in Finset.range N, (cap k : ℝ) * z k) -
        ∑ k in Finset.range N, (count k : ℝ) * z k := by
  calc
    (∑ k in Finset.range N, (natDeficit cap count k : ℝ) * z k) =
        ∑ k in Finset.range N,
          ((cap k : ℝ) * z k - (count k : ℝ) * z k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [natDeficit, Nat.cast_sub (hle k hk)]
            ring
    _ = _ := Finset.sum_sub_distrib

/-- The general finite `q=1` contradiction in doubled centered coordinates. -/
theorem profile_q1_impossible
    {α : Type*} [DecidableEq α]
    (n Nu Nv : ℕ) (S : Finset α)
    (fx fy fu fv : α → ℕ)
    (capU capV : ℕ → ℕ)
    (uoff voff : ℕ → ℝ)
    (DU DV RU RV : ℝ)
    (hn : 1 ≤ n)
    (hcard : S.card = 2 * n - 3)
    (hfx : ∀ p ∈ S, fx p < n)
    (hfy : ∀ p ∈ S, fy p < n)
    (hfu : ∀ p ∈ S, fu p < Nu)
    (hfv : ∀ p ∈ S, fv p < Nv)
    (hxcap : ∀ k ∈ Finset.range n, fiberCard S fx k ≤ 2)
    (hycap : ∀ k ∈ Finset.range n, fiberCard S fy k ≤ 2)
    (hucap : ∀ k ∈ Finset.range Nu, fiberCard S fu k ≤ capU k)
    (hvcap : ∀ k ∈ Finset.range Nv, fiberCard S fv k ≤ capV k)
    (hcapUsum : ∑ k in Finset.range Nu, capU k = 2 * n - 2)
    (hcapVsum : ∑ k in Finset.range Nv, capV k = 2 * n - 2)
    (hcapUfirst :
      ∑ k in Finset.range Nu, (capU k : ℝ) * uoff k = 0)
    (hcapVfirst :
      ∑ k in Finset.range Nv, (capV k : ℝ) * voff k = 0)
    (hcapUsecond :
      ∑ k in Finset.range Nu, (capU k : ℝ) * uoff k ^ 2 = DU)
    (hcapVsecond :
      ∑ k in Finset.range Nv, (capV k : ℝ) * voff k ^ 2 = DV)
    (hcoordX : ∀ p ∈ S,
      centered2Nat n (fx p) = uoff (fu p) + voff (fv p))
    (hcoordY : ∀ p ∈ S,
      centered2Nat n (fy p) = uoff (fu p) - voff (fv p))
    (hUradius : ∀ k ∈ Finset.range Nu, uoff k ^ 2 ≤ RU)
    (hVradius : ∀ k ∈ Finset.range Nv, voff k ^ 2 ≤ RV)
    (hgap : RU + RV <
      -3 * (4 * ((n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3) -
        2 * (DU + DV)) / 4) : False := by
  classical
  let cx : ℕ → ℕ := fun k => fiberCard S fx k
  let cy : ℕ → ℕ := fun k => fiberCard S fy k
  let cu : ℕ → ℕ := fun k => fiberCard S fu k
  let cv : ℕ → ℕ := fun k => fiberCard S fv k
  let c : ℕ → ℕ := natDeficit (fun _ => 2) cx
  let r : ℕ → ℕ := natDeficit (fun _ => 2) cy
  let μ : ℕ → ℕ := natDeficit capU cu
  let ν : ℕ → ℕ := natDeficit capV cv

  have hxsum : ∑ k in Finset.range n, cx k = S.card := by
    simpa [cx] using sum_fiberCard_range S fx n hfx
  have hysum : ∑ k in Finset.range n, cy k = S.card := by
    simpa [cy] using sum_fiberCard_range S fy n hfy
  have husum : ∑ k in Finset.range Nu, cu k = S.card := by
    simpa [cu] using sum_fiberCard_range S fu Nu hfu
  have hvsum : ∑ k in Finset.range Nv, cv k = S.card := by
    simpa [cv] using sum_fiberCard_range S fv Nv hfv

  have hcsum : ∑ k in Finset.range n, c k = 3 := by
    rw [show (∑ k in Finset.range n, c k) =
      (∑ k in Finset.range n, (2 : ℕ)) - ∑ k in Finset.range n, cx k by
        exact sum_natDeficit n (fun _ => 2) cx (by simpa [cx] using hxcap)]
    simp [hxsum, hcard]
    omega
  have hrsum : ∑ k in Finset.range n, r k = 3 := by
    rw [show (∑ k in Finset.range n, r k) =
      (∑ k in Finset.range n, (2 : ℕ)) - ∑ k in Finset.range n, cy k by
        exact sum_natDeficit n (fun _ => 2) cy (by simpa [cy] using hycap)]
    simp [hysum, hcard]
    omega
  have hmusum : ∑ k in Finset.range Nu, μ k = 1 := by
    rw [show (∑ k in Finset.range Nu, μ k) =
      (∑ k in Finset.range Nu, capU k) - ∑ k in Finset.range Nu, cu k by
        exact sum_natDeficit Nu capU cu (by simpa [cu] using hucap)]
    rw [hcapUsum, husum, hcard]
    omega
  have hnusum : ∑ k in Finset.range Nv, ν k = 1 := by
    rw [show (∑ k in Finset.range Nv, ν k) =
      (∑ k in Finset.range Nv, capV k) - ∑ k in Finset.range Nv, cv k by
        exact sum_natDeficit Nv capV cv (by simpa [cv] using hvcap)]
    rw [hcapVsum, hvsum, hcard]
    omega

  have hxocc1 :
      (∑ k in Finset.range n, (cx k : ℝ) * centered2Nat n k) =
        ∑ p ∈ S, centered2Nat n (fx p) := by
    simpa [cx] using sum_fiberCard_mul_range S fx n (centered2Nat n) hfx
  have hyocc1 :
      (∑ k in Finset.range n, (cy k : ℝ) * centered2Nat n k) =
        ∑ p ∈ S, centered2Nat n (fy p) := by
    simpa [cy] using sum_fiberCard_mul_range S fy n (centered2Nat n) hfy
  have huocc1 :
      (∑ k in Finset.range Nu, (cu k : ℝ) * uoff k) =
        ∑ p ∈ S, uoff (fu p) := by
    simpa [cu] using sum_fiberCard_mul_range S fu Nu uoff hfu
  have hvocc1 :
      (∑ k in Finset.range Nv, (cv k : ℝ) * voff k) =
        ∑ p ∈ S, voff (fv p) := by
    simpa [cv] using sum_fiberCard_mul_range S fv Nv voff hfv

  have hcfirst :
      (∑ k in Finset.range n, (c k : ℝ) * centered2Nat n k) =
        -(∑ p ∈ S, centered2Nat n (fx p)) := by
    rw [show (∑ k in Finset.range n, (c k : ℝ) * centered2Nat n k) =
      (∑ k in Finset.range n, ((2 : ℕ) : ℝ) * centered2Nat n k) -
        ∑ k in Finset.range n, (cx k : ℝ) * centered2Nat n k by
          exact sum_natDeficit_mul n (fun _ => 2) cx (centered2Nat n)
            (by simpa [cx] using hxcap)]
    rw [hxocc1]
    have hz := centered2_sum n
    simp_rw [← Finset.mul_sum]
    rw [hz]
    ring
  have hrfirst :
      (∑ k in Finset.range n, (r k : ℝ) * centered2Nat n k) =
        -(∑ p ∈ S, centered2Nat n (fy p)) := by
    rw [show (∑ k in Finset.range n, (r k : ℝ) * centered2Nat n k) =
      (∑ k in Finset.range n, ((2 : ℕ) : ℝ) * centered2Nat n k) -
        ∑ k in Finset.range n, (cy k : ℝ) * centered2Nat n k by
          exact sum_natDeficit_mul n (fun _ => 2) cy (centered2Nat n)
            (by simpa [cy] using hycap)]
    rw [hyocc1]
    have hz := centered2_sum n
    simp_rw [← Finset.mul_sum]
    rw [hz]
    ring
  have hmufirst :
      (∑ k in Finset.range Nu, (μ k : ℝ) * uoff k) =
        -(∑ p ∈ S, uoff (fu p)) := by
    rw [show (∑ k in Finset.range Nu, (μ k : ℝ) * uoff k) =
      (∑ k in Finset.range Nu, (capU k : ℝ) * uoff k) -
        ∑ k in Finset.range Nu, (cu k : ℝ) * uoff k by
          exact sum_natDeficit_mul Nu capU cu uoff (by simpa [cu] using hucap)]
    rw [hcapUfirst, huocc1]
    ring
  have hnufirst :
      (∑ k in Finset.range Nv, (ν k : ℝ) * voff k) =
        -(∑ p ∈ S, voff (fv p)) := by
    rw [show (∑ k in Finset.range Nv, (ν k : ℝ) * voff k) =
      (∑ k in Finset.range Nv, (capV k : ℝ) * voff k) -
        ∑ k in Finset.range Nv, (cv k : ℝ) * voff k by
          exact sum_natDeficit_mul Nv capV cv voff (by simpa [cv] using hvcap)]
    rw [hcapVfirst, hvocc1]
    ring

  have hpointX :
      (∑ p ∈ S, centered2Nat n (fx p)) =
        (∑ p ∈ S, uoff (fu p)) + ∑ p ∈ S, voff (fv p) := by
    calc
      (∑ p ∈ S, centered2Nat n (fx p)) =
          ∑ p ∈ S, (uoff (fu p) + voff (fv p)) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hcoordX p hp
      _ = _ := Finset.sum_add_distrib
  have hpointY :
      (∑ p ∈ S, centered2Nat n (fy p)) =
        (∑ p ∈ S, uoff (fu p)) - ∑ p ∈ S, voff (fv p) := by
    calc
      (∑ p ∈ S, centered2Nat n (fy p)) =
          ∑ p ∈ S, (uoff (fu p) - voff (fv p)) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hcoordY p hp
      _ = _ := Finset.sum_sub_distrib

  have hfirstC :
      (∑ k in Finset.range n, (c k : ℝ) * centered2Nat n k) =
        (∑ k in Finset.range Nu, (μ k : ℝ) * uoff k) +
          ∑ k in Finset.range Nv, (ν k : ℝ) * voff k := by
    rw [hcfirst, hmufirst, hnufirst, hpointX]
    ring
  have hfirstR :
      (∑ k in Finset.range n, (r k : ℝ) * centered2Nat n k) =
        (∑ k in Finset.range Nu, (μ k : ℝ) * uoff k) -
          ∑ k in Finset.range Nv, (ν k : ℝ) * voff k := by
    rw [hrfirst, hmufirst, hnufirst, hpointY]
    ring

  have hxocc2 :
      (∑ k in Finset.range n, (cx k : ℝ) * centered2Nat n k ^ 2) =
        ∑ p ∈ S, centered2Nat n (fx p) ^ 2 := by
    simpa [cx] using sum_fiberCard_mul_range S fx n
      (fun k => centered2Nat n k ^ 2) hfx
  have hyocc2 :
      (∑ k in Finset.range n, (cy k : ℝ) * centered2Nat n k ^ 2) =
        ∑ p ∈ S, centered2Nat n (fy p) ^ 2 := by
    simpa [cy] using sum_fiberCard_mul_range S fy n
      (fun k => centered2Nat n k ^ 2) hfy
  have huocc2 :
      (∑ k in Finset.range Nu, (cu k : ℝ) * uoff k ^ 2) =
        ∑ p ∈ S, uoff (fu p) ^ 2 := by
    simpa [cu] using sum_fiberCard_mul_range S fu Nu (fun k => uoff k ^ 2) hfu
  have hvocc2 :
      (∑ k in Finset.range Nv, (cv k : ℝ) * voff k ^ 2) =
        ∑ p ∈ S, voff (fv p) ^ 2 := by
    simpa [cv] using sum_fiberCard_mul_range S fv Nv (fun k => voff k ^ 2) hfv

  have hcsecond :
      (∑ k in Finset.range n, (c k : ℝ) * centered2Nat n k ^ 2) =
        2 * ((n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3) -
          ∑ p ∈ S, centered2Nat n (fx p) ^ 2 := by
    rw [show (∑ k in Finset.range n, (c k : ℝ) * centered2Nat n k ^ 2) =
      (∑ k in Finset.range n, ((2 : ℕ) : ℝ) * centered2Nat n k ^ 2) -
        ∑ k in Finset.range n, (cx k : ℝ) * centered2Nat n k ^ 2 by
          exact sum_natDeficit_mul n (fun _ => 2) cx
            (fun k => centered2Nat n k ^ 2) (by simpa [cx] using hxcap)]
    rw [hxocc2]
    simp_rw [← Finset.mul_sum]
    rw [centered2_square_sum]
  have hrsecond :
      (∑ k in Finset.range n, (r k : ℝ) * centered2Nat n k ^ 2) =
        2 * ((n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3) -
          ∑ p ∈ S, centered2Nat n (fy p) ^ 2 := by
    rw [show (∑ k in Finset.range n, (r k : ℝ) * centered2Nat n k ^ 2) =
      (∑ k in Finset.range n, ((2 : ℕ) : ℝ) * centered2Nat n k ^ 2) -
        ∑ k in Finset.range n, (cy k : ℝ) * centered2Nat n k ^ 2 by
          exact sum_natDeficit_mul n (fun _ => 2) cy
            (fun k => centered2Nat n k ^ 2) (by simpa [cy] using hycap)]
    rw [hyocc2]
    simp_rw [← Finset.mul_sum]
    rw [centered2_square_sum]
  have hmusecond :
      (∑ k in Finset.range Nu, (μ k : ℝ) * uoff k ^ 2) =
        DU - ∑ p ∈ S, uoff (fu p) ^ 2 := by
    rw [show (∑ k in Finset.range Nu, (μ k : ℝ) * uoff k ^ 2) =
      (∑ k in Finset.range Nu, (capU k : ℝ) * uoff k ^ 2) -
        ∑ k in Finset.range Nu, (cu k : ℝ) * uoff k ^ 2 by
          exact sum_natDeficit_mul Nu capU cu (fun k => uoff k ^ 2)
            (by simpa [cu] using hucap)]
    rw [hcapUsecond, huocc2]
  have hnusecond :
      (∑ k in Finset.range Nv, (ν k : ℝ) * voff k ^ 2) =
        DV - ∑ p ∈ S, voff (fv p) ^ 2 := by
    rw [show (∑ k in Finset.range Nv, (ν k : ℝ) * voff k ^ 2) =
      (∑ k in Finset.range Nv, (capV k : ℝ) * voff k ^ 2) -
        ∑ k in Finset.range Nv, (cv k : ℝ) * voff k ^ 2 by
          exact sum_natDeficit_mul Nv capV cv (fun k => voff k ^ 2)
            (by simpa [cv] using hvcap)]
    rw [hcapVsecond, hvocc2]

  have hpointSquares :
      (∑ p ∈ S, centered2Nat n (fx p) ^ 2) +
        (∑ p ∈ S, centered2Nat n (fy p) ^ 2) =
      2 * ((∑ p ∈ S, uoff (fu p) ^ 2) +
        ∑ p ∈ S, voff (fv p) ^ 2) := by
    calc
      (∑ p ∈ S, centered2Nat n (fx p) ^ 2) +
          (∑ p ∈ S, centered2Nat n (fy p) ^ 2) =
          ∑ p ∈ S,
            (centered2Nat n (fx p) ^ 2 + centered2Nat n (fy p) ^ 2) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ p ∈ S, 2 * (uoff (fu p) ^ 2 + voff (fv p) ^ 2) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [hcoordX p hp, hcoordY p hp]
            ring
      _ = _ := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]

  have hsecond :
      (∑ k in Finset.range n, (c k : ℝ) * centered2Nat n k ^ 2) +
        (∑ k in Finset.range n, (r k : ℝ) * centered2Nat n k ^ 2) =
      (4 * ((n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3) - 2 * (DU + DV)) +
        2 * ((∑ k in Finset.range Nu, (μ k : ℝ) * uoff k ^ 2) +
          ∑ k in Finset.range Nv, (ν k : ℝ) * voff k ^ 2) := by
    rw [hcsecond, hrsecond, hmusecond, hnusecond]
    linarith [hpointSquares]

  have hlower := q1_master_lower
    (Finset.range n) (Finset.range n) (Finset.range Nu) (Finset.range Nv)
    c r μ ν (centered2Nat n) (centered2Nat n) uoff voff
    (4 * ((n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3) - 2 * (DU + DV))
    hcsum hrsum hmusum hnusum hfirstC hfirstR hsecond
  have hupperU := unitDeficit_second_le
    (Finset.range Nu) μ uoff RU hmusum hUradius
  have hupperV := unitDeficit_second_le
    (Finset.range Nv) ν voff RV hnusum hVradius
  linarith

end Checkerboard
