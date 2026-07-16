#!/usr/bin/env python3
"""Generate the AE density proof for both outer marginals."""
from __future__ import annotations

import csv
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CSV_PATH = ROOT / "math/checkerboard/lp/certificates/q_weights_exact.csv"
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/OuterMarginalAE.lean"


def plus_expr(terms, zero="(0 : ℝ≥0∞)"):
    return " +\n      ".join(terms) if terms else zero


def real_fun(active, stem):
    n=len(active)
    lines=[f"  let f : Fin {n} → ℝ := fun j => match j.1 with"]
    for k,i in enumerate(active[:-1]): lines.append(f"    | {k} => outer{stem}Density{i}.eval")
    lines.append(f"    | _ => outer{stem}Density{active[-1]}.eval")
    return lines


def generate(rows):
    comps=[]
    for row in rows:
        comps.append(dict(ai=int(row['A_lo_idx']),aj=int(row['A_hi_idx']),
                          bi=int(row['B_lo_idx']),bj=int(row['B_hi_idx'])))
    out=["import Checkerboard.LP.DensityArithmetic",
         "import Checkerboard.LP.OuterGeometryCertificate","",
         "/-!","# Generated almost-everywhere outer marginal densities","",
         "The two coordinate marginals of the exact 35-component coupling are",
         "proved equal to unit Lebesgue density.  Closed-interval endpoint",
         "overlaps are discarded using `volume.ae_ne`.","-/","",
         "namespace Checkerboard","","noncomputable section","",
         "open MeasureTheory Set Filter","" ]

    for stem in ['A','B']:
        for i in range(35):
            out += [f"theorem outer{stem}Density{i}_pos : 0 < outer{stem}Density{i}.eval := by",
                    f"  rw [← outer{stem}Density{i}_ratio]",
                    f"  exact div_pos outerWeight{i}_pos outer{stem}Length{i}_pos","" ]

    for stem,cap in [('A','a'),('B','b')]:
        terms=[f"intervalDensity outerEndpointRep{z[cap+'i']}.eval outerEndpointRep{z[cap+'j']}.eval outer{stem}Density{i}.eval x" for i,z in enumerate(comps)]
        out += [f"def outer{stem}DensityFunction (x : ℝ) : ℝ≥0∞ :=",f"  {plus_expr(terms)}","" ]

    out += ["def outerUnitDensity (x : ℝ) : ℝ≥0∞ :=",
            "  intervalDensity outerEndpointRep0.eval outerEndpointRep7.eval 1 x","" ]

    for stem,cap,lower in [('A','a','a'),('B','b','b')]:
        for k in range(7):
            active=[i for i,z in enumerate(comps) if z[cap+'i']<=k<z[cap+'j']]
            expr=plus_expr([f"ENNReal.ofReal outer{stem}Density{i}.eval" for i in active])
            out += [f"theorem outer_{lower}_density_cell{k}_enn :",f"    {expr} = 1 := by"]
            out += real_fun(active,stem)
            out += ["  have hf : ∀ j, 0 ≤ f j := by","    intro j","    fin_cases j"]
            for i in active: out += [f"    · exact le_of_lt outer{stem}Density{i}_pos"]
            out += ["  have hs : ∑ j, f j = 1 := by",
                    f"    simpa [f, Fin.sum_univ_succ] using outer_{lower}_density_cell{k}_rep",
                    "  have h := univ_sum_ofReal_eq_of_real_sum f 1 hf hs",
                    "  simpa [f, Fin.sum_univ_succ] using h","" ]

            out += [f"theorem outer{stem}DensityFunction_cell{k} {{x : ℝ}}",
                    f"    (hl : outerEndpointRep{k}.eval < x)",
                    f"    (hu : x < outerEndpointRep{k+1}.eval) :",
                    f"    outer{stem}DensityFunction x = 1 := by",
                    "  rcases outerEndpointRep_strict_order with ⟨h01,h12,h23,h34,h45,h56,h67⟩"]
            memnames=[]
            for i,z in enumerate(comps):
                ai,aj=z[cap+'i'],z[cap+'j']
                name=f"hm{i}"
                memnames.append(name)
                if ai<=k<aj:
                    out += [f"  have {name} : x ∈ Set.Icc outerEndpointRep{ai}.eval outerEndpointRep{aj}.eval := by",
                            "    constructor <;> nlinarith"]
                else:
                    out += [f"  have {name} : x ∉ Set.Icc outerEndpointRep{ai}.eval outerEndpointRep{aj}.eval := by",
                            "    rintro ⟨hxlo,hxhi⟩","    nlinarith"]
            simp_args=", ".join(memnames)
            out += [f"  have hd : outer{stem}DensityFunction x = {expr} := by",
                    f"    simp [outer{stem}DensityFunction, intervalDensity, {simp_args}]",
                    f"  rw [hd, outer_{lower}_density_cell{k}_enn]","" ]

        for side in ['left','right']:
            cond=("x < outerEndpointRep0.eval" if side=='left' else "outerEndpointRep7.eval < x")
            out += [f"theorem outer{stem}DensityFunction_{side} {{x : ℝ}} (hx : {cond}) :",
                    f"    outer{stem}DensityFunction x = 0 := by",
                    "  rcases outerEndpointRep_strict_order with ⟨h01,h12,h23,h34,h45,h56,h67⟩"]
            memnames=[]
            for i,z in enumerate(comps):
                ai,aj=z[cap+'i'],z[cap+'j']; name=f"hm{i}"; memnames.append(name)
                out += [f"  have {name} : x ∉ Set.Icc outerEndpointRep{ai}.eval outerEndpointRep{aj}.eval := by",
                        "    rintro ⟨hxlo,hxhi⟩","    nlinarith"]
            out += [f"  simp [outer{stem}DensityFunction, intervalDensity, "+", ".join(memnames)+"]",""]

        out += [f"theorem outer{stem}DensityFunction_ae :",
                f"    outer{stem}DensityFunction =ᵐ[volume] outerUnitDensity := by",
                "  filter_upwards [volume.ae_ne outerEndpointRep0.eval,",
                "    volume.ae_ne outerEndpointRep1.eval, volume.ae_ne outerEndpointRep2.eval,",
                "    volume.ae_ne outerEndpointRep3.eval, volume.ae_ne outerEndpointRep4.eval,",
                "    volume.ae_ne outerEndpointRep5.eval, volume.ae_ne outerEndpointRep6.eval,",
                "    volume.ae_ne outerEndpointRep7.eval] with x hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7",
                "  rcases outerEndpointRep_strict_order with ⟨h01,h12,h23,h34,h45,h56,h67⟩",
                "  by_cases h0 : x < outerEndpointRep0.eval",
                f"  · rw [outer{stem}DensityFunction_left h0]",
                "    have hunit : x ∉ Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval := by",
                "      rintro ⟨hxlo,hxhi⟩","      nlinarith",
                "    simp [outerUnitDensity, intervalDensity, hunit]",
                "  have hx0' : outerEndpointRep0.eval < x :=",
                "    lt_of_le_of_ne (not_lt.mp h0) (Ne.symm hx0)"]
        for k in range(1,8):
            out += [f"  by_cases h{k} : x < outerEndpointRep{k}.eval"]
            prev=k-1
            out += [f"  · rw [outer{stem}DensityFunction_cell{prev} hx{prev}' h{k}]",
                    "    have hunit : x ∈ Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval := by",
                    "      constructor <;> nlinarith",
                    "    simp [outerUnitDensity, intervalDensity, hunit]"]
            out += [f"  have hx{k}' : outerEndpointRep{k}.eval < x :=",
                    f"    lt_of_le_of_ne (not_lt.mp h{k}) (Ne.symm hx{k})"]
        out += [f"  rw [outer{stem}DensityFunction_right hx7']",
                "  have hunit : x ∉ Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval := by",
                "    rintro ⟨hxlo,hxhi⟩","    nlinarith",
                "  simp [outerUnitDensity, intervalDensity, hunit]","" ]

    out += ["theorem volume_withDensity_outerADensity :",
            "    volume.withDensity outerADensityFunction =",
            "      volume.restrict (Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval) := by",
            "  rw [withDensity_congr_ae outerADensityFunction_ae]",
            "  unfold outerUnitDensity intervalDensity",
            "  rw [withDensity_indicator_one measurableSet_Icc]","",
            "theorem volume_withDensity_outerBDensity :",
            "    volume.withDensity outerBDensityFunction =",
            "      volume.restrict (Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval) := by",
            "  rw [withDensity_congr_ae outerBDensityFunction_ae]",
            "  unfold outerUnitDensity intervalDensity",
            "  rw [withDensity_indicator_one measurableSet_Icc]","",
            "end","","end Checkerboard",""]
    return "\n".join(out)


def main():
    rows=list(csv.DictReader(CSV_PATH.open(newline='',encoding='utf-8')))
    if len(rows)!=35: raise SystemExit(f"expected 35 rows, got {len(rows)}")
    LEAN_PATH.parent.mkdir(parents=True,exist_ok=True)
    LEAN_PATH.write_text(generate(rows),encoding='utf-8')
    print(f"wrote {LEAN_PATH}")

if __name__=='__main__': main()
