#!/usr/bin/env python3
"""Generate the AE density proof for the paired outer sum/difference projection."""
from __future__ import annotations

import csv
from fractions import Fraction
from pathlib import Path

from generate_outer_density_certificate import K, ordered, qlean, rep_literal, sign_kind

ROOT = Path(__file__).resolve().parents[2]
CSV_PATH = ROOT / "math/checkerboard/lp/certificates/q_weights_exact.csv"
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/OuterProjectionAE.lean"


def plus_expr(terms, zero="(0 : ℝ≥0∞)"):
    return " +\n      ".join(terms) if terms else zero


def emit_pos(out, theorem, defname, x):
    out += [f"theorem {theorem} : 0 < {defname}.eval := by",
            f"  have h : 0 < evalAtCheckerboardP {qlean(x.a)} {qlean(x.b)} {qlean(x.c)} := by"]
    kind=sign_kind(x)
    if kind=='concave':
        out += ["    apply evalAtCheckerboardP_pos_of_concave","    · norm_num",
                "    · norm_num [quadraticAt, pLower]","    · norm_num [quadraticAt, pUpper]"]
    elif kind=='left':
        out += ["    apply evalAtCheckerboardP_pos_of_left","    · norm_num",
                "    · norm_num [pLower]","    · norm_num [quadraticAt, pLower]"]
    else:
        out += ["    apply evalAtCheckerboardP_pos_of_right","    · norm_num",
                "    · norm_num [pUpper]","    · norm_num [quadraticAt, pUpper]"]
    out += [f"  simpa [{defname}, CubicRep.eval, evalAtCheckerboardP, quadraticAt] using h",""]


def finite_real_fun(active):
    n=len(active)
    lines=[f"  let f : Fin {n} → ℝ := fun j => match j.1 with"]
    for k,(kind,i) in enumerate(active[:-1]): lines.append(f"    | {k} => outer{kind}Density{i}.eval")
    kind,i=active[-1]
    lines.append(f"    | _ => outer{kind}Density{i}.eval")
    return lines


def generate(rows):
    r=K(Fraction(539,912),Fraction(487,456),Fraction(-1203,304))
    q=K(Fraction(-713,912),Fraction(871,152),Fraction(-6817,912))
    h=K(Fraction(-47,304),Fraction(4739,456),Fraction(-10025,912))
    E=[K(0),q,K(1)-r,h-K(1),r,(h-q)*Fraction(1,2),(h+q)*Fraction(1,2),K(1)]
    comps=[]
    breaks=[-r,-q,q,h]
    for row in rows:
        ai,aj=int(row['A_lo_idx']),int(row['A_hi_idx'])
        bi,bj=int(row['B_lo_idx']),int(row['B_hi_idx'])
        sigma=int(row['sigma'])
        la,lb=E[aj]-E[ai],E[bj]-E[bi]
        ma,mb=(E[ai]+E[aj])*Fraction(1,2),(E[bi]+E[bj])*Fraction(1,2)
        slo,shi,_=ordered(ma+mb,la+sigma*lb)
        dlo,dhi,_=ordered(ma-mb,la-sigma*lb)
        comps.append(dict(slo=slo,shi=shi,dlo=dlo,dhi=dhi))
        breaks += [slo,shi,dlo,dhi]
    uniq=[]
    for x in sorted(breaks,key=lambda u:u.decimal()):
        if not uniq or x!=uniq[-1]: uniq.append(x)
    if len(uniq)!=27: raise RuntimeError(f"expected 27 breakpoints, got {len(uniq)}")
    index={(x.a,x.b,x.c):i for i,x in enumerate(uniq)}
    neg_r=index[(-r).a,(-r).b,(-r).c]
    neg_q=index[(-q).a,(-q).b,(-q).c]
    pos_q=index[q.a,q.b,q.c]
    pos_h=index[h.a,h.b,h.c]

    out=["import Checkerboard.LP.DensityArithmetic",
         "import Checkerboard.LP.OuterSupportCertificate","",
         "/-!","# Generated AE paired outer projection density","",
         "The combined sum and difference pushforwards have density one exactly",
         "on `[-r,-q] ∪ [q,h]`, apart from finitely many endpoints.","-/","",
         "namespace Checkerboard","","noncomputable section","",
         "open MeasureTheory Set Filter","" ]

    for i in range(35):
        for kind in ['Sum','Diff']:
            out += [f"theorem outer{kind}Density{i}_pos : 0 < outer{kind}Density{i}.eval := by",
                    f"  rw [← outer{kind}Density{i}_ratio]",
                    f"  exact div_pos outerWeight{i}_pos outer{kind}Length{i}_pos","" ]

    for j,x in enumerate(uniq):
        out += [f"def outerProjectionBreakpoint{j} : CubicRep := {rep_literal(x)}",""]
    for j in range(26):
        gap=uniq[j+1]-uniq[j]
        out += [f"def outerProjectionGap{j} : CubicRep := {rep_literal(gap)}",""]
        emit_pos(out,f"outerProjectionGap{j}_pos",f"outerProjectionGap{j}",gap)
        out += [f"theorem outerProjectionBreakpoint_step{j} :",
                f"    outerProjectionBreakpoint{j}.eval < outerProjectionBreakpoint{j+1}.eval := by",
                f"  have heq : outerProjectionGap{j}.eval =",
                f"      outerProjectionBreakpoint{j+1}.eval - outerProjectionBreakpoint{j}.eval := by",
                f"    norm_num [outerProjectionGap{j}, outerProjectionBreakpoint{j},",
                f"      outerProjectionBreakpoint{j+1}, CubicRep.eval]","    ring",
                f"  nlinarith [outerProjectionGap{j}_pos]","" ]
    chain=" ∧\n    ".join(f"outerProjectionBreakpoint{j}.eval < outerProjectionBreakpoint{j+1}.eval" for j in range(26))
    out += ["theorem outerProjectionBreakpoint_order :",f"    {chain} := by",
            "  exact ⟨"+", ".join(f"outerProjectionBreakpoint_step{j}" for j in range(26)) + "⟩","" ]

    terms=[]
    for i,z in enumerate(comps):
        terms.append(f"intervalDensity outerSumLo{i}.eval outerSumHi{i}.eval outerSumDensity{i}.eval x")
        terms.append(f"intervalDensity outerDiffLo{i}.eval outerDiffHi{i}.eval outerDiffDensity{i}.eval x")
    out += ["def outerProjectionDensityFunction (x : ℝ) : ℝ≥0∞ :=",f"  {plus_expr(terms)}","",
            "def outerProjectionTargetDensity (x : ℝ) : ℝ≥0∞ :=",
            "  ((Set.Icc (-outerR) (-outerQ) ∪ Set.Icc outerQ outerH).indicator",
            "    (fun _ => (1 : ℝ≥0∞))) x","" ]

    # Cell theorems.
    for j,(lo,hi) in enumerate(zip(uniq,uniq[1:])):
        mid=(lo.decimal()+hi.decimal())/2
        active=[]
        for i,z in enumerate(comps):
            if z['slo'].decimal()<mid<z['shi'].decimal(): active.append(('Sum',i))
            if z['dlo'].decimal()<mid<z['dhi'].decimal(): active.append(('Diff',i))
        target=int((-r.decimal()<mid<-q.decimal()) or (q.decimal()<mid<h.decimal()))
        expr=plus_expr([f"ENNReal.ofReal outer{kind}Density{i}.eval" for kind,i in active])
        out += [f"theorem outer_projection_density_cell{j}_enn :",f"    {expr} = {target} := by"]
        if not active:
            out += ["  norm_num",""]
        else:
            out += finite_real_fun(active)
            out += ["  have hf : ∀ k, 0 ≤ f k := by","    intro k","    fin_cases k"]
            for kind,i in active: out += [f"    · exact le_of_lt outer{kind}Density{i}_pos"]
            out += [f"  have hs : ∑ k, f k = {target} := by",
                    f"    simpa [f, Fin.sum_univ_succ] using outer_projection_density_cell{j}_rep",
                    f"  have hsum := univ_sum_ofReal_eq_of_real_sum f {target} hf hs",
                    "  simpa [f, Fin.sum_univ_succ] using hsum","" ]

        out += [f"theorem outerProjectionDensityFunction_cell{j} {{x : ℝ}}",
                f"    (hl : outerProjectionBreakpoint{j}.eval < x)",
                f"    (hu : x < outerProjectionBreakpoint{j+1}.eval) :",
                f"    outerProjectionDensityFunction x = {target} := by",
                "  rcases outerProjectionBreakpoint_order with ⟨"+
                    ",".join(f"h{k}" for k in range(26))+"⟩"]
        memnames=[]
        for i,z in enumerate(comps):
            for kind,lk,hk in [('Sum','slo','shi'),('Diff','dlo','dhi')]:
                a=index[(z[lk].a,z[lk].b,z[lk].c)]
                b=index[(z[hk].a,z[hk].b,z[hk].c)]
                name=f"hm{kind}{i}"; memnames.append(name)
                isactive=a<=j<b
                if isactive:
                    out += [f"  have {name} : x ∈ Set.Icc outer{kind}Lo{i}.eval outer{kind}Hi{i}.eval := by",
                            f"    have hlo : outer{kind}Lo{i}.eval = outerProjectionBreakpoint{a}.eval := by",
                            f"      norm_num [outer{kind}Lo{i}, outerProjectionBreakpoint{a}, CubicRep.eval]",
                            f"    have hhi : outer{kind}Hi{i}.eval = outerProjectionBreakpoint{b}.eval := by",
                            f"      norm_num [outer{kind}Hi{i}, outerProjectionBreakpoint{b}, CubicRep.eval]",
                            "    rw [hlo,hhi]","    constructor <;> nlinarith"]
                else:
                    out += [f"  have {name} : x ∉ Set.Icc outer{kind}Lo{i}.eval outer{kind}Hi{i}.eval := by",
                            f"    have hlo : outer{kind}Lo{i}.eval = outerProjectionBreakpoint{a}.eval := by",
                            f"      norm_num [outer{kind}Lo{i}, outerProjectionBreakpoint{a}, CubicRep.eval]",
                            f"    have hhi : outer{kind}Hi{i}.eval = outerProjectionBreakpoint{b}.eval := by",
                            f"      norm_num [outer{kind}Hi{i}, outerProjectionBreakpoint{b}, CubicRep.eval]",
                            "    rw [hlo,hhi]","    rintro ⟨hxlo,hxhi⟩","    nlinarith"]
        out += [f"  have hd : outerProjectionDensityFunction x = {expr} := by",
                "    simp [outerProjectionDensityFunction, intervalDensity, "+", ".join(memnames)+"]",
                f"  rw [hd, outer_projection_density_cell{j}_enn]","" ]

    # Outside lemmas.
    for side,bp,ineq in [('left',0,'x < outerProjectionBreakpoint0.eval'),
                         ('right',26,'outerProjectionBreakpoint26.eval < x')]:
        out += [f"theorem outerProjectionDensityFunction_{side} {{x : ℝ}} (hx : {ineq}) :",
                "    outerProjectionDensityFunction x = 0 := by",
                "  rcases outerProjectionBreakpoint_order with ⟨"+
                    ",".join(f"h{k}" for k in range(26))+"⟩"]
        memnames=[]
        for i,z in enumerate(comps):
            for kind,lk,hk in [('Sum','slo','shi'),('Diff','dlo','dhi')]:
                a=index[(z[lk].a,z[lk].b,z[lk].c)]
                b=index[(z[hk].a,z[hk].b,z[hk].c)]
                name=f"hm{kind}{i}"; memnames.append(name)
                out += [f"  have {name} : x ∉ Set.Icc outer{kind}Lo{i}.eval outer{kind}Hi{i}.eval := by",
                        f"    have hlo : outer{kind}Lo{i}.eval = outerProjectionBreakpoint{a}.eval := by",
                        f"      norm_num [outer{kind}Lo{i}, outerProjectionBreakpoint{a}, CubicRep.eval]",
                        f"    have hhi : outer{kind}Hi{i}.eval = outerProjectionBreakpoint{b}.eval := by",
                        f"      norm_num [outer{kind}Hi{i}, outerProjectionBreakpoint{b}, CubicRep.eval]",
                        "    rw [hlo,hhi]","    rintro ⟨hxlo,hxhi⟩","    nlinarith"]
        out += ["  simp [outerProjectionDensityFunction, intervalDensity, "+", ".join(memnames)+"]",""]

    # Band endpoint evaluations.
    out += [f"theorem outerProjectionBreakpoint_negR : outerProjectionBreakpoint{neg_r}.eval = -outerR := by",
            "  rw [← outerNegRRep_eval]",f"  norm_num [outerProjectionBreakpoint{neg_r}, outerNegRRep, CubicRep.eval]","",
            f"theorem outerProjectionBreakpoint_negQ : outerProjectionBreakpoint{neg_q}.eval = -outerQ := by",
            "  rw [← outerNegQRep_eval]",f"  norm_num [outerProjectionBreakpoint{neg_q}, outerNegQRep, CubicRep.eval]","",
            f"theorem outerProjectionBreakpoint_posQ : outerProjectionBreakpoint{pos_q}.eval = outerQ := by",
            "  rw [← outerQRep_eval]",f"  norm_num [outerProjectionBreakpoint{pos_q}, outerQRep, CubicRep.eval]","",
            f"theorem outerProjectionBreakpoint_posH : outerProjectionBreakpoint{pos_h}.eval = outerH := by",
            "  rw [← outerHRep_eval]",f"  norm_num [outerProjectionBreakpoint{pos_h}, outerHRep, CubicRep.eval]","" ]

    # AE classification.
    ae_list=",\n    ".join(f"volume.ae_ne outerProjectionBreakpoint{j}.eval" for j in range(27))
    args=" ".join(f"hx{j}" for j in range(27))
    out += ["theorem outerProjectionDensityFunction_ae :",
            "    outerProjectionDensityFunction =ᵐ[volume] outerProjectionTargetDensity := by",
            f"  filter_upwards [{ae_list}] with x {args}",
            "  rcases outerProjectionBreakpoint_order with ⟨"+
                ",".join(f"h{k}" for k in range(26))+"⟩",
            "  by_cases hb0 : x < outerProjectionBreakpoint0.eval",
            "  · rw [outerProjectionDensityFunction_left hb0]",
            "    have hout : x ∉ Set.Icc (-outerR) (-outerQ) ∪ Set.Icc outerQ outerH := by",
            "      rintro (hxband | hxband)",
            f"      · rw [← outerProjectionBreakpoint_negR] at hxband","        nlinarith",
            f"      · rw [← outerProjectionBreakpoint_posQ] at hxband","        nlinarith",
            "    simp [outerProjectionTargetDensity, hout]",
            "  have hx0' : outerProjectionBreakpoint0.eval < x :=",
            "    lt_of_le_of_ne (not_lt.mp hb0) (Ne.symm hx0)"]
    for j in range(1,27):
        out += [f"  by_cases hb{j} : x < outerProjectionBreakpoint{j}.eval",
                f"  · rw [outerProjectionDensityFunction_cell{j-1} hx{j-1}' hb{j}]"]
        target=int((neg_r<=j-1<neg_q) or (pos_q<=j-1<pos_h))
        if target:
            if neg_r<=j-1<neg_q:
                out += ["    have hband : x ∈ Set.Icc (-outerR) (-outerQ) := by",
                        f"      rw [← outerProjectionBreakpoint_negR, ← outerProjectionBreakpoint_negQ]",
                        "      constructor <;> nlinarith",
                        "    simp [outerProjectionTargetDensity, hband]"]
            else:
                out += ["    have hband : x ∈ Set.Icc outerQ outerH := by",
                        f"      rw [← outerProjectionBreakpoint_posQ, ← outerProjectionBreakpoint_posH]",
                        "      constructor <;> nlinarith",
                        "    simp [outerProjectionTargetDensity, hband]"]
        else:
            out += ["    have hout : x ∉ Set.Icc (-outerR) (-outerQ) ∪ Set.Icc outerQ outerH := by",
                    "      rintro (hxband | hxband)"]
            # both alternatives contradicted by cell order; endpoint rewrites let nlinarith decide
            out += ["      · rw [← outerProjectionBreakpoint_negR, ← outerProjectionBreakpoint_negQ] at hxband",
                    "        nlinarith",
                    "      · rw [← outerProjectionBreakpoint_posQ, ← outerProjectionBreakpoint_posH] at hxband",
                    "        nlinarith",
                    "    simp [outerProjectionTargetDensity, hout]"]
        out += [f"  have hx{j}' : outerProjectionBreakpoint{j}.eval < x :=",
                f"    lt_of_le_of_ne (not_lt.mp hb{j}) (Ne.symm hx{j})"]
    out += ["  rw [outerProjectionDensityFunction_right hx26']",
            "  have hout : x ∉ Set.Icc (-outerR) (-outerQ) ∪ Set.Icc outerQ outerH := by",
            "    rintro (hxband | hxband)",
            "    · rw [← outerProjectionBreakpoint_negQ] at hxband","      nlinarith",
            "    · rw [← outerProjectionBreakpoint_posH] at hxband","      nlinarith",
            "  simp [outerProjectionTargetDensity, hout]","",
            "theorem volume_withDensity_outerProjectionDensity :",
            "    volume.withDensity outerProjectionDensityFunction =",
            "      volume.withDensity outerProjectionTargetDensity := by",
            "  exact withDensity_congr_ae outerProjectionDensityFunction_ae","",
            "end","","end Checkerboard",""]
    return "\n".join(out)


def main():
    rows=list(csv.DictReader(CSV_PATH.open(newline='',encoding='utf-8')))
    if len(rows)!=35: raise SystemExit(f"expected 35 rows, got {len(rows)}")
    LEAN_PATH.parent.mkdir(parents=True,exist_ok=True)
    LEAN_PATH.write_text(generate(rows),encoding='utf-8')
    print(f"wrote {LEAN_PATH}")

if __name__=='__main__': main()
