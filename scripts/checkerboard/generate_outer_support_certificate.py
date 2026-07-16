#!/usr/bin/env python3
"""Generate kernel-checkable support inequalities for all 35 outer components."""
from __future__ import annotations

import csv
from fractions import Fraction
from pathlib import Path

from generate_outer_density_certificate import K, qlean, rep_literal, ordered, sign_kind

ROOT = Path(__file__).resolve().parents[2]
CSV_PATH = ROOT / "math/checkerboard/lp/certificates/q_weights_exact.csv"
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/OuterSupportCertificate.lean"


def emit_nonneg(out, theorem: str, defname: str, x: K):
    if x == K(0):
        out += [f"theorem {theorem} : 0 ≤ {defname}.eval := by",
                f"  norm_num [{defname}, CubicRep.eval]",""]
        return
    out += [f"theorem {theorem}_pos : 0 < {defname}.eval := by",
            f"  have h : 0 < evalAtCheckerboardP {qlean(x.a)} {qlean(x.b)} {qlean(x.c)} := by"]
    kind=sign_kind(x)
    if kind=="concave":
        out += ["    apply evalAtCheckerboardP_pos_of_concave","    · norm_num",
                "    · norm_num [quadraticAt, pLower]","    · norm_num [quadraticAt, pUpper]"]
    elif kind=="left":
        out += ["    apply evalAtCheckerboardP_pos_of_left","    · norm_num",
                "    · norm_num [pLower]","    · norm_num [quadraticAt, pLower]"]
    else:
        out += ["    apply evalAtCheckerboardP_pos_of_right","    · norm_num",
                "    · norm_num [pUpper]","    · norm_num [quadraticAt, pUpper]"]
    out += [f"  simpa [{defname}, CubicRep.eval, evalAtCheckerboardP, quadraticAt] using h","",
            f"theorem {theorem} : 0 ≤ {defname}.eval := le_of_lt {theorem}_pos",""]


def emit_slack(out, name: str, x: K, left: str, right: str):
    out += [f"def {name} : CubicRep := {rep_literal(x)}","",
            f"theorem {name}_identity : {name} = CubicRep.sub {left} {right} := by",
            "  apply CubicRep.ext <;>",
            f"    norm_num [{name}, {left}, {right}, CubicRep.sub, CubicRep.add, CubicRep.neg]",""]
    emit_nonneg(out,name+"_nonneg",name,x)
    out += [f"theorem {name}_order : {right}.eval ≤ {left}.eval := by",
            f"  have he := congrArg CubicRep.eval {name}_identity",
            "  simp only [CubicRep.eval_sub] at he",
            f"  nlinarith [{name}_nonneg]",""]


def generate(rows):
    r=K(Fraction(539,912),Fraction(487,456),Fraction(-1203,304))
    q=K(Fraction(-713,912),Fraction(871,152),Fraction(-6817,912))
    h=K(Fraction(-47,304),Fraction(4739,456),Fraction(-10025,912))
    E=[K(0),q,K(1)-r,h-K(1),r,(h-q)*Fraction(1,2),(h+q)*Fraction(1,2),K(1)]
    comps=[]
    for row in rows:
        ai,aj=int(row['A_lo_idx']),int(row['A_hi_idx'])
        bi,bj=int(row['B_lo_idx']),int(row['B_hi_idx'])
        sigma=int(row['sigma'])
        la,lb=E[aj]-E[ai],E[bj]-E[bi]
        ma,mb=(E[ai]+E[aj])*Fraction(1,2),(E[bi]+E[bj])*Fraction(1,2)
        slo,shi,_=ordered(ma+mb,la+sigma*lb)
        dlo,dhi,_=ordered(ma-mb,la-sigma*lb)
        comps.append(dict(slo=slo,shi=shi,dlo=dlo,dhi=dhi))

    out=["import Checkerboard.LP.OuterDensityCertificate","",
         "/-!","# Generated support checks for the 35 outer affine couplings","",
         "Every component sum lies in `[q,h]`; every difference lies in",
         "`[-r,-q]` or `[q,h]`.  All inequalities are exact cubic-field checks.","-/","",
         "namespace Checkerboard","","noncomputable section","",
         f"def outerQRep : CubicRep := {rep_literal(q)}",
         f"def outerRRep : CubicRep := {rep_literal(r)}",
         f"def outerHRep : CubicRep := {rep_literal(h)}",
         f"def outerNegQRep : CubicRep := {rep_literal(-q)}",
         f"def outerNegRRep : CubicRep := {rep_literal(-r)}","",
         "theorem outerQRep_eval : outerQRep.eval = outerQ := by",
         "  rw [outerQ_reduced]","  norm_num [outerQRep, CubicRep.eval]","",
         "theorem outerRRep_eval : outerRRep.eval = outerR := by",
         "  rw [outerR_reduced]","  norm_num [outerRRep, CubicRep.eval]","",
         "theorem outerHRep_eval : outerHRep.eval = outerH := by",
         "  rw [outerH_reduced]","  norm_num [outerHRep, CubicRep.eval]","",
         "theorem outerNegQRep_eval : outerNegQRep.eval = -outerQ := by",
         "  rw [← outerQRep_eval]","  norm_num [outerNegQRep, outerQRep, CubicRep.eval]","",
         "theorem outerNegRRep_eval : outerNegRRep.eval = -outerR := by",
         "  rw [← outerRRep_eval]","  norm_num [outerNegRRep, outerRRep, CubicRep.eval]","" ]

    for i,z in enumerate(comps):
        emit_slack(out,f"outerSumLoSlack{i}",z['slo']-q,f"outerSumLo{i}","outerQRep")
        emit_slack(out,f"outerSumHiSlack{i}",h-z['shi'],"outerHRep",f"outerSumHi{i}")
        emit_slack(out,f"outerDiffFloorSlack{i}",z['dlo']-(-r),f"outerDiffLo{i}","outerNegRRep")
        if z['dhi'].decimal() <= (-q).decimal()+1e-12:
            emit_slack(out,f"outerDiffNegCeilSlack{i}",(-q)-z['dhi'],"outerNegQRep",f"outerDiffHi{i}")
            out += [f"theorem outerDiffComponent{i}_negative_band :",
                    f"    -outerR ≤ outerDiffLo{i}.eval ∧ outerDiffHi{i}.eval ≤ -outerQ := by",
                    f"  rw [← outerNegRRep_eval, ← outerNegQRep_eval]",
                    f"  exact ⟨outerDiffFloorSlack{i}_order, outerDiffNegCeilSlack{i}_order⟩",""]
        else:
            emit_slack(out,f"outerDiffPosFloorSlack{i}",z['dlo']-q,f"outerDiffLo{i}","outerQRep")
            emit_slack(out,f"outerDiffPosCeilSlack{i}",h-z['dhi'],"outerHRep",f"outerDiffHi{i}")
            out += [f"theorem outerDiffComponent{i}_positive_band :",
                    f"    outerQ ≤ outerDiffLo{i}.eval ∧ outerDiffHi{i}.eval ≤ outerH := by",
                    f"  rw [← outerQRep_eval, ← outerHRep_eval]",
                    f"  exact ⟨outerDiffPosFloorSlack{i}_order, outerDiffPosCeilSlack{i}_order⟩",""]
        out += [f"theorem outerSumComponent{i}_band :",
                f"    outerQ ≤ outerSumLo{i}.eval ∧ outerSumHi{i}.eval ≤ outerH := by",
                f"  rw [← outerQRep_eval, ← outerHRep_eval]",
                f"  exact ⟨outerSumLoSlack{i}_order, outerSumHiSlack{i}_order⟩",""]

    out += ["end","","end Checkerboard",""]
    return "\n".join(out)


def main():
    rows=list(csv.DictReader(CSV_PATH.open(newline='',encoding='utf-8')))
    if len(rows)!=35: raise SystemExit(f"expected 35 rows, got {len(rows)}")
    LEAN_PATH.parent.mkdir(parents=True,exist_ok=True)
    LEAN_PATH.write_text(generate(rows),encoding='utf-8')
    print(f"wrote {LEAN_PATH}")

if __name__=='__main__': main()
