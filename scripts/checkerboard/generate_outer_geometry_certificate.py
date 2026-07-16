#!/usr/bin/env python3
"""Generate the pointwise geometry proof for all 35 outer affine couplings."""
from __future__ import annotations

import csv
from fractions import Fraction
from pathlib import Path

from generate_outer_density_certificate import K, ordered

ROOT = Path(__file__).resolve().parents[2]
CSV_PATH = ROOT / "math/checkerboard/lp/certificates/q_weights_exact.csv"
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/OuterGeometryCertificate.lean"


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
        slo,shi,slen=ordered(ma+mb,la+sigma*lb)
        dlo,dhi,dlen=ordered(ma-mb,la-sigma*lb)
        comps.append(dict(ai=ai,aj=aj,bi=bi,bj=bj,sigma=sigma,
            sslope=la+sigma*lb,dslope=la-sigma*lb,
            slo=slo,shi=shi,slen=slen,dlo=dlo,dhi=dhi,dlen=dlen))

    out=["import Checkerboard.LP.OuterGeometryBase",
         "import Checkerboard.LP.OuterSupportCertificate","",
         "/-!","# Generated pointwise geometry of the 35 outer couplings","",
         "Every affine component is shown to remain in its tabulated A/B, sum,",
         "and difference intervals and hence to map into `continuumTriangle`.","-/","",
         "namespace Checkerboard","","noncomputable section",""]

    # Endpoint evaluation and strict chain.
    endpoint_rhs=["0","outerQ","1 - outerR","outerH - 1","outerR",
                  "(outerH - outerQ) / 2","(outerH + outerQ) / 2","1"]
    for i,rhs in enumerate(endpoint_rhs):
        out += [f"theorem outerEndpointRep{i}_eval : outerEndpointRep{i}.eval = {rhs} := by"]
        if i==0 or i==7:
            out += [f"  norm_num [outerEndpointRep{i}, CubicRep.eval]",""]
        elif i==1:
            out += ["  rw [outerQ_reduced]",f"  norm_num [outerEndpointRep{i}, CubicRep.eval]",""]
        elif i==4:
            out += ["  rw [outerR_reduced]",f"  norm_num [outerEndpointRep{i}, CubicRep.eval]",""]
        else:
            out += ["  rw [outerQ_reduced, outerR_reduced, outerH_reduced]",
                    f"  norm_num [outerEndpointRep{i}, CubicRep.eval]","  ring",""]
    out += ["theorem outerEndpointRep_strict_order :",
            "    outerEndpointRep0.eval < outerEndpointRep1.eval ∧",
            "    outerEndpointRep1.eval < outerEndpointRep2.eval ∧",
            "    outerEndpointRep2.eval < outerEndpointRep3.eval ∧",
            "    outerEndpointRep3.eval < outerEndpointRep4.eval ∧",
            "    outerEndpointRep4.eval < outerEndpointRep5.eval ∧",
            "    outerEndpointRep5.eval < outerEndpointRep6.eval ∧",
            "    outerEndpointRep6.eval < outerEndpointRep7.eval := by",
            "  rw [outerEndpointRep0_eval, outerEndpointRep1_eval, outerEndpointRep2_eval,",
            "    outerEndpointRep3_eval, outerEndpointRep4_eval, outerEndpointRep5_eval,",
            "    outerEndpointRep6_eval, outerEndpointRep7_eval]",
            "  exact outer_breakpoint_order","",
            "theorem outerEndpointRep_nonneg (i : Fin 8) : 0 ≤ (match i.1 with",
            "    | 0 => outerEndpointRep0.eval | 1 => outerEndpointRep1.eval",
            "    | 2 => outerEndpointRep2.eval | 3 => outerEndpointRep3.eval",
            "    | 4 => outerEndpointRep4.eval | 5 => outerEndpointRep5.eval",
            "    | 6 => outerEndpointRep6.eval | _ => outerEndpointRep7.eval) := by",
            "  rcases outerEndpointRep_strict_order with ⟨h01,h12,h23,h34,h45,h56,h67⟩",
            "  fin_cases i <;> simp <;> nlinarith [outerEndpointRep0_eval]","" ]

    for i,z in enumerate(comps):
        ai,aj,bi,bj,sigma=z['ai'],z['aj'],z['bi'],z['bj'],z['sigma']
        bdef="affineIntervalPoint" if sigma==1 else "affineIntervalPointRev"
        out += [f"def outerCurveA{i} (t : ℝ) : ℝ :=",
                f"  affineIntervalPoint outerEndpointRep{ai}.eval outerEndpointRep{aj}.eval t",
                f"def outerCurveB{i} (t : ℝ) : ℝ :=",
                f"  {bdef} outerEndpointRep{bi}.eval outerEndpointRep{bj}.eval t","",
                f"theorem outerCurveA{i}_mem {{t : ℝ}}",
                "    (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :",
                f"    outerCurveA{i} t ∈ Set.Icc outerEndpointRep{ai}.eval outerEndpointRep{aj}.eval := by",
                "  apply affineIntervalPoint_mem_Icc","  · rcases outerEndpointRep_strict_order with ⟨h01,h12,h23,h34,h45,h56,h67⟩",
                "    nlinarith","  · exact ht","",
                f"theorem outerCurveB{i}_mem {{t : ℝ}}",
                "    (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :",
                f"    outerCurveB{i} t ∈ Set.Icc outerEndpointRep{bi}.eval outerEndpointRep{bj}.eval := by",
                f"  apply {'affineIntervalPoint_mem_Icc' if sigma==1 else 'affineIntervalPointRev_mem_Icc'}",
                "  · rcases outerEndpointRep_strict_order with ⟨h01,h12,h23,h34,h45,h56,h67⟩",
                "    nlinarith","  · exact ht","" ]

        # Sum/difference interval membership. Use exact midpoint endpoint forms.
        for kind,sign,lo_name,hi_name,len_name in [
            ('sum',1,f'outerSumLo{i}',f'outerSumHi{i}',f'outerSumLength{i}'),
            ('diff',-1,f'outerDiffLo{i}',f'outerDiffHi{i}',f'outerDiffLength{i}')]:
            slope=z['sslope'] if kind=='sum' else z['dslope']
            expr=f"outerCurveA{i} t {'+' if kind=='sum' else '-'} outerCurveB{i} t"
            mid_expr=(f"(outerEndpointRep{ai}.eval + outerEndpointRep{aj}.eval) / 2 "
                      f"{'+' if kind=='sum' else '-'} "
                      f"(outerEndpointRep{bi}.eval + outerEndpointRep{bj}.eval) / 2")
            slope_expr=(f"(outerEndpointRep{aj}.eval - outerEndpointRep{ai}.eval) "
                        f"{'+' if (kind=='sum' and sigma==1) or (kind=='diff' and sigma==-1) else '-'} "
                        f"(outerEndpointRep{bj}.eval - outerEndpointRep{bi}.eval)")
            positive=slope.decimal()>=0
            out += [f"theorem outerCurve_{kind}{i}_mem {{t : ℝ}}",
                    "    (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :",
                    f"    {expr} ∈ Set.Icc {lo_name}.eval {hi_name}.eval := by",
                    f"  have hs : {'0 < '+slope_expr if positive else slope_expr+' < 0'} := by"]
            if positive:
                out += [f"    have hp := {len_name}_pos",
                        f"    have heq : {slope_expr} = {len_name}.eval := by",
                        f"      norm_num [outerEndpointRep{ai}, outerEndpointRep{aj}, outerEndpointRep{bi},",
                        f"        outerEndpointRep{bj}, {len_name}, CubicRep.eval]","      ring",
                        "    nlinarith"]
            else:
                out += [f"    have hp := {len_name}_pos",
                        f"    have heq : -({slope_expr}) = {len_name}.eval := by",
                        f"      norm_num [outerEndpointRep{ai}, outerEndpointRep{aj}, outerEndpointRep{bi},",
                        f"        outerEndpointRep{bj}, {len_name}, CubicRep.eval]","      ring",
                        "    nlinarith"]
            # endpoint exact identities
            if positive:
                lo_formula=f"{mid_expr} - ({slope_expr}) / 2"
                hi_formula=f"{mid_expr} + ({slope_expr}) / 2"
            else:
                lo_formula=f"{mid_expr} + ({slope_expr}) / 2"
                hi_formula=f"{mid_expr} - ({slope_expr}) / 2"
            out += [f"  have hlo : {lo_name}.eval = {lo_formula} := by",
                    f"    norm_num [{lo_name}, outerEndpointRep{ai}, outerEndpointRep{aj},",
                    f"      outerEndpointRep{bi}, outerEndpointRep{bj}, CubicRep.eval]","    ring",
                    f"  have hhi : {hi_name}.eval = {hi_formula} := by",
                    f"    norm_num [{hi_name}, outerEndpointRep{ai}, outerEndpointRep{aj},",
                    f"      outerEndpointRep{bi}, outerEndpointRep{bj}, CubicRep.eval]","    ring",
                    f"  have hcurve : {expr} = {mid_expr} + ({slope_expr}) * t := by",
                    f"    simp [outerCurveA{i}, outerCurveB{i}, affineIntervalPoint, affineIntervalPointRev]",
                    "    ring","  rcases ht with ⟨htl,htu⟩","  rw [hcurve, hlo, hhi]","  constructor"]
            if positive:
                out += ["  · have hp := mul_nonneg (le_of_lt hs) (by linarith : 0 ≤ t + 1 / 2)","    nlinarith",
                        "  · have hp := mul_nonneg (le_of_lt hs) (by linarith : 0 ≤ 1 / 2 - t)","    nlinarith",""]
            else:
                out += ["  · have hp := mul_nonneg (by linarith : 0 ≤ -("+slope_expr+"))",
                        "        (by linarith : 0 ≤ 1 / 2 - t)","    nlinarith",
                        "  · have hp := mul_nonneg (by linarith : 0 ≤ -("+slope_expr+"))",
                        "        (by linarith : 0 ≤ t + 1 / 2)","    nlinarith",""]

        out += [f"def outerMappedPoint{i} (t : ℝ) : ContinuumPoint :=",
                f"  (checkerboardP + outerLength * outerCurveA{i} t,",
                f"    outerLength * outerCurveB{i} t)","",
                f"theorem outerMappedPoint{i}_mem {{t : ℝ}}",
                "    (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :",
                f"    outerMappedPoint{i} t ∈ continuumTriangle := by",
                f"  have ha := outerCurveA{i}_mem ht",
                f"  have hb := outerCurveB{i}_mem ht",
                f"  have hs := outerCurve_sum{i}_mem ht",
                f"  have hd := outerCurve_diff{i}_mem ht",
                f"  have ha0 : 0 ≤ outerCurveA{i} t := by",
                f"    have h0 := outerEndpointRep_nonneg ⟨{ai}, by norm_num⟩","    linarith",
                f"  have hb0 : 0 ≤ outerCurveB{i} t := by",
                f"    have h0 := outerEndpointRep_nonneg ⟨{bi}, by norm_num⟩","    linarith",
                f"  have hdiff : -outerR ≤ outerCurveA{i} t - outerCurveB{i} t := by",
                f"    have hband := outerDiffFloorSlack{i}_order",
                "    rw [outerNegRRep_eval] at hband","    linarith",
                f"  have hsum : outerCurveA{i} t + outerCurveB{i} t ≤ outerH := by",
                f"    have hband := outerSumHiSlack{i}_order",
                "    rw [outerHRep_eval] at hband","    linarith",
                f"  exact outer_scaled_point_mem_triangle ha0 hb0 hdiff hsum","" ]

    out += ["def outerMappedPoint (i : Fin 35) (t : ℝ) : ContinuumPoint :=",
            "  match i.1 with"]
    for i in range(35): out.append(f"  | {i} => outerMappedPoint{i} t")
    out += ["  | _ => outerMappedPoint34 t","",
            "theorem outerMappedPoint_mem (i : Fin 35) {t : ℝ}",
            "    (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :",
            "    outerMappedPoint i t ∈ continuumTriangle := by",
            "  fin_cases i"]
    for i in range(35): out += [f"  · simpa [outerMappedPoint] using outerMappedPoint{i}_mem ht"]
    out += ["","end","","end Checkerboard",""]
    return "\n".join(out)


def main():
    rows=list(csv.DictReader(CSV_PATH.open(newline='',encoding='utf-8')))
    if len(rows)!=35: raise SystemExit(f"expected 35 rows, got {len(rows)}")
    LEAN_PATH.parent.mkdir(parents=True,exist_ok=True)
    LEAN_PATH.write_text(generate(rows),encoding='utf-8')
    print(f"wrote {LEAN_PATH}")

if __name__=='__main__': main()
