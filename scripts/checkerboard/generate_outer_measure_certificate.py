#!/usr/bin/env python3
"""Generate the normalized 35-component outer coupling measure proof."""
from __future__ import annotations

import csv
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CSV_PATH = ROOT / "math/checkerboard/lp/certificates/q_weights_exact.csv"
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/OuterMeasureCertificate.lean"


def match_def(name, typ, bodies, args=""):
    out = [f"def {name} (i : Fin 35){args} : {typ} :=", "  match i.1 with"]
    for j, body in enumerate(bodies[:-1]):
        out.append(f"  | {j} => {body}")
    out.append(f"  | _ => {bodies[-1]}")
    out.append("")
    return out


def generate(rows):
    from generate_outer_density_certificate import K

    out = [
        "import Checkerboard.LP.OuterMarginalAE",
        "import Checkerboard.LP.OuterProjectionAE",
        "",
        "/-!",
        "# The normalized 35-component outer coupling measure",
        "",
        "This generated module assembles the exact affine components into one",
        "probability coupling and proves its two coordinate marginals and paired",
        "sum/difference projection by the generated density certificates.",
        "-/",
        "",
        "namespace Checkerboard",
        "",
        "noncomputable section",
        "",
        "open MeasureTheory Set",
        "",
    ]

    out += match_def("outerNormalizedA", "ℝ", [f"outerCurveA{i} t" for i in range(35)], " (t : ℝ)")
    out += match_def("outerNormalizedB", "ℝ", [f"outerCurveB{i} t" for i in range(35)], " (t : ℝ)")
    out += match_def("outerWeightValue", "ℝ", [f"outerWeight{i}.eval" for i in range(35)])

    a_dens, b_dens, p_dens = [], [], []
    for i, row in enumerate(rows):
        ai, aj = int(row["A_lo_idx"]), int(row["A_hi_idx"])
        bi, bj = int(row["B_lo_idx"]), int(row["B_hi_idx"])
        a_dens.append(
            f"intervalDensity outerEndpointRep{ai}.eval outerEndpointRep{aj}.eval outerADensity{i}.eval x"
        )
        b_dens.append(
            f"intervalDensity outerEndpointRep{bi}.eval outerEndpointRep{bj}.eval outerBDensity{i}.eval x"
        )
        p_dens.append(
            f"intervalDensity outerSumLo{i}.eval outerSumHi{i}.eval outerSumDensity{i}.eval x + "
            f"intervalDensity outerDiffLo{i}.eval outerDiffHi{i}.eval outerDiffDensity{i}.eval x"
        )
    out += match_def("outerAComponentDensity", "ℝ≥0∞", a_dens, " (x : ℝ)")
    out += match_def("outerBComponentDensity", "ℝ≥0∞", b_dens, " (x : ℝ)")
    out += match_def("outerProjectionComponentDensity", "ℝ≥0∞", p_dens, " (x : ℝ)")

    out += [
        "def outerNormalizedPair (i : Fin 35) (t : ℝ) : ℝ × ℝ :=",
        "  (outerNormalizedA i t, outerNormalizedB i t)",
        "",
        "def outerComponentMeasure (i : Fin 35) : Measure (ℝ × ℝ) :=",
        "  ENNReal.ofReal (outerWeightValue i) •",
        "    Measure.map (outerNormalizedPair i) centeredUnitIntervalMeasure",
        "",
        "theorem measurable_outerNormalizedPair (i : Fin 35) :",
        "    Measurable (outerNormalizedPair i) := by",
        "  fin_cases i <;> simp [outerNormalizedPair, outerNormalizedA, outerNormalizedB] <;> fun_prop",
        "",
        "theorem outerWeightValue_pos (i : Fin 35) : 0 < outerWeightValue i := by",
        "  fin_cases i",
    ]
    for i in range(35):
        out.append(f"  · simpa [outerWeightValue] using outerWeight{i}_pos")
    out += [
        "",
        "theorem outerWeightValue_sum : ∑ i : Fin 35, outerWeightValue i = 1 := by",
        "  simpa [outerWeightValue, Fin.sum_univ_succ] using outerWeight_eval_sum",
        "",
        "theorem measurable_outerAComponentDensity (i : Fin 35) :",
        "    Measurable (outerAComponentDensity i) := by",
        "  fin_cases i <;> simp [outerAComponentDensity] <;> apply measurable_intervalDensity",
        "",
        "theorem measurable_outerBComponentDensity (i : Fin 35) :",
        "    Measurable (outerBComponentDensity i) := by",
        "  fin_cases i <;> simp [outerBComponentDensity] <;> apply measurable_intervalDensity",
        "",
        "theorem measurable_outerProjectionComponentDensity (i : Fin 35) :",
        "    Measurable (outerProjectionComponentDensity i) := by",
        "  fin_cases i <;> simp [outerProjectionComponentDensity] <;> fun_prop",
        "",
    ]

    for i, row in enumerate(rows):
        ai, aj = int(row["A_lo_idx"]), int(row["A_hi_idx"])
        bi, bj = int(row["B_lo_idx"]), int(row["B_hi_idx"])
        sigma = int(row["sigma"])
        pair = f"(fun t : ℝ => (outerCurveA{i} t, outerCurveB{i} t))"
        weight = f"outerWeight{i}.eval"
        cases = [
            ("fst", "Prod.fst", ai, aj, f"outerALength{i}", f"outerADensity{i}", f"outerCurveA{i}", 1),
            ("snd", "Prod.snd", bi, bj, f"outerBLength{i}", f"outerBDensity{i}", f"outerCurveB{i}", sigma),
        ]
        for kind, coord, lo_idx, hi_idx, length, density, curve, orient in cases:
            lo = f"outerEndpointRep{lo_idx}.eval"
            hi = f"outerEndpointRep{hi_idx}.eval"
            lemma = "weighted_map_centered_interval_affine" if orient == 1 else "weighted_map_centered_interval_affine_neg"
            sign = "+" if orient == 1 else "-"
            curve_base = "affineIntervalPoint" if orient == 1 else "affineIntervalPointRev"
            out += [
                f"theorem outerComponent_{kind}{i} :",
                f"    Measure.map {coord}",
                f"      (ENNReal.ofReal {weight} • Measure.map {pair} centeredUnitIntervalMeasure) =",
                f"      volume.withDensity (intervalDensity {lo} {hi} {density}.eval) := by",
                "  rw [Measure.map_smul]",
                "  rw [Measure.map_map (by fun_prop) (by fun_prop)]",
                f"  change ENNReal.ofReal {weight} • Measure.map (fun t : ℝ => {curve} t)",
                "      centeredUnitIntervalMeasure = _",
                f"  have hlen : {hi} - {lo} = {length}.eval := by",
                f"    norm_num [outerEndpointRep{lo_idx}, outerEndpointRep{hi_idx}, {length}, CubicRep.eval]",
                "    ring",
                f"  have hfun : (fun t : ℝ => {curve} t) =",
                f"      (fun t : ℝ => ({lo} + {hi}) / 2 {sign} {length}.eval * t) := by",
                "    funext t",
                f"    simp [{curve}, {curve_base}, hlen]",
                "  rw [hfun]",
                f"  have hbase := {lemma}",
                f"    (w := {weight}) (m := ({lo} + {hi}) / 2)",
                f"    (s := {length}.eval) (le_of_lt outerWeight{i}_pos) {length}_pos",
                f"  have hlo : ({lo} + {hi}) / 2 - {length}.eval / 2 = {lo} := by",
                "    rw [← hlen]",
                "    ring",
                f"  have hhi : ({lo} + {hi}) / 2 + {length}.eval / 2 = {hi} := by",
                "    rw [← hlen]",
                "    ring",
                f"  rw [hlo, hhi, {density}_ratio] at hbase",
                "  exact hbase",
                "",
            ]

    r = K(Fraction(539, 912), Fraction(487, 456), Fraction(-1203, 304))
    q = K(Fraction(-713, 912), Fraction(871, 152), Fraction(-6817, 912))
    h = K(Fraction(-47, 304), Fraction(4739, 456), Fraction(-10025, 912))
    endpoints = [K(0), q, K(1) - r, h - K(1), r, (h - q) * Fraction(1, 2), (h + q) * Fraction(1, 2), K(1)]

    for i, row in enumerate(rows):
        ai, aj = int(row["A_lo_idx"]), int(row["A_hi_idx"])
        bi, bj = int(row["B_lo_idx"]), int(row["B_hi_idx"])
        sigma = int(row["sigma"])
        la, lb = endpoints[aj] - endpoints[ai], endpoints[bj] - endpoints[bi]
        slopes = {"sum": la + sigma * lb, "diff": la - sigma * lb}
        pair = f"(fun t : ℝ => (outerCurveA{i} t, outerCurveB{i} t))"
        weight = f"outerWeight{i}.eval"
        for kind, op, length, density, lo, hi in [
            ("sum", "+", f"outerSumLength{i}", f"outerSumDensity{i}", f"outerSumLo{i}.eval", f"outerSumHi{i}.eval"),
            ("diff", "-", f"outerDiffLength{i}", f"outerDiffDensity{i}", f"outerDiffLo{i}.eval", f"outerDiffHi{i}.eval"),
        ]:
            orient = 1 if slopes[kind].decimal() >= 0 else -1
            lemma = "weighted_map_centered_interval_affine" if orient == 1 else "weighted_map_centered_interval_affine_neg"
            sign = "+" if orient == 1 else "-"
            projection = f"(fun z : ℝ × ℝ => z.1 {op} z.2)"
            curve_expr = f"outerCurveA{i} t {op} outerCurveB{i} t"
            out += [
                f"theorem outerComponent_{kind}{i} :",
                f"    Measure.map {projection}",
                f"      (ENNReal.ofReal {weight} • Measure.map {pair} centeredUnitIntervalMeasure) =",
                f"      volume.withDensity (intervalDensity {lo} {hi} {density}.eval) := by",
                "  rw [Measure.map_smul]",
                "  rw [Measure.map_map (by fun_prop) (by fun_prop)]",
                f"  change ENNReal.ofReal {weight} • Measure.map (fun t : ℝ => {curve_expr})",
                "      centeredUnitIntervalMeasure = _",
                f"  have hfun : (fun t : ℝ => {curve_expr}) =",
                f"      (fun t : ℝ => ({lo} + {hi}) / 2 {sign} {length}.eval * t) := by",
                "    funext t",
                f"    simp [outerCurveA{i}, outerCurveB{i}, affineIntervalPoint, affineIntervalPointRev]",
                f"    norm_num [outerEndpointRep{ai}, outerEndpointRep{aj}, outerEndpointRep{bi}, outerEndpointRep{bj},",
                f"      {lo.split('.')[0]}, {hi.split('.')[0]}, {length}, CubicRep.eval]",
                "    ring",
                f"  have hlen : {hi} - {lo} = {length}.eval := by",
                f"    norm_num [{lo.split('.')[0]}, {hi.split('.')[0]}, {length}, CubicRep.eval]",
                "    ring",
                "  rw [hfun]",
                f"  have hbase := {lemma}",
                f"    (w := {weight}) (m := ({lo} + {hi}) / 2)",
                f"    (s := {length}.eval) (le_of_lt outerWeight{i}_pos) {length}_pos",
                f"  have hlo : ({lo} + {hi}) / 2 - {length}.eval / 2 = {lo} := by",
                "    rw [← hlen]",
                "    ring",
                f"  have hhi : ({lo} + {hi}) / 2 + {length}.eval / 2 = {hi} := by",
                "    rw [← hlen]",
                "    ring",
                f"  rw [hlo, hhi, {density}_ratio] at hbase",
                "  exact hbase",
                "",
            ]

    for kind, density_def, theorem_prefix in [
        ("fst", "outerAComponentDensity", "outerComponent_fst"),
        ("snd", "outerBComponentDensity", "outerComponent_snd"),
    ]:
        coord = "Prod.fst" if kind == "fst" else "Prod.snd"
        out += [
            f"theorem outerComponentMeasure_{kind} (i : Fin 35) :",
            f"    Measure.map {coord} (outerComponentMeasure i) =",
            f"      volume.withDensity ({density_def} i) := by",
            "  fin_cases i",
        ]
        for i in range(35):
            out += [
                f"  · simpa [outerComponentMeasure, outerNormalizedPair, outerNormalizedA,",
                f"      outerNormalizedB, outerWeightValue, {density_def}] using {theorem_prefix}{i}",
            ]
        out.append("")

    for kind in ["sum", "diff"]:
        op = "+" if kind == "sum" else "-"
        cap = kind.capitalize()
        projection = f"(fun z : ℝ × ℝ => z.1 {op} z.2)"
        out += [
            f"theorem outerComponentMeasure_{kind} (i : Fin 35) :",
            f"    Measure.map {projection} (outerComponentMeasure i) =",
            "      volume.withDensity (match i.1 with",
        ]
        for i in range(34):
            out.append(
                f"        | {i} => intervalDensity outer{cap}Lo{i}.eval outer{cap}Hi{i}.eval outer{cap}Density{i}.eval"
            )
        out += [
            f"        | _ => intervalDensity outer{cap}Lo34.eval outer{cap}Hi34.eval outer{cap}Density34.eval) := by",
            "  fin_cases i",
        ]
        for i in range(35):
            out += [
                "  · simpa [outerComponentMeasure, outerNormalizedPair, outerNormalizedA,",
                f"      outerNormalizedB, outerWeightValue] using outerComponent_{kind}{i}",
            ]
        out.append("")

    out += [
        "theorem outerADensityFunction_eq_component_sum (x : ℝ) :",
        "    outerADensityFunction x = ∑ i : Fin 35, outerAComponentDensity i x := by",
        "  simp [outerADensityFunction, outerAComponentDensity, Fin.sum_univ_succ, add_assoc]",
        "",
        "theorem outerBDensityFunction_eq_component_sum (x : ℝ) :",
        "    outerBDensityFunction x = ∑ i : Fin 35, outerBComponentDensity i x := by",
        "  simp [outerBDensityFunction, outerBComponentDensity, Fin.sum_univ_succ, add_assoc]",
        "",
        "theorem outerProjectionDensityFunction_eq_component_sum (x : ℝ) :",
        "    outerProjectionDensityFunction x = ∑ i : Fin 35, outerProjectionComponentDensity i x := by",
        "  simp [outerProjectionDensityFunction, outerProjectionComponentDensity, Fin.sum_univ_succ, add_assoc]",
        "",
        "def outerNormalizedCoupling : Measure (ℝ × ℝ) := ∑ i : Fin 35, outerComponentMeasure i",
        "",
    ]

    for kind, coord, density, measurable_density, density_sum, final_theorem, full_density in [
        ("fst", "Prod.fst", "outerAComponentDensity", "measurable_outerAComponentDensity", "outerADensityFunction_eq_component_sum", "volume_withDensity_outerADensity", "outerADensityFunction"),
        ("snd", "Prod.snd", "outerBComponentDensity", "measurable_outerBComponentDensity", "outerBDensityFunction_eq_component_sum", "volume_withDensity_outerBDensity", "outerBDensityFunction"),
    ]:
        out += [
            f"theorem outerNormalizedCoupling_{kind} :",
            f"    Measure.map {coord} outerNormalizedCoupling =",
            "      volume.restrict (Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval) := by",
            "  calc",
            f"    Measure.map {coord} outerNormalizedCoupling =",
            f"        ∑ i : Fin 35, Measure.map {coord} (outerComponentMeasure i) := by",
            f"      exact map_fintype_sum outerComponentMeasure {coord} (by fun_prop)",
            f"    _ = ∑ i : Fin 35, volume.withDensity ({density} i) := by",
            "      apply Finset.sum_congr rfl",
            "      intro i hi",
            f"      exact outerComponentMeasure_{kind} i",
            f"    _ = volume.withDensity (fun x => ∑ i : Fin 35, {density} i x) := by",
            f"      symm; exact withDensity_finset_sum Finset.univ {density} (fun i _ => {measurable_density} i)",
            f"    _ = volume.withDensity {full_density} := by",
            "      congr 1",
            "      funext x",
            f"      exact ({density_sum} x).symm",
            "    _ = volume.restrict (Set.Icc outerEndpointRep0.eval outerEndpointRep7.eval) :=",
            f"      {final_theorem}",
            "",
        ]

    out += [
        "theorem outerComponentMeasure_projection (i : Fin 35) :",
        "    Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (outerComponentMeasure i) +",
        "      Measure.map (fun z : ℝ × ℝ => z.1 - z.2) (outerComponentMeasure i) =",
        "      volume.withDensity (outerProjectionComponentDensity i) := by",
        "  rw [outerComponentMeasure_sum i, outerComponentMeasure_diff i]",
        "  symm",
        "  apply withDensity_add_left",
        "  fin_cases i <;>",
        "    simp [outerProjectionComponentDensity] <;> apply measurable_intervalDensity",
        "",
        "theorem outerNormalizedCoupling_projection :",
        "    Measure.map (fun z : ℝ × ℝ => z.1 + z.2) outerNormalizedCoupling +",
        "      Measure.map (fun z : ℝ × ℝ => z.1 - z.2) outerNormalizedCoupling =",
        "      volume.withDensity outerProjectionTargetDensity := by",
        "  rw [map_fintype_sum outerComponentMeasure (fun z : ℝ × ℝ => z.1 + z.2) (by fun_prop)]",
        "  rw [map_fintype_sum outerComponentMeasure (fun z : ℝ × ℝ => z.1 - z.2) (by fun_prop)]",
        "  rw [← Finset.sum_add_distrib]",
        "  calc",
        "    (∑ i : Fin 35, (Measure.map (fun z : ℝ × ℝ => z.1 + z.2) (outerComponentMeasure i) +",
        "      Measure.map (fun z : ℝ × ℝ => z.1 - z.2) (outerComponentMeasure i))) =",
        "        ∑ i : Fin 35, volume.withDensity (outerProjectionComponentDensity i) := by",
        "      apply Finset.sum_congr rfl",
        "      intro i hi",
        "      exact outerComponentMeasure_projection i",
        "    _ = volume.withDensity (fun x => ∑ i : Fin 35, outerProjectionComponentDensity i x) := by",
        "      symm; exact withDensity_finset_sum Finset.univ outerProjectionComponentDensity",
        "        (fun i _ => measurable_outerProjectionComponentDensity i)",
        "    _ = volume.withDensity outerProjectionDensityFunction := by",
        "      congr 1",
        "      funext x",
        "      exact (outerProjectionDensityFunction_eq_component_sum x).symm",
        "    _ = volume.withDensity outerProjectionTargetDensity :=",
        "      volume_withDensity_outerProjectionDensity",
        "",
        "end",
        "",
        "end Checkerboard",
        "",
    ]
    return "\n".join(out)


def main():
    rows = list(csv.DictReader(CSV_PATH.open(newline="", encoding="utf-8")))
    if len(rows) != 35:
        raise SystemExit(f"expected 35 rows, got {len(rows)}")
    LEAN_PATH.parent.mkdir(parents=True, exist_ok=True)
    LEAN_PATH.write_text(generate(rows), encoding="utf-8")
    print(f"wrote {LEAN_PATH}")


if __name__ == "__main__":
    main()
