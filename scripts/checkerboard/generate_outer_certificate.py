#!/usr/bin/env python3
"""Generate Lean source for the exact 35-component outer transport certificate.

The embedded gzip/base64 payload is a lossless transcription of the exact
q_weights certificate recovered from the checkerboard proof archive.  The
generator is not trusted: every emitted sign and sum identity is rechecked by
Lean using rational arithmetic and the exact isolating interval for p.
"""

from __future__ import annotations

import base64
import csv
import gzip
import hashlib
import io
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CSV_PATH = ROOT / "math/checkerboard/lp/certificates/q_weights_exact.csv"
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/OuterCertificateData.lean"

DATA_GZ_B64 = """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"""
LOGICAL_SHA256 = "c78f596c63216ec700299213933ed604c2e243dc14a8882add10a24f939c7b2b"

P_LO = Fraction(2115883, 10_000_000)
P_HI = Fraction(2115884, 10_000_000)


def qlean(text: str) -> str:
    q = Fraction(text)
    if q.denominator == 1:
        return str(q.numerator)
    if q.numerator < 0:
        return f"(-{abs(q.numerator)} / {q.denominator} : ℚ)"
    return f"({q.numerator} / {q.denominator} : ℚ)"


def sign_kind(row: dict[str, str]) -> str:
    b = Fraction(row["weight_p"])
    c = Fraction(row["weight_p2"])
    if c < 0:
        return "concave"
    vertex = -b / (2 * c)
    if vertex <= P_LO:
        return "left"
    if vertex >= P_HI:
        return "right"
    raise RuntimeError(f"unexpected interior vertex for row {row['index']}")


def generate_lean(rows: list[dict[str, str]]) -> str:
    out: list[str] = [
        "import Checkerboard.LP.CubicInterval",
        "",
        "/-!",
        "# Exact 35-component outer transport data",
        "",
        "This file is generated by `scripts/checkerboard/generate_outer_certificate.py`.",
        "Every sign and coefficient-sum proof is checked in the Lean kernel.",
        "-/",
        "",
        "namespace Checkerboard",
        "",
        "noncomputable section",
        "",
        "structure CubicWeight where",
        "  constant : ℚ",
        "  linear : ℚ",
        "  quadratic : ℚ",
        "  deriving DecidableEq, Repr",
        "",
        "def CubicWeight.eval (w : CubicWeight) : ℝ :=",
        "  evalAtCheckerboardP w.constant w.linear w.quadratic",
        "",
        "structure OuterComponent where",
        "  aLo : Nat",
        "  aHi : Nat",
        "  bLo : Nat",
        "  bHi : Nat",
        "  sigma : Int",
        "  weight : CubicWeight",
        "  deriving DecidableEq, Repr",
        "",
    ]

    for i, row in enumerate(rows):
        a = qlean(row["weight_const"])
        b = qlean(row["weight_p"])
        c = qlean(row["weight_p2"])
        out.extend([
            f"def outerWeight{i} : CubicWeight :=",
            f"  ⟨{a}, {b}, {c}⟩",
            "",
            f"theorem outerWeight{i}_pos : 0 < outerWeight{i}.eval := by",
            f"  change 0 < evalAtCheckerboardP {a} {b} {c}",
        ])
        kind = sign_kind(row)
        if kind == "concave":
            out.extend([
                "  apply evalAtCheckerboardP_pos_of_concave",
                "  · norm_num",
                "  · norm_num [quadraticAt, pLower]",
                "  · norm_num [quadraticAt, pUpper]",
            ])
        elif kind == "left":
            out.extend([
                "  apply evalAtCheckerboardP_pos_of_left",
                "  · norm_num",
                "  · norm_num [pLower]",
                "  · norm_num [quadraticAt, pLower]",
            ])
        else:
            out.extend([
                "  apply evalAtCheckerboardP_pos_of_right",
                "  · norm_num",
                "  · norm_num [pUpper]",
                "  · norm_num [quadraticAt, pUpper]",
            ])
        out.append("")

    out.extend([
        "def outerComponent (i : Fin 35) : OuterComponent :=",
        "  match i.1 with",
    ])
    for i, row in enumerate(rows):
        out.append(
            f"  | {i} => ⟨{row['A_lo_idx']}, {row['A_hi_idx']}, "
            f"{row['B_lo_idx']}, {row['B_hi_idx']}, {row['sigma']}, outerWeight{i}⟩"
        )
    out.extend([
        "  | _ => ⟨6, 7, 2, 5, -1, outerWeight34⟩",
        "",
        "theorem outerComponent_indices_valid (i : Fin 35) :",
        "    (outerComponent i).aLo < 8 ∧ (outerComponent i).aHi < 8 ∧",
        "    (outerComponent i).bLo < 8 ∧ (outerComponent i).bHi < 8 := by",
        "  fin_cases i <;> norm_num [outerComponent]",
        "",
        "theorem outerComponent_intervals_nontrivial (i : Fin 35) :",
        "    (outerComponent i).aLo < (outerComponent i).aHi ∧",
        "    (outerComponent i).bLo < (outerComponent i).bHi := by",
        "  fin_cases i <;> norm_num [outerComponent]",
        "",
        "theorem outerComponent_sigma (i : Fin 35) :",
        "    (outerComponent i).sigma = 1 ∨ (outerComponent i).sigma = -1 := by",
        "  fin_cases i <;> norm_num [outerComponent]",
        "",
        "theorem outerComponent_weight_pos (i : Fin 35) :",
        "    0 < (outerComponent i).weight.eval := by",
        "  fin_cases i",
    ])
    for i in range(35):
        out.append(f"  · simpa [outerComponent] using outerWeight{i}_pos")
    out.append("")

    names = [f"outerWeight{i}" for i in range(35)]
    defs = ", ".join(names)
    for field, rhs in (("constant", "1"), ("linear", "0"), ("quadratic", "0")):
        expr = " +\n      ".join(f"{name}.{field}" for name in names)
        out.extend([
            f"theorem outerWeight_{field}_sum :",
            f"    {expr} = {rhs} := by",
            f"  norm_num [{defs}]",
            "",
        ])

    eval_expr = " +\n      ".join(f"{name}.eval" for name in names)
    const_expr = " + ".join(f"(({name}.constant : ℝ))" for name in names)
    linear_expr = " + ".join(f"(({name}.linear : ℝ))" for name in names)
    quadratic_expr = " + ".join(f"(({name}.quadratic : ℝ))" for name in names)
    out.extend([
        "/-- The 35 exact positive mixture weights sum to one. -/",
        "theorem outerWeight_eval_sum :",
        f"    {eval_expr} = 1 := by",
        f"  have hc : {const_expr} = 1 := by",
        "    exact_mod_cast outerWeight_constant_sum",
        f"  have hl : {linear_expr} = 0 := by",
        "    exact_mod_cast outerWeight_linear_sum",
        f"  have hq : {quadratic_expr} = 0 := by",
        "    exact_mod_cast outerWeight_quadratic_sum",
        "  simp only [CubicWeight.eval, evalAtCheckerboardP, quadraticAt]",
        "  linear_combination hc + checkerboardP * hl + checkerboardP ^ 2 * hq",
        "",
        "end",
        "",
        "end Checkerboard",
        "",
    ])
    return "\n".join(out)


def main() -> None:
    raw = gzip.decompress(base64.b64decode(DATA_GZ_B64))
    if hashlib.sha256(raw).hexdigest() != LOGICAL_SHA256:
        raise SystemExit("embedded certificate checksum mismatch")
    rows = list(csv.DictReader(io.StringIO(raw.decode("utf-8"))))
    if len(rows) != 35:
        raise SystemExit(f"expected 35 rows, got {len(rows)}")
    if [int(row["index"]) for row in rows] != list(range(35)):
        raise SystemExit("certificate row indices are not 0..34")

    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    LEAN_PATH.parent.mkdir(parents=True, exist_ok=True)
    CSV_PATH.write_bytes(raw)
    LEAN_PATH.write_text(generate_lean(rows), encoding="utf-8")
    print(f"wrote {CSV_PATH}")
    print(f"wrote {LEAN_PATH}")


if __name__ == "__main__":
    main()
