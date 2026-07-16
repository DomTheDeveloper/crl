#!/usr/bin/env python3
"""Generate exact endpoint identities and signs for the reduced dual profiles."""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path

import sympy as sp

from generate_outer_density_certificate import K, qlean, rep_literal, sign_kind

ROOT = Path(__file__).resolve().parents[2]
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/DualFunctionIdentities.lean"
p = sp.symbols("p")

P = K(0, 1, 0)
c = K(F(5, 76), F(64, 19), F(-401, 76))
d = K(F(71, 76), F(-45, 19), F(401, 76))
e = K(F(-33, 152), F(185, 76), F(-401, 152))
f = K(F(33, 152), F(-33, 76), F(401, 152))
g = K(F(43, 76), F(71, 38), F(-401, 76))
Kd = K(F(-1098531, 144400), F(13195599, 288800), F(-22897171, 577600))
rd = K(F(810789, 288800), F(-12744461, 577600), F(1294527, 57760))
s = K(F(489993, 144400), F(-420003, 14440), F(4499223, 144400))
ell = K(F(-1230561, 577600), F(4736889, 288800), F(-7718857, 577600))
qq = K(F(1317747, 577600), F(-3032869, 144400), F(31570701, 1155200))
n1 = K(F(-204729, 144400), F(335581, 36100), F(-5146329, 577600))
nu = K(F(-128871, 288800), F(4580837, 577600), F(-5000067, 577600))
n2 = K(F(-625473, 144400), F(4681961, 144400), F(-19965051, 577600))


def poly(value: K):
    return (
        sp.Rational(value.a.numerator, value.a.denominator)
        + sp.Rational(value.b.numerator, value.b.denominator) * p
        + sp.Rational(value.c.numerator, value.c.denominator) * p**2
    )


def A1(t):
    return -Kd*t*t - 2*rd*t + n1


def AL(t):
    return ell*t + nu


def A2(t):
    return -Kd*t*t + 2*Kd*t + n2


def BQ(t):
    return F(1, 2)*Kd*t*t + rd*t + s


def BL(t):
    return -ell*t + qq


UNFOLD = (
    "certifiedDualA1, certifiedDualAL, certifiedDualA2, certifiedDualBQ, certifiedDualBL, "
    "certifiedDualK, certifiedDualR, certifiedDualS, certifiedDualEll, certifiedDualQ, "
    "certifiedDualN1, certifiedDualNu, certifiedDualN2, certifiedDualKRep, certifiedDualRRep, "
    "certifiedDualSRep, certifiedDualEllRep, certifiedDualQRep, certifiedDualN1Rep, "
    "certifiedDualNuRep, certifiedDualN2Rep, CubicRep.eval, primalC_reduced, primalD_reduced, "
    "primalE_reduced, primalF_reduced, primalG_reduced"
)

VALUES = [
    ("dualA1_p", "certifiedDualA1 checkerboardP", -poly(Kd)*p**2 - 2*poly(rd)*p + poly(n1), A1(P)),
    ("dualA1_c", "certifiedDualA1 primalC", -poly(Kd)*poly(c)**2 - 2*poly(rd)*poly(c) + poly(n1), A1(c)),
    ("dualAL_c", "certifiedDualAL primalC", poly(ell)*poly(c) + poly(nu), AL(c)),
    ("dualAL_d", "certifiedDualAL primalD", poly(ell)*poly(d) + poly(nu), AL(d)),
    ("dualA2_d", "certifiedDualA2 primalD", -poly(Kd)*poly(d)**2 + 2*poly(Kd)*poly(d) + poly(n2), A2(d)),
    ("dualA2_one", "certifiedDualA2 1", -poly(Kd) + 2*poly(Kd) + poly(n2), A2(K(1))),
    ("dualBQ_zero", "certifiedDualBQ 0", poly(s), BQ(K(0))),
    ("dualBQ_e", "certifiedDualBQ primalE", sp.Rational(1, 2)*poly(Kd)*poly(e)**2 + poly(rd)*poly(e) + poly(s), BQ(e)),
    ("dualBL_e", "certifiedDualBL primalE", -poly(ell)*poly(e) + poly(qq), BL(e)),
    ("dualBL_f", "certifiedDualBL primalF", -poly(ell)*poly(f) + poly(qq), BL(f)),
    ("dualBQ_f", "certifiedDualBQ primalF", sp.Rational(1, 2)*poly(Kd)*poly(f)**2 + poly(rd)*poly(f) + poly(s), BQ(f)),
    ("dualBQ_g", "certifiedDualBQ primalG", sp.Rational(1, 2)*poly(Kd)*poly(g)**2 + poly(rd)*poly(g) + poly(s), BQ(g)),
]


def quotient(raw, remainder):
    cubic = 401*p**3 - 331*p**2 + 19*p + 7
    q, r = sp.div(sp.expand(raw-remainder), cubic, p)
    if sp.expand(r) != 0:
        raise RuntimeError(f"nonzero cubic remainder: {r}")
    return sp.factor(q)


def lean_sympy(expression):
    return sp.sstr(sp.factor(expression)).replace("**", "^")


def emit_positive(out, name, representative):
    if representative == K(0):
        out += [
            f"theorem {name}_nonneg : 0 ≤ {name}Rep.eval := by",
            f"  norm_num [{name}Rep, CubicRep.eval]",
            "",
        ]
        return
    out += [
        f"theorem {name}_pos : 0 < {name}Rep.eval := by",
        f"  have h : 0 < evalAtCheckerboardP {qlean(representative.a)} {qlean(representative.b)} {qlean(representative.c)} := by",
    ]
    kind = sign_kind(representative)
    if kind == "concave":
        out += [
            "    apply evalAtCheckerboardP_pos_of_concave",
            "    · norm_num",
            "    · norm_num [quadraticAt, pLower]",
            "    · norm_num [quadraticAt, pUpper]",
        ]
    elif kind == "right":
        out += [
            "    apply evalAtCheckerboardP_pos_of_right",
            "    · norm_num",
            "    · norm_num [pUpper]",
            "    · norm_num [quadraticAt, pUpper]",
        ]
    else:
        out += [
            "    apply evalAtCheckerboardP_pos_of_left",
            "    · norm_num",
            "    · norm_num [pLower]",
            "    · norm_num [quadraticAt, pLower]",
        ]
    out += [
        f"  simpa [{name}Rep, CubicRep.eval, evalAtCheckerboardP, quadraticAt] using h",
        "",
        f"theorem {name}_nonneg : 0 ≤ {name}Rep.eval := le_of_lt {name}_pos",
        "",
    ]


def generate():
    out = [
        "import Checkerboard.LP.DualCertifiedFunctions",
        "import Checkerboard.LP.CubicInterval",
        "",
        "/-!",
        "# Exact endpoint identities for the reduced dual profiles",
        "-/",
        "",
        "namespace Checkerboard",
        "",
        "noncomputable section",
        "",
    ]
    for name, term, raw, representative in VALUES:
        qpoly = quotient(raw, poly(representative))
        qlean_poly = lean_sympy(qpoly).replace("p", "checkerboardP")
        out += [
            f"def {name}Rep : CubicRep := {rep_literal(representative)}",
            "",
            f"theorem {name}_eq : {term} = {name}Rep.eval := by",
            "  have hp := checkerboardP_root",
            "  simp [pPoly] at hp",
            f"  simp [{UNFOLD}, {name}Rep, CubicRep.eval]",
            f"  linear_combination ({qlean_poly}) * hp",
            "",
        ]
        emit_positive(out, name, representative)

    out += [
        "theorem certifiedDualA1_at_p : certifiedDualA1 checkerboardP = 0 := by",
        "  rw [dualA1_p_eq]",
        "  norm_num [dualA1_pRep, CubicRep.eval]",
        "",
        "theorem certifiedDualA1_at_c_eq_AL :",
        "    certifiedDualA1 primalC = certifiedDualAL primalC := by",
        "  rw [dualA1_c_eq, dualAL_c_eq]",
        "  norm_num [dualA1_cRep, dualAL_cRep]",
        "",
        "theorem certifiedDualAL_at_d_eq_A2 :",
        "    certifiedDualAL primalD = certifiedDualA2 primalD := by",
        "  rw [dualAL_d_eq, dualA2_d_eq]",
        "  norm_num [dualAL_dRep, dualA2_dRep]",
        "",
        "theorem certifiedDualBQ_at_e_eq_BL :",
        "    certifiedDualBQ primalE = certifiedDualBL primalE := by",
        "  rw [dualBQ_e_eq, dualBL_e_eq]",
        "  norm_num [dualBQ_eRep, dualBL_eRep]",
        "",
        "theorem certifiedDualBL_at_f_eq_BQ :",
        "    certifiedDualBL primalF = certifiedDualBQ primalF := by",
        "  rw [dualBL_f_eq, dualBQ_f_eq]",
        "  norm_num [dualBL_fRep, dualBQ_fRep]",
        "",
        "theorem certifiedDualBQ_at_g : certifiedDualBQ primalG = 0 := by",
        "  rw [dualBQ_g_eq]",
        "  norm_num [dualBQ_gRep, CubicRep.eval]",
        "",
        "end",
        "",
        "end Checkerboard",
        "",
    ]
    return "\n".join(out)


def main():
    LEAN_PATH.parent.mkdir(parents=True, exist_ok=True)
    LEAN_PATH.write_text(generate(), encoding="utf-8")
    print(f"wrote {LEAN_PATH}")


if __name__ == "__main__":
    main()
