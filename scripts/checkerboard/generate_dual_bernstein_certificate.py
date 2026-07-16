#!/usr/bin/env python3
"""Reconstruct and generate the exact 40-triangle odd-fat dual certificate.

The arrangement and fan triangulation are rebuilt from the displayed breakpoint
lines. Lean rechecks every algebraic coefficient and every sign; the Python
geometry is only a source generator, not part of the trusted proof base.
"""
from __future__ import annotations

import csv
from fractions import Fraction as F
from pathlib import Path

from generate_outer_density_certificate import K, qlean, rep_literal, sign_kind

ROOT = Path(__file__).resolve().parents[2]
TRI_PATH = ROOT / "math/checkerboard/lp/certificates/dual_triangles_reconstructed.tsv"
COEFF_PATH = ROOT / "math/checkerboard/lp/certificates/dual_bernstein_reconstructed.tsv"
LEAN_PATH = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/DualBernsteinData.lean"

P = K(0, 1, 0)
c = K(F(5, 76), F(64, 19), F(-401, 76))
d = K(F(71, 76), F(-45, 19), F(401, 76))
e = K(F(-33, 152), F(185, 76), F(-401, 152))
f = K(F(33, 152), F(-33, 76), F(401, 152))
g = K(F(43, 76), F(71, 38), F(-401, 76))

C = -c*c + F(1, 2)*c*e + F(1, 2)*c*f + d*d - F(1, 2)*d*e - F(1, 2)*d*f - 2*d - g*g + 2*P*P + 1
D = -c - d - 2*g + 4*P
E = -2*c*c + c*e + c*f - F(1, 2)*e*f - F(1, 2)*e - F(1, 2)*f - F(1, 2)*g*g + 2*P*P
H = -2*c - g + 4*P - 1
det = C*H - E*D
Kd = (H-D) / det
rd = (C-E) / det
s = -F(1, 2)*Kd*g*g - rd*g
ell = -(F(1, 2)*Kd*(e+f) + rd)
qq = -F(1, 2)*Kd*e*f - F(1, 2)*Kd*g*g - rd*g
n1 = Kd*P*P + 2*rd*P
nu = (-2*Kd*c*c + Kd*c*e + Kd*c*f + 2*Kd*P*P - 2*c*rd + 4*P*rd) * F(1, 2)
n2 = (-2*Kd*c*c + Kd*c*e + Kd*c*f + 2*Kd*d*d - Kd*d*e - Kd*d*f - 4*Kd*d + 2*Kd*P*P - 2*c*rd - 2*d*rd + 4*P*rd) * F(1, 2)


def side(line, point):
    a, b, constant = line
    return a*point[0] + b*point[1] - constant


def intersect(p, q, line):
    sp, sq = side(line, p), side(line, q)
    t = sp / (sp-sq)
    return (p[0] + t*(q[0]-p[0]), p[1] + t*(q[1]-p[1]))


def clean(poly):
    out = []
    for point in poly:
        if not out or abs((point[0]-out[-1][0]).decimal()) + abs((point[1]-out[-1][1]).decimal()) > 1e-10:
            out.append(point)
    if len(out) > 1 and abs((out[0][0]-out[-1][0]).decimal()) + abs((out[0][1]-out[-1][1]).decimal()) < 1e-10:
        out.pop()
    return out


def clip(poly, line, keep_positive):
    out = []
    for i, point in enumerate(poly):
        nxt = poly[(i+1) % len(poly)]
        sp, sn = side(line, point).decimal(), side(line, nxt).decimal()
        inside_p = sp >= -1e-12 if keep_positive else sp <= 1e-12
        inside_n = sn >= -1e-12 if keep_positive else sn <= 1e-12
        if inside_p:
            out.append(point)
        if inside_p != inside_n:
            out.append(intersect(point, nxt, line))
    return clean(out)


def area(poly):
    return sum(
        (poly[i][0]*poly[(i+1) % len(poly)][1] - poly[(i+1) % len(poly)][0]*poly[i][1]).decimal()
        for i in range(len(poly))
    ) / 2


def centroid(poly):
    return (
        sum(x.decimal() for x, _ in poly) / len(poly),
        sum(y.decimal() for _, y in poly) / len(poly),
    )


def reconstruct_cells():
    polygons = [[(K(0), K(0)), (K(1), K(0)), (K(1), K(1))]]
    lines = []
    for z in (e, f, g):
        lines.append((K(1), K(0), z))
    for z in (e, f, g):
        lines.append((K(0), K(1), z))
    for z in (2*P, 2*c, 2*d):
        lines.append((K(1), K(1), z))
    for z in (2*(1-d), 2*(1-c)):
        lines.append((K(1), K(-1), z))
    for line in lines:
        new = []
        for poly in polygons:
            for keep in (True, False):
                piece = clip(poly, line, keep)
                if len(piece) >= 3 and abs(area(piece)) > 1e-10:
                    new.append(piece)
        polygons = new
    if len(polygons) != 24:
        raise RuntimeError(f"expected 24 cells, got {len(polygons)}")
    for poly in polygons:
        if area(poly) < 0:
            poly.reverse()
    polygons.sort(key=centroid)
    if sum(len(poly)-2 for poly in polygons) != 40:
        raise RuntimeError("fan triangulation is not 40 triangles")
    return polygons


def A_piece(tnum):
    if tnum <= P.decimal() + 1e-9:
        return lambda t: K(0)
    if tnum <= c.decimal() + 1e-9:
        return lambda t: -Kd*t*t - 2*rd*t + n1
    if tnum <= d.decimal() + 1e-9:
        return lambda t: ell*t + nu
    return lambda t: -Kd*t*t + 2*Kd*t + n2


def B_piece(tnum):
    if tnum <= e.decimal() + 1e-9:
        return lambda t: F(1, 2)*Kd*t*t + rd*t + s
    if tnum <= f.decimal() + 1e-9:
        return lambda t: -ell*t + qq
    if tnum <= g.decimal() + 1e-9:
        return lambda t: F(1, 2)*Kd*t*t + rd*t + s
    return lambda t: K(0)


def cell_polynomial(poly):
    cu, cv = centroid(poly)
    ax, ay = A_piece((cu+cv)/2), A_piece((2-cu+cv)/2)
    bu, bv = B_piece(cu), B_piece(cv)

    def obstacle(point):
        u, v = point
        return ax((u+v)*F(1, 2)) + ay((2-u+v)*F(1, 2)) + bu(u) + bv(v) - 1

    return obstacle


def reconstruct():
    triangles, coefficients = [], []
    for cell, poly in enumerate(reconstruct_cells()):
        obstacle = cell_polynomial(poly)
        for j in range(1, len(poly)-1):
            vertices = [poly[0], poly[j], poly[j+1]]
            values = [obstacle(vertex) for vertex in vertices]
            bernstein = [values[0], values[1], values[2]]
            for a, b in ((0, 1), (0, 2), (1, 2)):
                midpoint = (
                    (vertices[a][0]+vertices[b][0])*F(1, 2),
                    (vertices[a][1]+vertices[b][1])*F(1, 2),
                )
                bernstein.append(2*obstacle(midpoint) - F(1, 2)*(values[a]+values[b]))
            triangles.append((cell, vertices))
            coefficients.append(bernstein)
    if len(triangles) != 40 or sum(map(len, coefficients)) != 240:
        raise RuntimeError("wrong certificate size")
    if any(value.decimal() < -1e-10 for row in coefficients for value in row):
        raise RuntimeError("negative reconstructed coefficient")
    return triangles, coefficients


def write_tsv(triangles, coefficients):
    TRI_PATH.parent.mkdir(parents=True, exist_ok=True)
    with TRI_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle, delimiter="\t")
        writer.writerow(
            ["triangle", "cell"]
            + [f"{axis}{vertex}{coef}" for vertex in range(3) for axis in ("u", "v") for coef in ("a", "b", "c")]
        )
        for triangle, (cell, vertices) in enumerate(triangles):
            row = [triangle, cell]
            for u, v in vertices:
                row += [u.a, u.b, u.c, v.a, v.b, v.c]
            writer.writerow(row)
    names = ["200", "020", "002", "110", "101", "011"]
    with COEFF_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle, delimiter="\t")
        writer.writerow(["triangle", "coefficient", "a", "b", "c"])
        for triangle, row in enumerate(coefficients):
            for name, value in zip(names, row):
                writer.writerow([triangle, name, value.a, value.b, value.c])


def generate_lean(triangles, coefficients):
    unique, index = [], {}
    for row in coefficients:
        for value in row:
            key = (value.a, value.b, value.c)
            if key not in index:
                index[key] = len(unique)
                unique.append(value)

    out = [
        "import Checkerboard.LP.CubicField",
        "import Checkerboard.LP.CubicInterval",
        "import Checkerboard.LP.Bernstein",
        "",
        "/-!",
        "# Reconstructed exact 40-triangle dual Bernstein certificate",
        "",
        "Generated independently from the displayed breakpoint arrangement and dual formulas.",
        "All coefficient signs are rechecked by the Lean kernel on the isolating interval.",
        "-/",
        "",
        "namespace Checkerboard",
        "",
        "noncomputable section",
        "",
        "structure DualTriangleData where",
        "  u0 : CubicRep",
        "  v0 : CubicRep",
        "  u1 : CubicRep",
        "  v1 : CubicRep",
        "  u2 : CubicRep",
        "  v2 : CubicRep",
        "  b200 : CubicRep",
        "  b020 : CubicRep",
        "  b002 : CubicRep",
        "  b110 : CubicRep",
        "  b101 : CubicRep",
        "  b011 : CubicRep",
        "",
    ]

    for i, value in enumerate(unique):
        out += [f"def dualBernsteinCoeff{i} : CubicRep := {rep_literal(value)}", ""]
        if value == K(0):
            out += [
                f"theorem dualBernsteinCoeff{i}_nonneg : 0 ≤ dualBernsteinCoeff{i}.eval := by",
                f"  norm_num [dualBernsteinCoeff{i}, CubicRep.eval]",
                "",
            ]
        else:
            out += [
                f"theorem dualBernsteinCoeff{i}_pos : 0 < dualBernsteinCoeff{i}.eval := by",
                f"  have h : 0 < evalAtCheckerboardP {qlean(value.a)} {qlean(value.b)} {qlean(value.c)} := by",
            ]
            kind = sign_kind(value)
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
                f"  simpa [dualBernsteinCoeff{i}, CubicRep.eval, evalAtCheckerboardP, quadraticAt] using h",
                "",
                f"theorem dualBernsteinCoeff{i}_nonneg : 0 ≤ dualBernsteinCoeff{i}.eval :=",
                f"  le_of_lt dualBernsteinCoeff{i}_pos",
                "",
            ]

    out += ["def dualTriangleData (i : Fin 40) : DualTriangleData :=", "  match i.1 with"]
    for triangle, ((cell, vertices), bernstein) in enumerate(zip(triangles, coefficients)):
        parts = []
        for u, v in vertices:
            parts += [rep_literal(u), rep_literal(v)]
        parts += [f"dualBernsteinCoeff{index[(value.a, value.b, value.c)]}" for value in bernstein]
        clause = f"⟨{', '.join(parts)}⟩"
        out.append(f"  | {triangle} => {clause}" if triangle < 39 else f"  | _ => {clause}")

    out += [
        "",
        "theorem dualTriangle_coefficients_nonneg (i : Fin 40) :",
        "    0 ≤ (dualTriangleData i).b200.eval ∧ 0 ≤ (dualTriangleData i).b020.eval ∧",
        "    0 ≤ (dualTriangleData i).b002.eval ∧ 0 ≤ (dualTriangleData i).b110.eval ∧",
        "    0 ≤ (dualTriangleData i).b101.eval ∧ 0 ≤ (dualTriangleData i).b011.eval := by",
        "  fin_cases i",
    ]
    for row in coefficients:
        names = [f"dualBernsteinCoeff{index[(value.a, value.b, value.c)]}_nonneg" for value in row]
        out.append(
            f"  · simpa [dualTriangleData] using And.intro {names[0]} "
            f"(And.intro {names[1]} (And.intro {names[2]} (And.intro {names[3]} "
            f"(And.intro {names[4]} {names[5]}))))"
        )

    out += [
        "",
        "theorem dualTriangle_bernstein_nonneg (i : Fin 40) {l0 l1 l2 : ℝ}",
        "    (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) :",
        "    0 ≤ quadraticBernstein (dualTriangleData i).b200.eval",
        "      (dualTriangleData i).b020.eval (dualTriangleData i).b002.eval",
        "      (dualTriangleData i).b110.eval (dualTriangleData i).b101.eval",
        "      (dualTriangleData i).b011.eval l0 l1 l2 := by",
        "  rcases dualTriangle_coefficients_nonneg i with ⟨h200,h020,h002,h110,h101,h011⟩",
        "  exact quadraticBernstein_nonneg h200 h020 h002 h110 h101 h011 hl0 hl1 hl2",
        "",
        "end",
        "",
        "end Checkerboard",
        "",
    ]
    return "\n".join(out)


def main():
    triangles, coefficients = reconstruct()
    write_tsv(triangles, coefficients)
    LEAN_PATH.parent.mkdir(parents=True, exist_ok=True)
    LEAN_PATH.write_text(generate_lean(triangles, coefficients), encoding="utf-8")
    print(f"wrote {TRI_PATH}")
    print(f"wrote {COEFF_PATH}")
    print(f"wrote {LEAN_PATH}")
    print(
        f"{len(triangles)} triangles; {sum(map(len, coefficients))} coefficients; "
        f"{sum(value == K(0) for row in coefficients for value in row)} zeros"
    )


if __name__ == "__main__":
    main()
