#!/usr/bin/env python3
"""Exact rational verification of Bernstein coefficient/value moment identities.

For the standard triangle and degree-r barycentric lattice interpolation, this
computes the inverse Bernstein collocation matrix exactly over Q. For every
coefficient functional L_i(v)=b_i(I_r v)-v(x_i), it verifies that L_i
annihilates affine functions and computes the Taylor-remainder constant

    C_i = 1/2 * sum_j |(E^{-1})_{ij}| |x_j-x_i|^2.

Thus |L_i(v)| <= C_i ||D^2 v||_op on the reference triangle.
"""
from __future__ import annotations

import csv
from math import factorial
from pathlib import Path
import sympy as sp


def multi_indices(r: int):
    return [(a, b, r - a - b) for a in range(r + 1) for b in range(r + 1 - a)]


def bernstein_value(alpha, lam, r: int):
    a, b, c = alpha
    return (
        sp.Rational(factorial(r), factorial(a) * factorial(b) * factorial(c))
        * lam[0] ** a
        * lam[1] ** b
        * lam[2] ** c
    )


def verify_degree(r: int):
    indices = multi_indices(r)
    nodes = [
        (sp.Rational(a, r), sp.Rational(b, r), sp.Rational(c, r))
        for a, b, c in indices
    ]
    coordinates = [sp.Matrix([lam[1], lam[2]]) for lam in nodes]

    evaluation = sp.Matrix(
        [[bernstein_value(alpha, lam, r) for alpha in indices] for lam in nodes]
    )
    inverse = evaluation.inv()

    rows = []
    max_constant = sp.Rational(0)
    for i, row in enumerate(inverse.tolist()):
        xi = coordinates[i]
        zeroth_moment = sp.simplify(sum(row) - 1)
        first_x = sp.simplify(sum(c * x[0] for c, x in zip(row, coordinates)) - xi[0])
        first_y = sp.simplify(sum(c * x[1] for c, x in zip(row, coordinates)) - xi[1])
        if zeroth_moment != 0 or first_x != 0 or first_y != 0:
            raise AssertionError(
                f"Affine moment failure at degree {r}, index {indices[i]}: "
                f"{zeroth_moment}, {first_x}, {first_y}"
            )

        constant = sp.simplify(
            sum(
                sp.Abs(c) * ((x - xi).dot(x - xi)) / 2
                for c, x in zip(row, coordinates)
            )
        )
        max_constant = max(max_constant, constant)
        rows.append(
            {
                "degree": r,
                "alpha": str(indices[i]),
                "constant_exact": str(constant),
                "constant_float": float(constant),
            }
        )

    return rows, max_constant


def main():
    output = Path(__file__).with_name("bernstein_coefficient_constants.csv")
    all_rows = []
    summary = []
    for r in range(1, 7):
        rows, maximum = verify_degree(r)
        all_rows.extend(rows)
        summary.append((r, str(maximum), float(maximum)))

    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=all_rows[0].keys())
        writer.writeheader()
        writer.writerows(all_rows)

    print("degree,max_constant_exact,max_constant_float")
    for row in summary:
        print(f"{row[0]},{row[1]},{row[2]:.16g}")
    print(f"wrote {output}")


if __name__ == "__main__":
    main()
