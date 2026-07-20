#!/usr/bin/env python3
"""Adversarial numerical stress tests for the Bernstein obstacle proof chain.

These tests do not replace mathematical proof. They are designed to falsify
implementation-level and statement-level mistakes in the finite certificate,
shared-face clipping, projection inequalities, free-boundary scaling, and
cut-element coefficient localization mechanisms.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
import pandas as pd


def multiindices(total: int, length: int):
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in multiindices(total - first, length - 1):
            yield (first,) + tail


def multinomial(alpha):
    n = sum(alpha)
    value = math.factorial(n)
    for a in alpha:
        value //= math.factorial(a)
    return value


def simplex_basis(alpha, lam):
    value = float(multinomial(alpha))
    for a, x in zip(alpha, lam):
        value *= x**a
    return value


def simplex_field(coefficients, lam):
    return sum(c * simplex_basis(alpha, lam) for alpha, c in coefficients.items())


def test_random_simplex_positivity(rng):
    worst = math.inf
    cases = 0
    for dimension in range(1, 5):
        for degree in range(1, 7):
            indices = list(multiindices(degree, dimension + 1))
            for _ in range(20):
                coeff = {alpha: float(rng.exponential()) for alpha in indices}
                for _ in range(200):
                    lam = rng.dirichlet(np.ones(dimension + 1))
                    value = simplex_field(coeff, lam)
                    worst = min(worst, value)
                    cases += 1
                    if value < -1e-12:
                        raise AssertionError((dimension, degree, value))
    return {"test": "random_simplex_positivity", "cases": cases,
            "worst_margin": worst, "passed": True}


def test_shared_face_clipping(rng):
    worst_before = 0.0
    worst_after = 0.0
    cases = 0
    for degree in range(1, 9):
        edge_coeff = rng.normal(size=degree + 1)
        coeff_a, coeff_b = {}, {}
        for alpha in multiindices(degree, 3):
            if alpha[2] == 0:
                coeff_a[alpha] = edge_coeff[alpha[1]]
                beta = (alpha[1], alpha[0], 0)
                coeff_b[beta] = edge_coeff[alpha[1]]
            else:
                coeff_a[alpha] = float(rng.normal())
                coeff_b[alpha] = float(rng.normal())
        clipped_a = {a: max(v, 0.0) for a, v in coeff_a.items()}
        clipped_b = {a: max(v, 0.0) for a, v in coeff_b.items()}
        for t in np.linspace(0.0, 1.0, 1001):
            va = simplex_field(coeff_a, (1.0 - t, t, 0.0))
            vb = simplex_field(coeff_b, (t, 1.0 - t, 0.0))
            ca = simplex_field(clipped_a, (1.0 - t, t, 0.0))
            cb = simplex_field(clipped_b, (t, 1.0 - t, 0.0))
            worst_before = max(worst_before, abs(va - vb))
            worst_after = max(worst_after, abs(ca - cb))
            cases += 1
    if worst_before > 2e-12 or worst_after > 2e-12:
        raise AssertionError((worst_before, worst_after))
    return {"test": "shared_face_clipping_conformity", "cases": cases,
            "worst_before": worst_before, "worst_after": worst_after,
            "passed": True}


def sqdist(a, b):
    return float(np.sum((a - b) ** 2))


def test_projection_identities(rng):
    worst_kkt = 0.0
    worst_pythagorean_slack = math.inf
    worst_nonexpansive_slack = math.inf
    cases = 0
    for dimension in [1, 2, 5, 20, 100]:
        for _ in range(1000):
            c = rng.normal(size=dimension)
            d = rng.exponential(size=dimension)
            e = rng.normal(size=dimension)
            pc = np.maximum(c, 0.0)
            pe = np.maximum(e, 0.0)
            residual = pc - c
            kkt = float(residual @ (d - pc))
            pythagorean_slack = sqdist(c, d) - sqdist(c, pc) - sqdist(pc, d)
            nonexpansive_slack = sqdist(c, e) - sqdist(pc, pe)
            worst_kkt = min(worst_kkt, kkt)
            worst_pythagorean_slack = min(worst_pythagorean_slack, pythagorean_slack)
            worst_nonexpansive_slack = min(worst_nonexpansive_slack, nonexpansive_slack)
            cases += 1
            if min(kkt, pythagorean_slack, nonexpansive_slack) < -2e-11:
                raise AssertionError((kkt, pythagorean_slack, nonexpansive_slack))
    return {"test": "coefficient_projection_kkt", "cases": cases,
            "minimum_kkt": worst_kkt,
            "minimum_pythagorean_slack": worst_pythagorean_slack,
            "minimum_nonexpansive_slack": worst_nonexpansive_slack,
            "passed": True}


def test_strip_scaling():
    hs = 2.0 ** (-np.arange(3, 15, dtype=float))
    l2_sq = (2.0 / 3.0) * hs**5
    grad_sq = 2.0 * hs**3
    h1 = np.sqrt(l2_sq + grad_sq)
    slopes = np.diff(np.log(h1)) / np.diff(np.log(hs))
    fitted = float(np.polyfit(np.log(hs), np.log(h1), 1)[0])
    if abs(fitted - 1.5) > 0.01:
        raise AssertionError(fitted)
    return ({"test": "codimension_one_strip_h1_scaling", "cases": len(hs),
             "fitted_rate": fitted, "last_step_rate": float(slopes[-1]),
             "passed": True},
            pd.DataFrame({"h": hs, "l2_sq": l2_sq,
                          "grad_sq": grad_sq, "h1_norm": h1}))


def bernstein_collocation(degree):
    nodes = np.arange(degree + 1, dtype=float) / degree
    matrix = np.empty((degree + 1, degree + 1))
    for j, x in enumerate(nodes):
        for k in range(degree + 1):
            matrix[j, k] = math.comb(degree, k) * x**k * (1.0 - x) ** (degree - k)
    return nodes, matrix


def test_cut_element_localization():
    records = []
    worst_normalized_negative = 0.0
    for degree in range(2, 9):
        nodes, matrix = bernstein_collocation(degree)
        inverse = np.linalg.inv(matrix)
        for phase in np.linspace(0.025, 0.975, 39):
            reference_values = np.maximum(nodes - phase, 0.0) ** 2
            normalized_coefficients = inverse @ reference_values
            worst_normalized_negative = max(
                worst_normalized_negative,
                float(np.max(np.maximum(-normalized_coefficients, 0.0))))
            for h in [1 / 8, 1 / 16, 1 / 32, 1 / 64]:
                coefficients = h**2 * normalized_coefficients
                ratio = float(np.max(np.maximum(-coefficients, 0.0)) / h**2)
                records.append({"degree": degree, "phase": phase, "h": h,
                                "max_negative": float(np.max(np.maximum(-coefficients, 0.0))),
                                "negative_over_h2": ratio})
                if ratio > worst_normalized_negative + 1e-10:
                    raise AssertionError((degree, phase, h, ratio))
    frame = pd.DataFrame(records)
    return ({"test": "cut_element_negative_coefficient_O_h2",
             "cases": len(frame),
             "maximum_negative_over_h2": worst_normalized_negative,
             "passed": True}, frame)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--strip", type=Path, required=True)
    parser.add_argument("--localization", type=Path, required=True)
    args = parser.parse_args()
    rng = np.random.default_rng(20260720)
    results = [test_random_simplex_positivity(rng),
               test_shared_face_clipping(rng),
               test_projection_identities(rng)]
    strip_result, strip_frame = test_strip_scaling()
    localization_result, localization_frame = test_cut_element_localization()
    results.extend([strip_result, localization_result])
    args.summary.write_text(json.dumps(results, indent=2), encoding="utf-8")
    strip_frame.to_csv(args.strip, index=False)
    localization_frame.to_csv(args.localization, index=False)
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
