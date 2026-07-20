#!/usr/bin/env python3
"""Deterministic falsification test for the nonlinear certified Falk estimate.

This is numerical stress evidence, not a mathematical proof.

We generate nonsymmetric linear operators F(x)=Ax-b whose symmetric parts are
positive definite.  The continuous feasible set is the nonnegative orthant and
the certified inner set is a shifted orthant x >= q >= 0.  Both variational
inequalities are solved as linear complementarity problems with a
Fischer--Burmeister least-squares formulation.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from numpy.linalg import eigvalsh, norm
from scipy.optimize import least_squares


SEED = 20260720
CASES = 1000
TOLERANCE = 1.0e-7


def solve_lcp_fb(A: np.ndarray, b: np.ndarray, q: np.ndarray) -> np.ndarray:
    """Solve x>=q, F(x)>=0, (x-q)*F(x)=0 by Fischer--Burmeister."""

    def residual(x: np.ndarray) -> np.ndarray:
        y = x - q
        f = A @ x - b
        return np.sqrt(y * y + f * f) - y - f

    initial = q + np.maximum(0.0, b)
    result = least_squares(
        residual,
        initial,
        xtol=1.0e-12,
        ftol=1.0e-12,
        gtol=1.0e-12,
        max_nfev=3000,
    )
    if not result.success:
        raise RuntimeError(result.message)
    return result.x


def complementarity_residual(
    A: np.ndarray, b: np.ndarray, q: np.ndarray, x: np.ndarray
) -> float:
    y = x - q
    f = A @ x - b
    return float(
        max(
            np.max(np.maximum(-y, 0.0)),
            np.max(np.maximum(-f, 0.0)),
            np.max(np.abs(y * f)),
        )
    )


def main() -> None:
    rng = np.random.default_rng(SEED)
    violations = 0
    worst_margin = float("inf")
    max_ratio = 0.0
    sum_ratio = 0.0
    max_complementarity = 0.0
    samples: list[dict[str, float | int]] = []

    for case in range(CASES):
        dimension = int(rng.integers(2, 9))

        raw = rng.normal(size=(dimension, dimension))
        symmetric = raw.T @ raw + (0.5 + rng.random()) * np.eye(dimension)
        raw_skew = rng.normal(size=(dimension, dimension))
        skew = 0.5 * (raw_skew - raw_skew.T)
        A = symmetric + skew
        b = rng.normal(size=dimension)
        q = np.maximum(0.0, rng.normal(scale=0.25, size=dimension))

        u = solve_lcp_fb(A, b, np.zeros(dimension))
        u_h = solve_lcp_fb(A, b, q)
        v_h = np.maximum(u, q)

        alpha = float(eigvalsh((A + A.T) / 2.0).min())
        lipschitz = float(norm(A, 2))
        error = u_h - u
        recovery_error = v_h - u
        multiplier_term = float((A @ u - b) @ recovery_error)

        lhs = alpha * norm(error) ** 2
        rhs = (
            lipschitz * norm(error) * norm(recovery_error)
            + multiplier_term
        )
        margin = float(rhs - lhs)

        squared_bound = (
            lipschitz**2 / alpha**2 * norm(recovery_error) ** 2
            + 2.0 / alpha * multiplier_term
        )
        ratio = (
            float(norm(error) ** 2 / squared_bound)
            if squared_bound > 1.0e-18
            else 0.0
        )

        comp = max(
            complementarity_residual(A, b, np.zeros(dimension), u),
            complementarity_residual(A, b, q, u_h),
        )

        if margin < -TOLERANCE:
            violations += 1
        worst_margin = min(worst_margin, margin)
        max_ratio = max(max_ratio, ratio)
        sum_ratio += ratio
        max_complementarity = max(max_complementarity, comp)

        if case < 5:
            samples.append(
                {
                    "dimension": dimension,
                    "alpha": alpha,
                    "lipschitz": lipschitz,
                    "margin": margin,
                    "squared_error_to_bound_ratio": ratio,
                    "multiplier_term": multiplier_term,
                    "complementarity_residual": comp,
                }
            )

    summary = {
        "seed": SEED,
        "cases": CASES,
        "violations_below_minus_1e-7": violations,
        "worst_margin": worst_margin,
        "max_squared_error_to_bound_ratio": max_ratio,
        "mean_squared_error_to_bound_ratio": sum_ratio / CASES,
        "max_complementarity_residual": max_complementarity,
        "sample_cases": samples,
    }

    output = (
        Path(__file__).resolve().parents[1]
        / "results"
        / "nonlinear_falk_stress_summary.json"
    )
    output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))

    if violations:
        raise SystemExit(f"found {violations} violations")


if __name__ == "__main__":
    main()
