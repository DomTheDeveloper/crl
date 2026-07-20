#!/usr/bin/env python3
"""Independent solver/certificate check for the 3D Bernstein obstacle benchmark.

Uses the benchmark only for deterministic matrix/load assembly. It then solves
one small bound-constrained QP twice:
  (1) the project's primal-dual active-set method;
  (2) SciPy L-BFGS-B from the zero vector with nonnegative bounds.

The resulting control vectors, objectives, stationarity/complementarity
residuals, and dense/random pointwise values are compared. Point evaluation is
implemented independently with explicit binomial Bernstein factors.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from scipy.special import comb


def load_module(path: Path):
    spec = importlib.util.spec_from_file_location("bernstein3d", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def objective(A, f, c):
    return 0.5 * float(c @ (A @ c)) - float(f @ c)


def gradient(A, f, c):
    return np.asarray(A @ c - f)


def kkt_residual(A, f, c):
    g = gradient(A, f, c)
    return max(
        float(np.max(np.maximum(-c, 0.0))),
        float(np.max(np.maximum(-g, 0.0))),
        float(np.max(np.abs(np.minimum(c, g)))),
    )


def bval(r: int, i: int, t: float) -> float:
    return float(comb(r, i, exact=True)) * t**i * (1.0 - t) ** (r - i)


def eval_piecewise(coeff, elements: int, degree: int, points: np.ndarray) -> np.ndarray:
    out = np.empty(len(points))
    m, r = elements, degree
    for p_index, (x, y, z) in enumerate(points):
        ex = min(int(x * m), m - 1)
        ey = min(int(y * m), m - 1)
        ez = min(int(z * m), m - 1)
        tx, ty, tz = x * m - ex, y * m - ey, z * m - ez
        value = 0.0
        for i in range(r + 1):
            bx = bval(r, i, tx)
            for j in range(r + 1):
                bxy = bx * bval(r, j, ty)
                for k in range(r + 1):
                    value += coeff[ex*r+i, ey*r+j, ez*r+k] * bxy * bval(r, k, tz)
        out[p_index] = value
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark", type=Path, default=Path(__file__).with_name("bernstein_obstacle_3d.py"))
    parser.add_argument("--output", type=Path, default=Path("bernstein_obstacle_3d_independent_check.json"))
    parser.add_argument("--degree", type=int, default=2)
    parser.add_argument("--elements", type=int, default=3)
    parser.add_argument("--seed", type=int, default=20260720)
    args = parser.parse_args()

    bench = load_module(args.benchmark)
    A, f, interior_ids, g = bench.assemble(args.elements, args.degree, 0.22, 1000.0)
    c_pdas, _lam_pdas, iterations, residual_pdas = bench.pdas(A, f)

    fun = lambda c: objective(A, f, c)
    jac = lambda c: gradient(A, f, c)
    opt = minimize(
        fun,
        np.zeros_like(c_pdas),
        jac=jac,
        method="L-BFGS-B",
        bounds=[(0.0, None)] * len(f),
        options={"ftol": 1e-14, "gtol": 1e-11, "maxiter": 20000, "maxls": 50},
    )
    c_lbfgs = np.asarray(opt.x)

    coeff_pdas = bench.reconstruct(c_pdas, interior_ids, g)
    coeff_lbfgs = bench.reconstruct(c_lbfgs, interior_ids, g)

    rng = np.random.default_rng(args.seed)
    random_points = rng.random((25000, 3))
    grid_axis = np.linspace(0.0, 1.0, 31)
    gx, gy, gz = np.meshgrid(grid_axis, grid_axis, grid_axis, indexing="ij")
    sample_points = np.vstack((random_points, np.column_stack((gx.ravel(), gy.ravel(), gz.ravel()))))

    values_pdas = eval_piecewise(coeff_pdas, args.elements, args.degree, sample_points)
    values_lbfgs = eval_piecewise(coeff_lbfgs, args.elements, args.degree, sample_points)

    report = {
        "degree": args.degree,
        "elements_per_axis": args.elements,
        "unknowns": int(len(f)),
        "pdas_iterations": int(iterations),
        "pdas_reported_residual": float(residual_pdas),
        "pdas_independent_kkt_residual": kkt_residual(A, f, c_pdas),
        "lbfgsb_success": bool(opt.success),
        "lbfgsb_message": str(opt.message),
        "lbfgsb_iterations": int(opt.nit),
        "lbfgsb_kkt_residual": kkt_residual(A, f, c_lbfgs),
        "pdas_objective": fun(c_pdas),
        "lbfgsb_objective": fun(c_lbfgs),
        "absolute_objective_difference": abs(fun(c_pdas) - fun(c_lbfgs)),
        "coefficient_linf_difference": float(np.max(np.abs(c_pdas - c_lbfgs))),
        "coefficient_l2_difference": float(np.linalg.norm(c_pdas - c_lbfgs)),
        "pdas_minimum_coefficient": float(coeff_pdas.min()),
        "lbfgsb_minimum_coefficient": float(coeff_lbfgs.min()),
        "pdas_minimum_over_54791_points": float(values_pdas.min()),
        "lbfgsb_minimum_over_54791_points": float(values_lbfgs.min()),
        "maximum_sampled_solution_difference": float(np.max(np.abs(values_pdas - values_lbfgs))),
        "basis_partition_unity_max_error": float(max(
            abs(sum(bval(args.degree, i, t) for i in range(args.degree + 1)) - 1.0)
            for t in np.linspace(0.0, 1.0, 1001)
        )),
    }
    report["accepted"] = bool(
        report["pdas_independent_kkt_residual"] < 1e-9
        and report["lbfgsb_kkt_residual"] < 2e-7
        and report["absolute_objective_difference"] < 1e-9
        and report["coefficient_linf_difference"] < 5e-6
        and report["pdas_minimum_over_54791_points"] >= -1e-12
        and report["lbfgsb_minimum_over_54791_points"] >= -1e-12
        and report["basis_partition_unity_max_error"] < 1e-12
    )
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    if not report["accepted"]:
        raise SystemExit("independent check failed")


if __name__ == "__main__":
    main()
