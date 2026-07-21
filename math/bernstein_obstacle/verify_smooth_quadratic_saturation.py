#!/usr/bin/env python3
"""Numerically verify smooth quadratic-contact Bernstein-cone saturation.

The script assembles the exact global H1 Gram matrix for continuous degree-p
Bernstein finite elements on an odd uniform mesh of (-1,1). It minimizes the H1
error to u(x)=x^2 subject to coefficient bounds 0 <= b <= 1 and exact endpoint
values. The normalized error is compared with the predicted sharp constant

gamma_p * sqrt(2/tanh(1)).

Dependencies: numpy, scipy.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize


@dataclass(frozen=True)
class Result:
    degree: int
    cells: int
    mesh_width: float
    error: float
    normalized_error: float
    predicted_constant: float
    optimizer_success: bool
    optimizer_iterations: int


def bernstein_basis_and_derivative(degree: int, t: float) -> tuple[np.ndarray, np.ndarray]:
    basis = np.array(
        [
            math.comb(degree, k) * t**k * (1.0 - t) ** (degree - k)
            for k in range(degree + 1)
        ],
        dtype=float,
    )
    if degree == 0:
        return basis, np.zeros(1, dtype=float)

    lower = np.array(
        [
            math.comb(degree - 1, k)
            * t**k
            * (1.0 - t) ** (degree - 1 - k)
            for k in range(degree)
        ],
        dtype=float,
    )
    derivative = np.zeros(degree + 1, dtype=float)
    for k in range(degree + 1):
        left = lower[k - 1] if k > 0 else 0.0
        right = lower[k] if k < degree else 0.0
        derivative[k] = degree * (left - right)
    return basis, derivative


def local_h1_gram(degree: int, mesh_width: float) -> np.ndarray:
    nodes, weights = leggauss(max(2 * degree + 3, 10))
    parameters = (nodes + 1.0) / 2.0
    weights = weights / 2.0

    gram = np.zeros((degree + 1, degree + 1), dtype=float)
    for t, weight in zip(parameters, weights, strict=True):
        basis, derivative = bernstein_basis_and_derivative(degree, float(t))
        gram += weight * mesh_width * np.outer(basis, basis)
        gram += weight / mesh_width * np.outer(derivative, derivative)
    return gram


def x_squared_coefficients(degree: int, left_endpoint: float, mesh_width: float) -> np.ndarray:
    if degree < 2:
        raise ValueError("degree must be at least two")
    return np.array(
        [
            left_endpoint**2
            + 2.0 * left_endpoint * mesh_width * k / degree
            + mesh_width**2 * k * (k - 1) / (degree * (degree - 1))
            for k in range(degree + 1)
        ],
        dtype=float,
    )


def gamma(degree: int) -> float:
    if degree < 2:
        raise ValueError("degree must be at least two")
    if degree % 2 == 0:
        return 1.0 / (4.0 * (degree - 1))
    return 1.0 / (4.0 * degree)


def predicted_constant(degree: int) -> float:
    return gamma(degree) * math.sqrt(2.0 / math.tanh(1.0))


def solve(degree: int, cells: int) -> Result:
    if degree < 2:
        raise ValueError("degree must be at least two")
    if cells <= 0 or cells % 2 == 0:
        raise ValueError("cells must be a positive odd integer")

    mesh_width = 2.0 / cells
    variable_count = cells * degree + 1
    gram = np.zeros((variable_count, variable_count), dtype=float)
    target_sum = np.zeros(variable_count, dtype=float)
    target_count = np.zeros(variable_count, dtype=float)
    local_gram = local_h1_gram(degree, mesh_width)

    for element in range(cells):
        indices = np.arange(element * degree, element * degree + degree + 1)
        gram[np.ix_(indices, indices)] += local_gram
        left_endpoint = -1.0 + element * mesh_width
        local_target = x_squared_coefficients(degree, left_endpoint, mesh_width)
        target_sum[indices] += local_target
        target_count[indices] += 1.0

    target = target_sum / target_count
    fixed_indices = np.array([0, variable_count - 1], dtype=int)
    fixed_values = np.array([1.0, 1.0], dtype=float)
    free_indices = np.array(
        [index for index in range(variable_count) if index not in {0, variable_count - 1}],
        dtype=int,
    )

    def assemble(free_values: np.ndarray) -> np.ndarray:
        coefficients = target.copy()
        coefficients[free_indices] = free_values
        coefficients[fixed_indices] = fixed_values
        return coefficients

    def objective(free_values: np.ndarray) -> float:
        error = assemble(free_values) - target
        return float(error @ gram @ error)

    def gradient(free_values: np.ndarray) -> np.ndarray:
        error = assemble(free_values) - target
        return 2.0 * (gram @ error)[free_indices]

    initial = np.clip(target[free_indices], 0.0, 1.0)
    optimization = minimize(
        objective,
        initial,
        jac=gradient,
        bounds=[(0.0, 1.0)] * len(free_indices),
        method="L-BFGS-B",
        options={"ftol": 1e-14, "gtol": 1e-11, "maxiter": 20_000, "maxls": 50},
    )

    error = math.sqrt(max(float(optimization.fun), 0.0))
    return Result(
        degree=degree,
        cells=cells,
        mesh_width=mesh_width,
        error=error,
        normalized_error=error / mesh_width**2,
        predicted_constant=predicted_constant(degree),
        optimizer_success=bool(optimization.success),
        optimizer_iterations=int(optimization.nit),
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--degrees", nargs="+", type=int, default=[2, 3, 4, 5, 6])
    parser.add_argument("--cells", nargs="+", type=int, default=[9, 17, 33, 65])
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    print("p,N,h,error,error_over_h2,predicted,success,iterations")
    for degree in args.degrees:
        for cells in args.cells:
            result = solve(degree, cells)
            print(
                f"{result.degree},{result.cells},{result.mesh_width:.12g},"
                f"{result.error:.12g},{result.normalized_error:.12g},"
                f"{result.predicted_constant:.12g},"
                f"{str(result.optimizer_success).lower()},"
                f"{result.optimizer_iterations}"
            )


if __name__ == "__main__":
    main()
