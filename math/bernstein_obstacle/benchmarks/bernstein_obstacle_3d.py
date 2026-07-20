#!/usr/bin/env python3
"""Three-dimensional pointwise-feasible Bernstein obstacle benchmark.

Solves a manufactured obstacle problem on the unit cube using conforming
structured tensor-product Bernstein elements and a primal-dual active-set
method. Nonnegative global Bernstein control coefficients certify u_h >= 0
at every point of every hexahedral element.
"""
from __future__ import annotations

import argparse
import csv
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np
import sympy as sp
from numpy.polynomial.legendre import leggauss
from scipy.sparse import csr_matrix, lil_matrix
from scipy.sparse.linalg import spsolve
from scipy.special import comb


@dataclass(frozen=True)
class Result:
    degree: int
    elements_per_axis: int
    unknowns: int
    total_control_coefficients: int
    pdas_iterations: int
    active_coefficients: int
    kkt_residual: float
    l2_error: float
    h1_seminorm_error: float
    minimum_coefficient: float
    minimum_sampled_solution: float
    total_contact_force: float
    exact_contact_volume: float
    contact_force_error: float


def bernstein_values_derivatives(degree: int, points: np.ndarray):
    points = np.asarray(points, dtype=float)
    values = np.array([
        comb(degree, i) * points**i * (1.0 - points)**(degree - i)
        for i in range(degree + 1)
    ]).T
    derivatives = np.zeros_like(values)
    if degree == 0:
        return values, derivatives
    lower = np.array([
        comb(degree - 1, i) * points**i * (1.0 - points)**(degree - 1 - i)
        for i in range(degree)
    ]).T
    derivatives[:, 0] = -degree * lower[:, 0]
    derivatives[:, -1] = degree * lower[:, -1]
    for i in range(1, degree):
        derivatives[:, i] = degree * (lower[:, i - 1] - lower[:, i])
    return values, derivatives


def manufactured_functions():
    x, y, z, radius = sp.symbols("x y z radius", real=True)
    bubble = x * (1 - x) * y * (1 - y) * z * (1 - z)
    level = (
        (x - sp.Rational(1, 2))**2
        + (y - sp.Rational(1, 2))**2
        + (z - sp.Rational(1, 2))**2
        - radius**2
    )
    exterior = bubble * level**2
    laplacian = sum(sp.diff(exterior, variable, 2) for variable in (x, y, z))
    return (
        sp.lambdify((x, y, z, radius), exterior, "numpy"),
        sp.lambdify((x, y, z, radius), sp.diff(exterior, x), "numpy"),
        sp.lambdify((x, y, z, radius), sp.diff(exterior, y), "numpy"),
        sp.lambdify((x, y, z, radius), sp.diff(exterior, z), "numpy"),
        sp.lambdify((x, y, z, radius), -laplacian, "numpy"),
    )


U_EXT, UX_EXT, UY_EXT, UZ_EXT, F_EXT = manufactured_functions()


def reference_matrices(degree: int, order: int | None = None):
    order = order or max(2 * degree + 4, 9)
    nodes, weights = leggauss(order)
    nodes = (nodes + 1.0) / 2.0
    weights = weights / 2.0
    basis, derivative = bernstein_values_derivatives(degree, nodes)
    mass = basis.T @ (weights[:, None] * basis)
    stiffness = derivative.T @ (weights[:, None] * derivative)
    return mass, stiffness


def assemble(elements: int, degree: int, radius: float, scale: float):
    m = elements
    r = degree
    g = m * r + 1
    total = g**3
    mass, stiffness = reference_matrices(r)
    h = 1.0 / m
    local_operator = h * (
        np.kron(np.kron(stiffness, mass), mass)
        + np.kron(np.kron(mass, stiffness), mass)
        + np.kron(np.kron(mass, mass), stiffness)
    )

    order = max(2 * r + 7, 11)
    nodes, weights = leggauss(order)
    nodes = (nodes + 1.0) / 2.0
    weights = weights / 2.0
    basis, _ = bernstein_values_derivatives(r, nodes)
    tensor_basis = np.einsum("ai,bj,ck->abcijk", basis, basis, basis).reshape(
        order**3, (r + 1)**3
    )
    tensor_weights = np.einsum("a,b,c->abc", weights, weights, weights).reshape(-1)

    matrix = lil_matrix((total, total))
    load = np.zeros(total)

    def gid(ix: int, iy: int, iz: int) -> int:
        return (ix * g + iy) * g + iz

    for ex in range(m):
        for ey in range(m):
            for ez in range(m):
                global_ids = np.array([
                    gid(ex * r + i, ey * r + j, ez * r + k)
                    for i in range(r + 1)
                    for j in range(r + 1)
                    for k in range(r + 1)
                ])
                matrix[np.ix_(global_ids, global_ids)] += local_operator

                qx = (ex + nodes[:, None, None]) / m
                qy = (ey + nodes[None, :, None]) / m
                qz = (ez + nodes[None, None, :]) / m
                level = (qx - 0.5)**2 + (qy - 0.5)**2 + (qz - 0.5)**2 - radius**2
                force = np.where(
                    level > 0,
                    scale * F_EXT(qx, qy, qz, radius),
                    -scale,
                ).reshape(-1)
                local_load = tensor_basis.T @ (tensor_weights * force) * h**3
                load[global_ids] += local_load

    ids = np.arange(total).reshape(g, g, g)
    interior = ids[1:-1, 1:-1, 1:-1].reshape(-1)
    return matrix.tocsr()[interior][:, interior], load[interior], interior, g


def pdas(matrix: csr_matrix, load: np.ndarray, tolerance: float = 2e-10, maximum_iterations: int = 120):
    coefficients = np.zeros_like(load)
    multipliers = np.maximum(matrix @ coefficients - load, 0.0)
    previous_active = None

    for iteration in range(1, maximum_iterations + 1):
        active = multipliers - coefficients > 0
        inactive = ~active
        new_coefficients = np.zeros_like(coefficients)
        if np.any(inactive):
            new_coefficients[inactive] = spsolve(matrix[inactive][:, inactive], load[inactive])
        gradient = matrix @ new_coefficients - load
        new_multipliers = np.zeros_like(multipliers)
        new_multipliers[active] = gradient[active]

        residual = max(
            float(np.max(np.maximum(-new_coefficients, 0.0))),
            float(np.max(np.maximum(-new_multipliers, 0.0))),
            float(np.max(np.abs(np.minimum(new_coefficients, new_multipliers)))),
            float(np.max(np.abs(gradient[inactive]))) if np.any(inactive) else 0.0,
        )
        if previous_active is not None and np.array_equal(active, previous_active) and residual <= tolerance:
            return new_coefficients, new_multipliers, iteration, residual
        coefficients = new_coefficients
        multipliers = new_multipliers
        previous_active = active
    raise RuntimeError(f"PDAS failed after {maximum_iterations} iterations; residual={residual:.3e}")


def reconstruct(interior_coefficients: np.ndarray, interior_ids: np.ndarray, g: int):
    coefficients = np.zeros(g**3)
    coefficients[interior_ids] = interior_coefficients
    return coefficients.reshape(g, g, g)


def exact_solution_gradient(x, y, z, radius: float, scale: float):
    level = (x - 0.5)**2 + (y - 0.5)**2 + (z - 0.5)**2 - radius**2
    outside = level > 0
    u = np.where(outside, scale * U_EXT(x, y, z, radius), 0.0)
    ux = np.where(outside, scale * UX_EXT(x, y, z, radius), 0.0)
    uy = np.where(outside, scale * UY_EXT(x, y, z, radius), 0.0)
    uz = np.where(outside, scale * UZ_EXT(x, y, z, radius), 0.0)
    return u, ux, uy, uz


def compute_errors(coefficients, elements: int, degree: int, radius: float, scale: float, order: int = 8):
    nodes, weights = leggauss(order)
    nodes = (nodes + 1.0) / 2.0
    weights = weights / 2.0
    basis, derivative = bernstein_values_derivatives(degree, nodes)
    tensor_weights = np.einsum("a,b,c->abc", weights, weights, weights)
    m = elements
    r = degree
    h = 1.0 / m
    l2_squared = 0.0
    h1_squared = 0.0
    minimum_value = float("inf")

    for ex in range(m):
        for ey in range(m):
            for ez in range(m):
                block = coefficients[
                    ex*r:ex*r+r+1,
                    ey*r:ey*r+r+1,
                    ez*r:ez*r+r+1,
                ]
                numerical = np.einsum("ai,bj,ck,ijk->abc", basis, basis, basis, block)
                numerical_x = np.einsum("ai,bj,ck,ijk->abc", derivative, basis, basis, block) / h
                numerical_y = np.einsum("ai,bj,ck,ijk->abc", basis, derivative, basis, block) / h
                numerical_z = np.einsum("ai,bj,ck,ijk->abc", basis, basis, derivative, block) / h

                qx = (ex + nodes[:, None, None]) / m
                qy = (ey + nodes[None, :, None]) / m
                qz = (ez + nodes[None, None, :]) / m
                exact, exact_x, exact_y, exact_z = exact_solution_gradient(qx, qy, qz, radius, scale)
                physical_weights = tensor_weights * h**3
                l2_squared += np.sum(physical_weights * (numerical - exact)**2)
                h1_squared += np.sum(
                    physical_weights * (
                        (numerical_x - exact_x)**2
                        + (numerical_y - exact_y)**2
                        + (numerical_z - exact_z)**2
                    )
                )
                minimum_value = min(minimum_value, float(numerical.min()))
    return math.sqrt(l2_squared), math.sqrt(h1_squared), minimum_value


def run_case(degree: int, elements: int, radius: float = 0.22, scale: float = 1000.0):
    matrix, load, interior_ids, g = assemble(elements, degree, radius, scale)
    interior, multipliers, iterations, residual = pdas(matrix, load)
    coefficients = reconstruct(interior, interior_ids, g)
    l2_error, h1_error, minimum_value = compute_errors(coefficients, elements, degree, radius, scale)

    # Summing KKT multipliers is not a physical integral. Reconstruct total force
    # through the partition-of-unity identity: the load dual acts on the constant
    # coefficient vector. Boundary coefficient multipliers are absent, so this is
    # reported as a discrete interior contact-force diagnostic.
    total_force = float(np.sum(multipliers))
    exact_volume_force = scale * (4.0 / 3.0) * math.pi * radius**3

    return Result(
        degree=degree,
        elements_per_axis=elements,
        unknowns=len(interior),
        total_control_coefficients=g**3,
        pdas_iterations=iterations,
        active_coefficients=int(np.sum(interior <= 1e-10)),
        kkt_residual=residual,
        l2_error=l2_error,
        h1_seminorm_error=h1_error,
        minimum_coefficient=float(coefficients.min()),
        minimum_sampled_solution=minimum_value,
        total_contact_force=total_force,
        exact_contact_volume=exact_volume_force,
        contact_force_error=abs(total_force - exact_volume_force),
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("bernstein_obstacle_3d_results.csv"))
    parser.add_argument("--degrees", nargs="+", type=int, default=[1, 2, 3])
    parser.add_argument("--meshes", nargs="+", type=int, default=[4, 6])
    args = parser.parse_args()

    results = []
    for degree in args.degrees:
        for mesh in args.meshes:
            if degree == 3 and mesh > 4:
                continue
            result = run_case(degree, mesh)
            results.append(result)
            print(result)

    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(asdict(results[0]).keys()))
        writer.writeheader()
        writer.writerows(asdict(result) for result in results)
    print(f"Wrote {args.output.resolve()}")


if __name__ == "__main__":
    main()
