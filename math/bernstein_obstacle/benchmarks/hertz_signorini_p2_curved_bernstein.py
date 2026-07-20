#!/usr/bin/env python3
"""Curved isoparametric quadratic Bernstein--Bezier Hertz/Signorini benchmark.

This program upgrades ``hertz_signorini_p2_bernstein.py`` from polygonal
contact geometry to a genuinely curved quadratic isoparametric boundary.

Key certificate
---------------
On a curved contact edge the physical vertical coordinate and the vertical
displacement are represented in the same quadratic Bernstein basis. Hence

    gap(t) = sum_i (Y_i + U_i) B_i^2(t).

Requiring all three edge coefficients ``Y_i + U_i`` to be nonnegative proves
``gap(t) >= 0`` for every point on the curved edge, not only at nodes.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from scipy.optimize import minimize_scalar
from scipy.sparse import lil_matrix

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import hertz_signorini_p2_bernstein as base


def curved_geometry_controls(mesh: dict, radius: float) -> np.ndarray:
    points = mesh["points"]
    edge_dictionary = mesh["edge_dictionary"]
    vertex_count = len(points)
    controls = np.zeros((vertex_count + len(edge_dictionary), 2))
    controls[:vertex_count] = points
    center = np.array([0.0, radius])
    contact_edges = set(mesh["contact_edges"])
    for edge, edge_index in edge_dictionary.items():
        a, b = edge
        chord_midpoint = 0.5 * (points[a] + points[b])
        if edge in contact_edges:
            angle_a = math.atan2(points[a, 1] - radius, points[a, 0])
            angle_b = math.atan2(points[b, 1] - radius, points[b, 0])
            angle_midpoint = 0.5 * (angle_a + angle_b)
            arc_midpoint = center + radius * np.array(
                [math.cos(angle_midpoint), math.sin(angle_midpoint)]
            )
            control = 2.0 * arc_midpoint - chord_midpoint
        else:
            control = chord_midpoint
        controls[vertex_count + edge_index] = control
    return controls


def assemble_curved(mesh, radius, young, poisson, top_pressure, quadrature_order=5):
    points = mesh["points"]
    triangles = mesh["triangles"]
    edge_dictionary = mesh["edge_dictionary"]
    vertex_count = len(points)
    scalar_dofs = vertex_count + len(edge_dictionary)
    local_map = base.local_scalar_map(mesh)
    geometry_controls = curved_geometry_controls(mesh, radius)
    matrix = lil_matrix((2 * scalar_dofs, 2 * scalar_dofs))
    load = np.zeros(2 * scalar_dofs)
    constitutive = (
        young / ((1.0 + poisson) * (1.0 - 2.0 * poisson))
        * np.array([
            [1.0 - poisson, poisson, 0.0],
            [poisson, 1.0 - poisson, 0.0],
            [0.0, 0.0, (1.0 - 2.0 * poisson) / 2.0],
        ])
    )
    reference_points, quadrature_weights = base.triangle_quadrature(quadrature_order)
    _, reference_gradients = base.p2_basis_gradients(reference_points)
    minimum_jacobian_determinant = math.inf
    maximum_jacobian_determinant = 0.0
    for triangle_index in range(len(triangles)):
        scalar_indices = local_map[triangle_index]
        geometry = geometry_controls[scalar_indices]
        local_matrix = np.zeros((12, 12))
        for quadrature_index in range(len(reference_points)):
            jacobian = geometry.T @ reference_gradients[quadrature_index]
            determinant = float(np.linalg.det(jacobian))
            if determinant <= 0.0:
                raise RuntimeError(f"Nonpositive isoparametric Jacobian {determinant}")
            minimum_jacobian_determinant = min(minimum_jacobian_determinant, determinant)
            maximum_jacobian_determinant = max(maximum_jacobian_determinant, determinant)
            physical_gradients = reference_gradients[quadrature_index] @ np.linalg.inv(jacobian)
            strain = np.zeros((3, 12))
            for local_index, (derivative_x, derivative_y) in enumerate(physical_gradients):
                strain[0, 2 * local_index] = derivative_x
                strain[1, 2 * local_index + 1] = derivative_y
                strain[2, 2 * local_index] = derivative_y
                strain[2, 2 * local_index + 1] = derivative_x
            local_matrix += (
                quadrature_weights[quadrature_index]
                * determinant * strain.T @ constitutive @ strain
            )
        dofs = np.ravel(np.column_stack((2 * scalar_indices, 2 * scalar_indices + 1)))
        matrix[np.ix_(dofs, dofs)] += local_matrix
    for edge in mesh["top_edges"]:
        edge_control = vertex_count + edge_dictionary[edge]
        scalar_indices = [edge[0], edge_control, edge[1]]
        projected_length = abs(geometry_controls[edge[1], 0] - geometry_controls[edge[0], 0])
        nodal_force = -top_pressure * projected_length / 3.0
        for scalar_index in scalar_indices:
            load[2 * scalar_index + 1] += nodal_force
    fixed_x_scalar_dofs = set(mesh["symmetry_vertices"])
    fixed_x_scalar_dofs.update(vertex_count + edge_dictionary[e] for e in mesh["symmetry_edges"])
    contact_geometry = {
        int(vertex): float(geometry_controls[vertex, 1])
        for vertex in mesh["contact_vertices"]
    }
    for edge in mesh["contact_edges"]:
        edge_control = vertex_count + edge_dictionary[edge]
        contact_geometry[edge_control] = float(geometry_controls[edge_control, 1])
    return {
        "matrix": matrix.tocsr(), "load": load, "scalar_dofs": scalar_dofs,
        "local_map": local_map, "fixed_x_scalar_dofs": fixed_x_scalar_dofs,
        "contact_geometry": contact_geometry, "geometry_controls": geometry_controls,
        "minimum_jacobian_determinant": minimum_jacobian_determinant,
        "maximum_jacobian_determinant": maximum_jacobian_determinant,
    }


def contact_diagnostics(mesh, system, solution, radius, young, poisson, top_pressure):
    geometry = system["geometry_controls"]
    edge_dictionary = mesh["edge_dictionary"]
    vertex_count = len(mesh["points"])
    contact_geometry = system["contact_geometry"]
    displacement = solution["displacement"]
    gradient = solution["gradient"]
    projected_weights = {int(index): 0.0 for index in contact_geometry}
    gauss_nodes, gauss_weights = np.polynomial.legendre.leggauss(16)
    t = (gauss_nodes + 1.0) / 2.0
    weights = gauss_weights / 2.0
    edge_basis = np.column_stack(((1.0 - t) ** 2, 2.0 * t * (1.0 - t), t**2))
    edge_basis_derivative = np.column_stack((-2.0 * (1.0 - t), 2.0 - 4.0 * t, 2.0 * t))
    center = np.array([0.0, radius])
    maximum_radius_error = 0.0
    for edge in mesh["contact_edges"]:
        edge_control = vertex_count + edge_dictionary[edge]
        a, b = edge
        if geometry[a, 0] > geometry[b, 0]:
            a, b = b, a
        scalar_indices = [a, edge_control, b]
        edge_geometry = geometry[scalar_indices]
        derivative_x = edge_basis_derivative @ edge_geometry[:, 0]
        for local_index, scalar_index in enumerate(scalar_indices):
            projected_weights[int(scalar_index)] += float(np.sum(
                weights * edge_basis[:, local_index] * np.abs(derivative_x)
            ))
        sampled_points = edge_basis @ edge_geometry
        maximum_radius_error = max(maximum_radius_error, float(np.max(
            np.abs(np.linalg.norm(sampled_points - center, axis=1) - radius)
        )))
    scalar_indices = np.asarray(sorted(contact_geometry), dtype=int)
    x = geometry[scalar_indices, 0]
    gap_coefficients = displacement[2 * scalar_indices + 1] + np.asarray(
        [contact_geometry[int(index)] for index in scalar_indices]
    )
    reactions = gradient[2 * scalar_indices + 1]
    pressure_weights = np.asarray([projected_weights[int(index)] for index in scalar_indices])
    order = np.argsort(x)
    x, gap_coefficients, reactions, pressure_weights = (
        x[order], gap_coefficients[order], reactions[order], pressure_weights[order]
    )
    numerical_pressure = reactions / pressure_weights
    exact_half_width, exact_pressure = base.hertz_reference(
        radius, young, poisson, top_pressure, x
    )
    active = gap_coefficients <= 1e-10
    last_active = int(np.flatnonzero(active)[-1])
    bracketed_half_width = (
        0.5 * (x[last_active] + x[last_active + 1])
        if last_active + 1 < len(x) else x[last_active]
    )
    comparison_region = x <= 1.6 * exact_half_width
    pressure_error = numerical_pressure - exact_pressure
    def hertz_model(candidate_half_width):
        return 4.0 * radius * top_pressure / (math.pi * candidate_half_width**2) * np.sqrt(
            np.maximum(candidate_half_width**2 - x**2, 0.0)
        )
    def objective(candidate_half_width):
        error = numerical_pressure - hertz_model(candidate_half_width)
        return float(np.sum(pressure_weights[comparison_region] * error[comparison_region] ** 2))
    fit = minimize_scalar(
        objective, bounds=(0.5 * exact_half_width, 1.5 * exact_half_width),
        method="bounded", options={"xatol": 1e-12}
    )
    return {
        "x": x, "gap_coefficients": gap_coefficients, "reactions": reactions,
        "pressure_weights": pressure_weights, "numerical_pressure": numerical_pressure,
        "exact_pressure": exact_pressure, "exact_half_width": exact_half_width,
        "bracketed_half_width": bracketed_half_width, "fitted_half_width": float(fit.x),
        "pressure_l2_error": math.sqrt(float(np.sum(
            pressure_weights[comparison_region] * pressure_error[comparison_region] ** 2
        ))),
        "pressure_linf_error": float(np.max(np.abs(pressure_error[comparison_region]))),
        "total_half_reaction": float(np.sum(reactions)),
        "minimum_gap_coefficient": float(np.min(gap_coefficients)),
        "minimum_reaction": float(np.min(reactions)),
        "active_gap_coefficients": int(np.sum(active)),
        "maximum_boundary_radius_error": maximum_radius_error,
    }


def run_case(radius, young, poisson, top_pressure, radial_intervals, angular_intervals,
             perform_crosscheck=False):
    mesh = base.make_mesh(radius, radial_intervals, angular_intervals)
    system = assemble_curved(mesh, radius, young, poisson, top_pressure)
    solution = base.solve_pdas(system)
    diagnostics = contact_diagnostics(
        mesh, system, solution, radius, young, poisson, top_pressure
    )
    row = {
        "radial_intervals": radial_intervals, "angular_intervals": angular_intervals,
        "vertices": len(mesh["points"]), "triangles": len(mesh["triangles"]),
        "scalar_control_dofs": system["scalar_dofs"],
        "displacement_unknowns": 2 * system["scalar_dofs"] - len(system["fixed_x_scalar_dofs"]),
        "pdas_iterations": solution["iterations"], "kkt_residual": solution["kkt_residual"],
        "exact_contact_half_width": diagnostics["exact_half_width"],
        "bracketed_contact_half_width": diagnostics["bracketed_half_width"],
        "bracketed_half_width_error": abs(diagnostics["bracketed_half_width"] - diagnostics["exact_half_width"]),
        "fitted_contact_half_width": diagnostics["fitted_half_width"],
        "fitted_half_width_error": abs(diagnostics["fitted_half_width"] - diagnostics["exact_half_width"]),
        "pressure_l2_error": diagnostics["pressure_l2_error"],
        "pressure_linf_error": diagnostics["pressure_linf_error"],
        "total_half_reaction": diagnostics["total_half_reaction"],
        "expected_half_reaction": top_pressure * radius,
        "reaction_absolute_error": abs(diagnostics["total_half_reaction"] - top_pressure * radius),
        "minimum_gap_coefficient": diagnostics["minimum_gap_coefficient"],
        "minimum_reaction": diagnostics["minimum_reaction"],
        "active_gap_coefficients": diagnostics["active_gap_coefficients"],
        "maximum_boundary_radius_error": diagnostics["maximum_boundary_radius_error"],
        "minimum_jacobian_determinant": system["minimum_jacobian_determinant"],
    }
    crosscheck = base.independent_check(mesh, system, solution) if perform_crosscheck else None
    return row, diagnostics, crosscheck


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--crosscheck", type=Path, required=True)
    parser.add_argument("--pressure-plot", type=Path, required=True)
    parser.add_argument("--convergence-plot", type=Path, required=True)
    parser.add_argument("--geometry-plot", type=Path, required=True)
    args = parser.parse_args()
    radius, young, poisson, top_pressure = 1.0, 200.0, 0.3, 0.5
    meshes = [(4, 40), (6, 60), (8, 80), (12, 120), (16, 160)]
    rows, diagnostics_by_mesh, crosscheck = [], [], None
    for index, (radial, angular) in enumerate(meshes):
        row, diagnostics, check = run_case(
            radius, young, poisson, top_pressure, radial, angular, index == 0
        )
        rows.append(row); diagnostics_by_mesh.append(diagnostics)
        if check is not None: crosscheck = check
    frame = pd.DataFrame(rows)
    frame.to_csv(args.output, index=False)
    args.crosscheck.write_text(json.dumps(crosscheck, indent=2), encoding="utf-8")
    figure, axis = plt.subplots()
    finest = diagnostics_by_mesh[-1]
    axis.plot(finest["x"], finest["exact_pressure"], label="Hertz analytical pressure")
    for index in [0, 2, 4]:
        diagnostics = diagnostics_by_mesh[index]
        radial, angular = meshes[index]
        axis.plot(diagnostics["x"], diagnostics["numerical_pressure"],
                  label=f"Curved P2 {radial}x{angular}")
    axis.set_xlim(0.0, 1.35 * finest["exact_half_width"])
    axis.set_xlabel("Contact coordinate x"); axis.set_ylabel("Normal pressure")
    axis.set_title("Curved isoparametric Bernstein Hertz contact")
    axis.grid(True); axis.legend()
    figure.savefig(args.pressure_plot, dpi=180, bbox_inches="tight"); plt.close(figure)
    figure, axis = plt.subplots()
    axis.loglog(frame["displacement_unknowns"], frame["fitted_half_width_error"],
                marker="o", label="Pressure-fitted half-width error")
    axis.loglog(frame["displacement_unknowns"], frame["pressure_l2_error"],
                marker="s", label="Pressure L2 error")
    axis.set_xlabel("Displacement unknowns"); axis.set_ylabel("Error")
    axis.set_title("Curved Bernstein Hertz benchmark convergence")
    axis.grid(True); axis.legend()
    figure.savefig(args.convergence_plot, dpi=180, bbox_inches="tight"); plt.close(figure)
    figure, axis = plt.subplots()
    axis.loglog(frame["angular_intervals"], frame["maximum_boundary_radius_error"], marker="o")
    axis.set_xlabel("Angular boundary intervals")
    axis.set_ylabel("Maximum circular-boundary radius error")
    axis.set_title("Quadratic isoparametric contact-geometry accuracy")
    axis.grid(True)
    figure.savefig(args.geometry_plot, dpi=180, bbox_inches="tight"); plt.close(figure)


if __name__ == "__main__":
    main()
