#!/usr/bin/env python3
"""One-command reproduction for the Bernstein obstacle validation campaign.

Runs:
  1. deterministic theorem stress tests;
  2. custom curved quadratic Bernstein--Bézier Hertz/Signorini solver;
  3. independent scikit-fem curved P2 solver;
  4. numerical acceptance checks against invariant tolerances.

The script intentionally checks mathematical invariants and cross-framework
agreement rather than exact CSV byte equality, which is too brittle across
BLAS/LAPACK builds.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

import pandas as pd


def run(command: list[str]) -> None:
    print("+", " ".join(command), flush=True)
    subprocess.run(command, check=True)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("reproduction-output"),
    )
    parser.add_argument(
        "--skip-skfem",
        action="store_true",
        help="Run the custom solver and proof stress tests only.",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parent
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)

    stress_summary = output / "bernstein_proof_stress_summary.json"
    strip_csv = output / "bernstein_strip_scaling_results.csv"
    localization_csv = output / "bernstein_cut_localization_results.csv"
    run([
        sys.executable,
        str(root / "bernstein_proof_stress_tests.py"),
        "--summary", str(stress_summary),
        "--strip", str(strip_csv),
        "--localization", str(localization_csv),
    ])

    curved_csv = output / "hertz_signorini_p2_curved_results.csv"
    curved_json = output / "hertz_signorini_p2_curved_crosscheck.json"
    run([
        sys.executable,
        str(root / "hertz_signorini_p2_curved_bernstein.py"),
        "--output", str(curved_csv),
        "--crosscheck", str(curved_json),
        "--pressure-plot", str(output / "hertz_signorini_p2_curved_pressure.png"),
        "--convergence-plot", str(output / "hertz_signorini_p2_curved_convergence.png"),
        "--geometry-plot", str(output / "hertz_signorini_p2_curved_geometry.png"),
    ])

    stress = json.loads(stress_summary.read_text(encoding="utf-8"))
    require(all(item["passed"] for item in stress), "A proof stress test failed.")
    rates = {item["test"]: item for item in stress}
    require(
        abs(rates["codimension_one_strip_h1_scaling"]["fitted_rate"] - 1.5) < 5e-3,
        "The fitted strip exponent is not 3/2.",
    )
    require(
        rates["cut_element_negative_coefficient_O_h2"]["maximum_negative_over_h2"] < 0.5,
        "Cut-element coefficient localization exceeded the audited constant.",
    )

    curved = pd.read_csv(curved_csv)
    finest = curved.iloc[-1]
    require(finest["minimum_gap_coefficient"] >= -1e-12, "Curved solver penetrated.")
    require(finest["kkt_residual"] <= 2e-10, "Curved solver KKT residual is too large.")
    require(finest["reaction_absolute_error"] <= 1e-8, "Curved solver lost force balance.")
    require(
        finest["maximum_boundary_radius_error"] <= 5e-9,
        "Curved geometry failed its radius check.",
    )
    require(
        finest["bracketed_half_width_error"] <= 2e-4,
        "Curved Hertz contact-width error exceeded the audited tolerance.",
    )

    comparison: dict[str, float | int | bool] = {
        "stress_tests_passed": True,
        "curved_solver_passed": True,
        "finest_curved_half_width_error": float(finest["bracketed_half_width_error"]),
        "finest_curved_reaction_error": float(finest["reaction_absolute_error"]),
        "finest_curved_minimum_gap": float(finest["minimum_gap_coefficient"]),
    }

    if not args.skip_skfem:
        skfem_csv = output / "hertz_signorini_skfem_results.csv"
        skfem_json = output / "hertz_signorini_skfem_comparison.json"
        run([
            sys.executable,
            str(root / "hertz_signorini_skfem_independent.py"),
            "--output", str(skfem_csv),
            "--comparison", str(skfem_json),
            "--reference", str(curved_csv),
        ])
        independent = pd.read_csv(skfem_csv)
        require(len(independent) == len(curved), "Framework result lengths differ.")
        half_width_diff = (
            independent["estimated_contact_half_width"]
            - curved["bracketed_contact_half_width"]
        ).abs()
        reaction_diff = (
            independent["total_half_reaction"]
            - curved["total_half_reaction"]
        ).abs()
        require(half_width_diff.max() <= 1e-5, "Cross-framework contact widths disagree.")
        require(reaction_diff.max() <= 5e-9, "Cross-framework reactions disagree.")
        require(
            independent["minimum_gap_coefficient"].min() >= -1e-11,
            "scikit-fem penetrated.",
        )
        comparison.update({
            "skfem_passed": True,
            "maximum_cross_framework_half_width_difference": float(half_width_diff.max()),
            "maximum_cross_framework_reaction_difference": float(reaction_diff.max()),
        })

    (output / "REPRODUCTION_PASS.json").write_text(
        json.dumps(comparison, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(comparison, indent=2, sort_keys=True))
    print("REPRODUCTION PASSED")


if __name__ == "__main__":
    main()
