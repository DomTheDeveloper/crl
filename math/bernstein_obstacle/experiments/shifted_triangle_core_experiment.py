#!/usr/bin/env python3
"""Empirical check of the eroded-triangle-core translation lemma.

The plane is tiled by unit squares split along the southwest-to-northeast diagonal.
For a uniformly random translation, every fixed curve point is uniformly distributed
in the fundamental square.  A point is declared good when its distance from all three
edges of the containing triangle is at least ``r``.

For the right isosceles reference triangle, the exact good area fraction is

    p_r = ((R-r)/R)^2,  R = 1 - 1/sqrt(2).

The experiment samples long straight interface segments at several angles and checks
that the average good-length fraction agrees with this orientation-independent value.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Result:
    angle_degrees: float
    mean: float
    q10: float
    median: float
    probability_above_threshold: float


def exact_core_fraction(r: float) -> float:
    inradius = 1.0 - 1.0 / math.sqrt(2.0)
    if not 0.0 <= r < inradius:
        raise ValueError(f"r must lie in [0, {inradius})")
    return ((inradius - r) / inradius) ** 2


def sampled_core_fractions(
    points: np.ndarray, translations: np.ndarray, r: float
) -> np.ndarray:
    output = np.empty(translations.shape[0], dtype=float)
    sqrt_two = math.sqrt(2.0)

    for index, translation in enumerate(translations):
        fractional = (points - translation) % 1.0
        x = fractional[:, 0]
        y = fractional[:, 1]
        lower = y <= x
        distance = np.empty_like(x)

        distance[lower] = np.minimum.reduce(
            [
                y[lower],
                1.0 - x[lower],
                (x[lower] - y[lower]) / sqrt_two,
            ]
        )

        upper = ~lower
        distance[upper] = np.minimum.reduce(
            [
                x[upper],
                1.0 - y[upper],
                (y[upper] - x[upper]) / sqrt_two,
            ]
        )

        output[index] = np.mean(distance >= r)

    return output


def run(
    *,
    r: float,
    samples: int,
    translations: int,
    segment_length: float,
    threshold: float,
    seed: int,
) -> list[Result]:
    generator = np.random.default_rng(seed)
    shifts = generator.random((translations, 2))
    parameter = np.linspace(0.0, segment_length, samples)
    results: list[Result] = []

    for angle_degrees in (0, 15, 30, 45, 60, 75, 90, 120, 150):
        angle = math.radians(angle_degrees)
        points = np.column_stack(
            [parameter * math.cos(angle), parameter * math.sin(angle)]
        )
        values = sampled_core_fractions(points, shifts, r)
        results.append(
            Result(
                angle_degrees=float(angle_degrees),
                mean=float(np.mean(values)),
                q10=float(np.quantile(values, 0.10)),
                median=float(np.median(values)),
                probability_above_threshold=float(np.mean(values >= threshold)),
            )
        )

    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--r", type=float, default=0.08)
    parser.add_argument("--samples", type=int, default=10_000)
    parser.add_argument("--translations", type=int, default=2_000)
    parser.add_argument("--segment-length", type=float, default=100.0)
    parser.add_argument("--threshold", type=float, default=0.15)
    parser.add_argument("--seed", type=int, default=20_260_721)
    arguments = parser.parse_args()

    exact = exact_core_fraction(arguments.r)
    print(f"exact expected core fraction: {exact:.6f}")
    print("angle  mean      q10       median    probability>=threshold")

    for result in run(
        r=arguments.r,
        samples=arguments.samples,
        translations=arguments.translations,
        segment_length=arguments.segment_length,
        threshold=arguments.threshold,
        seed=arguments.seed,
    ):
        print(
            f"{result.angle_degrees:5.0f}  "
            f"{result.mean:8.6f}  "
            f"{result.q10:8.6f}  "
            f"{result.median:8.6f}  "
            f"{result.probability_above_threshold:8.6f}"
        )


if __name__ == "__main__":
    main()
