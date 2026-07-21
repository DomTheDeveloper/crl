#!/usr/bin/env python3
"""Quadratic Bernstein finite elements for a nonlinear nonsymmetric obstacle VI.

Operator
    A(u) = -u'' + beta*u' + c*u + gamma*tanh(u)
Obstacle
    u >= 0
Manufactured exact solution
    u(x) = (x-a)_+^2 (1-x)
Multiplier
    lambda(x) = 1 on x<a and 0 on x>a
Forcing
    f = A(u) - lambda

The discrete cone is the nonnegative orthant of assembled quadratic Bernstein
coefficients.  The nonlinear VI is solved as a Fischer--Burmeister
complementarity system.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import root


@dataclass
class Result:
    n_elements: int
    h: float
    success: bool
    iterations: int
    residual_norm: float
    h1_error: float
    l2_error: float
    min_coefficient: float
    min_dual_residual: float
    complementarity_inf: float
    observed_h1_rate: float | None = None


class BernsteinVI1D:
    def __init__(
        self,
        n: int,
        a: float,
        beta: float,
        c: float,
        gamma: float,
        qorder: int = 10,
    ) -> None:
        if n < 2:
            raise ValueError("n must be at least 2")
        self.n = n
        self.h = 1.0 / n
        self.a = a
        self.beta = beta
        self.c = c
        self.gamma = gamma
        qx, qw = leggauss(qorder)
        self.tq = (qx + 1.0) / 2.0
        self.wq = qw / 2.0
        self.B = np.vstack(
            ((1.0 - self.tq) ** 2, 2.0 * self.tq * (1.0 - self.tq), self.tq**2)
        ).T
        self.dBdt = np.vstack(
            (-2.0 * (1.0 - self.tq), 2.0 * (1.0 - 2.0 * self.tq), 2.0 * self.tq)
        ).T

        # Full degrees of freedom: n+1 shared endpoint coefficients followed by
        # one interior Bernstein coefficient per element.  Boundary endpoints
        # are fixed at zero.
        self.ndof_full = 2 * n + 1
        self.free = np.array(
            list(range(1, n)) + list(range(n + 1, 2 * n + 1)), dtype=int
        )
        self.full_to_free = -np.ones(self.ndof_full, dtype=int)
        self.full_to_free[self.free] = np.arange(len(self.free))

    def local_dofs(self, element: int) -> np.ndarray:
        return np.array(
            [element, self.n + 1 + element, element + 1], dtype=int
        )

    def exact(self, x: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        s = np.maximum(x - self.a, 0.0)
        positive = x > self.a
        u = s * s * (1.0 - x)
        du = np.where(positive, 2.0 * s * (1.0 - x) - s * s, 0.0)
        d2u = np.where(positive, 2.0 * (1.0 - x) - 4.0 * s, 0.0)
        return u, du, d2u

    def forcing(self, x: np.ndarray) -> np.ndarray:
        u, du, d2u = self.exact(x)
        operator_value = (
            -d2u
            + self.beta * du
            + self.c * u
            + self.gamma * np.tanh(u)
        )
        multiplier = np.where(x < self.a, 1.0, 0.0)
        return operator_value - multiplier

    def lift(self, z: np.ndarray) -> np.ndarray:
        full = np.zeros(self.ndof_full)
        full[self.free] = z
        return full

    def residual_jacobian(self, z: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        full = self.lift(z)
        m = len(z)
        residual = np.zeros(m)
        jacobian = np.zeros((m, m))

        for element in range(self.n):
            x0 = element * self.h
            xq = x0 + self.h * self.tq
            local = self.local_dofs(element)
            coefficient = full[local]
            B = self.B
            dB = self.dBdt / self.h
            uq = B @ coefficient
            duq = dB @ coefficient
            fq = self.forcing(xq)
            sech2 = 1.0 / np.cosh(uq) ** 2

            local_residual = self.h * np.sum(
                self.wq[:, None]
                * (
                    duq[:, None] * dB
                    + self.beta * duq[:, None] * B
                    + self.c * uq[:, None] * B
                    + self.gamma * np.tanh(uq)[:, None] * B
                    - fq[:, None] * B
                ),
                axis=0,
            )

            local_jacobian = self.h * np.einsum(
                "q,qi,qj->ij", self.wq, dB, dB
            )
            local_jacobian += self.h * self.beta * np.einsum(
                "q,qi,qj->ij", self.wq, B, dB
            )
            local_jacobian += self.h * self.c * np.einsum(
                "q,qi,qj->ij", self.wq, B, B
            )
            local_jacobian += self.h * self.gamma * np.einsum(
                "q,q,qi,qj->ij", self.wq, sech2, B, B
            )

            for i, global_i in enumerate(local):
                row = self.full_to_free[global_i]
                if row < 0:
                    continue
                residual[row] += local_residual[i]
                for j, global_j in enumerate(local):
                    column = self.full_to_free[global_j]
                    if column >= 0:
                        jacobian[row, column] += local_jacobian[i, j]

        return residual, jacobian

    def fischer_burmeister(self, z: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        residual, residual_jacobian = self.residual_jacobian(z)
        scale = np.sqrt(z * z + residual * residual + 1.0e-28)
        phi = scale - z - residual
        direct_derivative = z / scale - 1.0
        residual_derivative = residual / scale - 1.0
        phi_jacobian = np.diag(direct_derivative) + residual_derivative[:, None] * residual_jacobian
        return phi, phi_jacobian

    def initial_guess(self) -> np.ndarray:
        full = np.zeros(self.ndof_full)
        vertices = np.linspace(0.0, 1.0, self.n + 1)
        full[: self.n + 1] = self.exact(vertices)[0]
        for element in range(self.n):
            x0 = element * self.h
            x1 = (element + 1) * self.h
            midpoint = (x0 + x1) / 2.0
            endpoint_0 = full[element]
            endpoint_1 = full[element + 1]
            midpoint_value = self.exact(np.array([midpoint]))[0][0]
            # B0(1/2)=1/4, B1(1/2)=1/2, B2(1/2)=1/4.
            interior = 2.0 * midpoint_value - 0.5 * (endpoint_0 + endpoint_1)
            full[self.n + 1 + element] = max(0.0, interior)
        return full[self.free]

    def solve(self) -> tuple[np.ndarray, object]:
        initial = self.initial_guess()
        solution = root(
            lambda z: self.fischer_burmeister(z)[0],
            initial,
            jac=lambda z: self.fischer_burmeister(z)[1],
            method="hybr",
            options={"xtol": 1.0e-11, "maxfev": 5000},
        )
        return solution.x, solution

    def errors(self, z: np.ndarray, qorder: int = 20) -> tuple[float, float]:
        full = self.lift(z)
        tq, wq = leggauss(qorder)
        tq = (tq + 1.0) / 2.0
        wq = wq / 2.0
        B = np.vstack(((1.0 - tq) ** 2, 2.0 * tq * (1.0 - tq), tq**2)).T
        dBdt = np.vstack((-2.0 * (1.0 - tq), 2.0 * (1.0 - 2.0 * tq), 2.0 * tq)).T
        l2_squared = 0.0
        h1_squared = 0.0

        for element in range(self.n):
            xq = element * self.h + self.h * tq
            coefficient = full[self.local_dofs(element)]
            uh = B @ coefficient
            duh = (dBdt / self.h) @ coefficient
            u, du, _ = self.exact(xq)
            l2_squared += self.h * np.sum(wq * (uh - u) ** 2)
            h1_squared += self.h * np.sum(
                wq * ((uh - u) ** 2 + (duh - du) ** 2)
            )

        return float(np.sqrt(l2_squared)), float(np.sqrt(h1_squared))

    def run(self) -> Result:
        z, solution = self.solve()
        dual_residual, _ = self.residual_jacobian(z)
        complementarity_residual, _ = self.fischer_burmeister(z)
        l2_error, h1_error = self.errors(z)
        return Result(
            n_elements=self.n,
            h=self.h,
            success=bool(solution.success),
            iterations=int(getattr(solution, "nfev", 0)),
            residual_norm=float(np.linalg.norm(complementarity_residual, np.inf)),
            h1_error=h1_error,
            l2_error=l2_error,
            min_coefficient=float(np.min(z)),
            min_dual_residual=float(np.min(dual_residual)),
            complementarity_inf=float(np.max(np.abs(z * dual_residual))),
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--levels", default="32,64,128,256")
    parser.add_argument("--a", type=float, default=(np.sqrt(5.0) - 1.0) / 4.0)
    parser.add_argument("--beta", type=float, default=0.7)
    parser.add_argument("--c", type=float, default=1.0)
    parser.add_argument("--gamma", type=float, default=0.5)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("nonlinear_bernstein_vi_1d_results.json"),
    )
    args = parser.parse_args()

    results: list[Result] = []
    for n in map(int, args.levels.split(",")):
        result = BernsteinVI1D(n, args.a, args.beta, args.c, args.gamma).run()
        if results:
            result.observed_h1_rate = float(
                np.log(results[-1].h1_error / result.h1_error) / np.log(2.0)
            )
        results.append(result)
        print(asdict(result))

    payload = {
        "parameters": {
            "a": args.a,
            "beta": args.beta,
            "c": args.c,
            "gamma": args.gamma,
        },
        "results": [asdict(result) for result in results],
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n")

    if not all(result.success for result in results):
        raise SystemExit("nonlinear complementarity solve failed")
    if max(abs(result.min_coefficient) for result in results) > 1.0e-10:
        raise SystemExit("coefficient feasibility check failed")
    if max(abs(result.min_dual_residual) for result in results) > 1.0e-9:
        raise SystemExit("dual feasibility check failed")
    if max(result.complementarity_inf for result in results) > 1.0e-9:
        raise SystemExit("complementarity check failed")


if __name__ == "__main__":
    main()
