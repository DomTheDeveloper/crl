#!/usr/bin/env python3
"""Proof-producing parity/conjugacy filter for ``s = 76`` intact cores.

This is a necessary-condition projection of the exact S4 block equations.
For every cross-block permutation retain only its sign.  For every triangle
holonomy retain:

* its sign ``z``;
* one class bit ``c`` distinguishing identity from double transposition when
  ``z=0``, and four-cycle from transposition when ``z=1``.

For a disjoint pair of intact fibers the three incident triangle holonomies
obey the exact local rule:

* all three signs are even and exactly one class bit is one; or
* exactly two signs are odd and all three class bits agree.

For a pair of intersecting intact fibers, the six two-edge path signs can have
any weight except one or five.  These rules are necessary consequences of the
original common-neighbor block equations.  Therefore an independently checked
UNSAT proof eliminates the entire intact-core type.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations, product
from pathlib import Path

from s76_core_profiles import FIBERS, KG_EDGES, audit as core_profile_audit

EDGE_INDEX = {edge: index for index, edge in enumerate(KG_EDGES)}
TRIANGLES = [
    triangle
    for triangle in combinations(range(21), 3)
    if all(
        set(FIBERS[left]).isdisjoint(FIBERS[right])
        for left, right in combinations(triangle, 2)
    )
]
TRIANGLE_INDEX = {triangle: index for index, triangle in enumerate(TRIANGLES)}
EDGE_TRIANGLES = {
    edge: tuple(
        TRIANGLE_INDEX[tuple(sorted((*edge, third)))]
        for third in range(21)
        if third not in edge
        and set(FIBERS[third]).isdisjoint(FIBERS[edge[0]])
        and set(FIBERS[third]).isdisjoint(FIBERS[edge[1]])
    )
    for edge in KG_EDGES
}
assert all(len(values) == 3 for values in EDGE_TRIANGLES.values())


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def forbidden_clause(variables: tuple[int, ...], assignment: tuple[int, ...]) -> list[int]:
    return [(-variable if value else variable) for variable, value in zip(variables, assignment)]


class Model:
    def __init__(self, profile: dict[str, int]):
        self.profile = profile
        mask = int(profile["mask"])
        self.intact = {vertex for vertex in range(21) if (mask >> vertex) & 1}
        self.used_edges = [
            edge for edge in KG_EDGES if edge[0] in self.intact or edge[1] in self.intact
        ]
        self.central_edges = [
            edge for edge in KG_EDGES if edge[0] in self.intact and edge[1] in self.intact
        ]
        self.intersecting_pairs = [
            (left, right)
            for left, right in combinations(sorted(self.intact), 2)
            if set(FIBERS[left]) & set(FIBERS[right])
        ]
        self.next_variable = 1
        self.clauses: list[list[int]] = []
        self.edge_parity = {edge: self.new_variable() for edge in self.used_edges}

        relevant_triangles = sorted(
            {
                triangle
                for edge in self.central_edges
                for triangle in EDGE_TRIANGLES[edge]
            }
        )
        self.triangle_parity = {
            triangle: self.new_variable() for triangle in relevant_triangles
        }
        self.triangle_class = {
            triangle: self.new_variable() for triangle in relevant_triangles
        }
        self.path_parity = {}
        self._encode_triangle_parities()
        self._encode_local_class_rules()
        self._encode_intersecting_path_rules()

    def new_variable(self) -> int:
        variable = self.next_variable
        self.next_variable += 1
        return variable

    def add_xor_zero(self, variables: tuple[int, ...]) -> None:
        for assignment in product((0, 1), repeat=len(variables)):
            if sum(assignment) & 1:
                self.clauses.append(forbidden_clause(variables, assignment))

    def _encode_triangle_parities(self) -> None:
        for triangle, z_variable in self.triangle_parity.items():
            vertices = TRIANGLES[triangle]
            edge_variables = tuple(
                self.edge_parity[edge]
                for edge in combinations(vertices, 2)
            )
            assert len(edge_variables) == 3
            # z is the sign of the three-edge holonomy.
            self.add_xor_zero((*edge_variables, z_variable))

    def _encode_local_class_rules(self) -> None:
        allowed = set()
        for z_values in product((0, 1), repeat=3):
            for c_values in product((0, 1), repeat=3):
                valid = (
                    sum(z_values) == 0 and sum(c_values) == 1
                ) or (
                    sum(z_values) == 2 and c_values[0] == c_values[1] == c_values[2]
                )
                if valid:
                    allowed.add(z_values + c_values)
        assert len(allowed) == 9

        for edge in self.central_edges:
            triangles = EDGE_TRIANGLES[edge]
            variables = tuple(self.triangle_parity[t] for t in triangles) + tuple(
                self.triangle_class[t] for t in triangles
            )
            for assignment in product((0, 1), repeat=6):
                if assignment not in allowed:
                    self.clauses.append(forbidden_clause(variables, assignment))

    def _encode_intersecting_path_rules(self) -> None:
        for left, right in self.intersecting_pairs:
            thirds = [
                middle
                for middle in range(21)
                if set(FIBERS[middle]).isdisjoint(FIBERS[left])
                and set(FIBERS[middle]).isdisjoint(FIBERS[right])
            ]
            assert len(thirds) == 6
            variables = []
            for middle in thirds:
                first = tuple(sorted((left, middle)))
                second = tuple(sorted((right, middle)))
                assert first in self.edge_parity and second in self.edge_parity
                key = (left, middle, right)
                path = self.new_variable()
                self.path_parity[key] = path
                variables.append(path)
                # path = sign(first) xor sign(second).
                self.add_xor_zero((self.edge_parity[first], self.edge_parity[second], path))

            variables = tuple(variables)
            for assignment in product((0, 1), repeat=6):
                if sum(assignment) in (1, 5):
                    self.clauses.append(forbidden_clause(variables, assignment))

    @property
    def variables(self) -> int:
        return self.next_variable - 1

    def verify_assignment(self, positive: set[int]) -> dict[str, object]:
        edge_values = {
            edge: int(variable in positive)
            for edge, variable in self.edge_parity.items()
        }
        triangle_values = {}
        for triangle in self.triangle_parity:
            z = int(self.triangle_parity[triangle] in positive)
            c = int(self.triangle_class[triangle] in positive)
            vertices = TRIANGLES[triangle]
            assert z == sum(edge_values[edge] for edge in combinations(vertices, 2)) % 2
            triangle_values[triangle] = (z, c)

        for edge in self.central_edges:
            values = [triangle_values[triangle] for triangle in EDGE_TRIANGLES[edge]]
            z_values = [value[0] for value in values]
            c_values = [value[1] for value in values]
            assert (
                sum(z_values) == 0 and sum(c_values) == 1
            ) or (
                sum(z_values) == 2 and c_values[0] == c_values[1] == c_values[2]
            )

        path_weight_histogram = {}
        for left, right in self.intersecting_pairs:
            values = []
            for middle in range(21):
                key = (left, middle, right)
                if key not in self.path_parity:
                    continue
                first = tuple(sorted((left, middle)))
                second = tuple(sorted((right, middle)))
                value = edge_values[first] ^ edge_values[second]
                assert value == int(self.path_parity[key] in positive)
                values.append(value)
            assert len(values) == 6 and sum(values) not in (1, 5)
            path_weight_histogram[str(sum(values))] = (
                path_weight_histogram.get(str(sum(values)), 0) + 1
            )

        return {
            "edge_parity_weight": sum(edge_values.values()),
            "triangle_parity_weight": sum(value[0] for value in triangle_values.values()),
            "triangle_class_weight": sum(value[1] for value in triangle_values.values()),
            "intersecting_path_weight_histogram": path_weight_histogram,
        }


def write_dimacs(path: Path, variables: int, clauses: list[list[int]]) -> None:
    with path.open("w") as handle:
        handle.write(f"p cnf {variables} {len(clauses)}\n")
        for clause in clauses:
            handle.write(" ".join(map(str, clause)) + " 0\n")


def load_profiles(path: Path | None) -> dict[str, object]:
    report = core_profile_audit() if path is None else json.loads(path.read_text())
    assert report["PASS"]
    assert report["completed_transition_orbits"] == 701
    assert report["S7_intact_core_orbits"] == 41
    assert len(report["profiles"]) == 41
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", type=Path)
    parser.add_argument("--profile", type=int, required=True)
    parser.add_argument("--cnf", type=Path)
    parser.add_argument("--emit-only", action="store_true")
    parser.add_argument("--solver", default="glucose4")
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--assignment", type=Path)
    args = parser.parse_args()

    report = load_profiles(args.profiles)
    if not 0 <= args.profile < 41:
        parser.error("--profile must lie in 0..40")
    profile = report["profiles"][args.profile]
    model = Model(profile)
    metadata = {
        "profile_index": args.profile,
        "profile": profile,
        "variables": model.variables,
        "clauses": len(model.clauses),
        "edge_parity_variables": len(model.edge_parity),
        "triangle_parity_variables": len(model.triangle_parity),
        "triangle_class_variables": len(model.triangle_class),
        "path_parity_variables": len(model.path_parity),
        "central_disjoint_edges": len(model.central_edges),
        "intact_intersecting_pairs": len(model.intersecting_pairs),
    }
    if args.cnf:
        write_dimacs(args.cnf, model.variables, model.clauses)
        metadata["cnf"] = str(args.cnf)
        metadata["cnf_sha256"] = sha256(args.cnf)
    print("RESULT_JSON " + json.dumps({"event": "emitted", **metadata}, sort_keys=True), flush=True)
    if args.emit_only:
        return

    from pysat.solvers import Solver

    with Solver(
        name=args.solver,
        bootstrap_with=model.clauses,
        with_proof=bool(args.proof),
    ) as solver:
        satisfiable = solver.solve()
        result = {
            **metadata,
            "solver": args.solver,
            "status": "SAT" if satisfiable else "UNSAT",
        }
        if satisfiable:
            positive = {literal for literal in solver.get_model() if literal > 0}
            verified = model.verify_assignment(positive)
            result["verified_assignment"] = verified
            if args.assignment:
                args.assignment.write_text(
                    json.dumps(
                        {
                            "profile_index": args.profile,
                            "positive_literals": sorted(positive),
                            **verified,
                        },
                        indent=2,
                        sort_keys=True,
                    )
                    + "\n"
                )
                result["assignment"] = str(args.assignment)
                result["assignment_sha256"] = sha256(args.assignment)
        elif args.proof:
            proof = solver.get_proof()
            if not proof:
                raise RuntimeError("UNSAT returned without a proof trace")
            args.proof.write_text("\n".join(proof) + "\n")
            result["proof"] = str(args.proof)
            result["proof_lines"] = len(proof)
            result["proof_sha256"] = sha256(args.proof)

    print("RESULT_JSON " + json.dumps(result, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
