#!/usr/bin/env python3
"""Proof-producing position-sensitive ``S3`` quotient for ``s = 76`` cores.

Every six-valued variable is one-hot encoded.  Each exact finite relation uses
selector variables with bidirectional support clauses, so satisfying assignments
are precisely the tuples accepted by the audited quotient tables.  An UNSAT
answer counts only after its DRUP trace is checked independently.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Solver

from s76_core_profiles import FIBERS, KG_EDGES, audit as core_profile_audit
from s76_linear_quotient_cpsat import (
    quotient_composition_tuples,
    quotient_holonomy_tuples,
    quotient_local_tuples,
    quotient_six_path_tuples,
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


class Model:
    def __init__(self, profile: dict[str, int]):
        self.profile = profile
        mask = int(profile["mask"])
        self.intact = {vertex for vertex in range(21) if (mask >> vertex) & 1}
        self.used_edges = [
            edge for edge in KG_EDGES if edge[0] in self.intact or edge[1] in self.intact
        ]
        self.next_variable = 1
        self.cnf = CNF()
        self.domains: dict[object, tuple[int, ...]] = {}
        self.tables: list[tuple[tuple[object, ...], tuple[tuple[int, ...], ...]]] = []
        self.edge_keys = {edge: ("edge", *edge) for edge in self.used_edges}
        for key in self.edge_keys.values():
            self.new_domain(key)

        self.common_thirds = {
            edge: tuple(
                vertex
                for vertex in range(21)
                if vertex not in edge
                and set(FIBERS[vertex]).isdisjoint(FIBERS[edge[0]])
                and set(FIBERS[vertex]).isdisjoint(FIBERS[edge[1]])
            )
            for edge in KG_EDGES
        }
        self.central_edges = [
            edge for edge in KG_EDGES if edge[0] in self.intact and edge[1] in self.intact
        ]
        self.intersecting_pairs = [
            (left, right)
            for left, right in combinations(sorted(self.intact), 2)
            if set(FIBERS[left]) & set(FIBERS[right])
        ]
        self.three_path_keys = {}
        self.holonomy_keys = {}
        self.six_path_keys = {}
        self.position_histogram = {"00": 0, "01": 0, "10": 0, "11": 0}
        self._encode_disjoint_relations()
        self._encode_intersecting_relations()

    def new_boolean(self) -> int:
        variable = self.next_variable
        self.next_variable += 1
        return variable

    def new_domain(self, key: object) -> tuple[int, ...]:
        assert key not in self.domains
        values = tuple(self.new_boolean() for _ in range(6))
        self.domains[key] = values
        self.cnf.append(list(values))
        for left, right in combinations(values, 2):
            self.cnf.append([-left, -right])
        return values

    def add_table(
        self,
        scope: tuple[object, ...],
        allowed: tuple[tuple[int, ...], ...] | list[tuple[int, ...]],
    ) -> None:
        allowed = tuple(allowed)
        assert allowed and all(len(row) == len(scope) for row in allowed)
        assert len(set(allowed)) == len(allowed)
        for key in scope:
            assert key in self.domains

        selectors = tuple(self.new_boolean() for _ in allowed)
        self.cnf.append(list(selectors))
        for selector, row in zip(selectors, allowed):
            for key, value in zip(scope, row):
                assert 0 <= value < 6
                self.cnf.append([-selector, self.domains[key][value]])
        for position, key in enumerate(scope):
            for value in range(6):
                supporters = [
                    selector
                    for selector, row in zip(selectors, allowed)
                    if row[position] == value
                ]
                assert supporters
                self.cnf.append([-self.domains[key][value], *supporters])
        self.tables.append((scope, allowed))

    def _encode_disjoint_relations(self) -> None:
        for central_edge in self.central_edges:
            left, right = central_edge
            based_holonomies = []
            for third in self.common_thirds[central_edge]:
                first_edge = tuple(sorted((left, third)))
                second_edge = tuple(sorted((right, third)))
                path_key = ("three_path", left, third, right)
                self.three_path_keys[(left, third, right)] = path_key
                self.new_domain(path_key)
                self.add_table(
                    (
                        self.edge_keys[first_edge],
                        self.edge_keys[second_edge],
                        path_key,
                    ),
                    quotient_composition_tuples(
                        first_edge, left, third, second_edge, right
                    ),
                )
                holonomy_key = ("holonomy", left, right, third)
                self.holonomy_keys[(central_edge, third)] = holonomy_key
                self.new_domain(holonomy_key)
                self.add_table(
                    (self.edge_keys[central_edge], path_key, holonomy_key),
                    quotient_holonomy_tuples(),
                )
                based_holonomies.append(holonomy_key)
            self.add_table(
                (self.edge_keys[central_edge], *based_holonomies),
                quotient_local_tuples(),
            )

    def _encode_intersecting_relations(self) -> None:
        for left, right in self.intersecting_pairs:
            shared = next(iter(set(FIBERS[left]) & set(FIBERS[right])))
            position_left = 0 if FIBERS[left][0] == shared else 1
            position_right = 0 if FIBERS[right][0] == shared else 1
            self.position_histogram[f"{position_left}{position_right}"] += 1
            paths = []
            for third in range(21):
                if not (
                    set(FIBERS[third]).isdisjoint(FIBERS[left])
                    and set(FIBERS[third]).isdisjoint(FIBERS[right])
                ):
                    continue
                first_edge = tuple(sorted((left, third)))
                second_edge = tuple(sorted((right, third)))
                path_key = ("six_path", left, third, right)
                self.six_path_keys[(left, third, right)] = path_key
                self.new_domain(path_key)
                self.add_table(
                    (
                        self.edge_keys[first_edge],
                        self.edge_keys[second_edge],
                        path_key,
                    ),
                    quotient_composition_tuples(
                        first_edge, left, third, second_edge, right
                    ),
                )
                paths.append(path_key)
            assert len(paths) == 6
            self.add_table(
                tuple(paths),
                quotient_six_path_tuples(position_left, position_right),
            )

    @property
    def variables(self) -> int:
        return self.next_variable - 1

    def decode_assignment(self, positive: set[int]) -> dict[object, int]:
        values = {}
        for key, literals in self.domains.items():
            selected = [value for value, literal in enumerate(literals) if literal in positive]
            assert len(selected) == 1
            values[key] = selected[0]
        for scope, allowed in self.tables:
            row = tuple(values[key] for key in scope)
            assert row in allowed
        return values

    def verify_assignment(self, positive: set[int]) -> dict[str, object]:
        values = self.decode_assignment(positive)
        return {
            "edge_linear_permutations": {
                f"{edge[0]}-{edge[1]}": values[key]
                for edge, key in sorted(self.edge_keys.items())
            },
            "domains": len(self.domains),
            "table_constraints": len(self.tables),
            "position_histogram": self.position_histogram,
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
    model = Model(report["profiles"][args.profile])
    metadata = {
        "profile_index": args.profile,
        "profile": model.profile,
        "variables": model.variables,
        "clauses": len(model.cnf.clauses),
        "domains": len(model.domains),
        "table_constraints": len(model.tables),
        "edge_domains": len(model.edge_keys),
        "three_path_domains": len(model.three_path_keys),
        "holonomy_domains": len(model.holonomy_keys),
        "six_path_domains": len(model.six_path_keys),
        "central_disjoint_edges": len(model.central_edges),
        "intact_intersecting_pairs": len(model.intersecting_pairs),
        "position_histogram": model.position_histogram,
    }
    if args.cnf:
        write_dimacs(args.cnf, model.variables, model.cnf.clauses)
        metadata["cnf"] = str(args.cnf)
        metadata["cnf_sha256"] = sha256(args.cnf)
    print("RESULT_JSON " + json.dumps({"event": "emitted", **metadata}, sort_keys=True), flush=True)
    if args.emit_only:
        return

    with Solver(
        name=args.solver,
        bootstrap_with=model.cnf.clauses,
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
