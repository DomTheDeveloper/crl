#!/usr/bin/env python3
"""Exact translation-lift CNF for the weight-48 ``s = 84`` holonomy sector.

A retained certificate contains 90 representatives for the physical linear
parts of all weight-48 four-fold-cover connections.  For one representative,
this program restores the ``V4 = F_2^2`` translations of the 105 affine edge
maps and encodes every remaining common-neighbor equation.

The finite-domain model has:

* 105 edge translations;
* 315 based triangle-holonomy translations;
* 630 intersecting-pair transport translations;
* 315 deterministic four-variable tables;
* 630 deterministic three-variable tables;
* 105 disjoint-edge tables;
* 105 intersecting-pair tables.

Thus a SAT model reconstructs a complete ``SRG(99,14,1,2)`` witness in the
``s=84`` branch, while an independently checked UNSAT proof eliminates the
selected physical-linear orbit.
"""
from __future__ import annotations

import argparse
import base64
import gzip
import hashlib
import json
import time
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path

FIBERS = list(combinations(range(7), 2))
KG_EDGES = [
    (i, j)
    for i, j in combinations(range(21), 2)
    if set(FIBERS[i]).isdisjoint(FIBERS[j])
]
EDGE_INDEX = {edge: i for i, edge in enumerate(KG_EDGES)}
TRIANGLES = [
    triple
    for triple in combinations(range(21), 3)
    if all(edge in EDGE_INDEX for edge in combinations(triple, 2))
]
EDGE_TRIANGLES = [[] for _ in KG_EDGES]
for triangle_index, triangle in enumerate(TRIANGLES):
    for edge in combinations(triangle, 2):
        EDGE_TRIANGLES[EDGE_INDEX[edge]].append(triangle_index)
INTERSECTING_PAIRS = [
    (u, v)
    for u, v in combinations(range(21), 2)
    if set(FIBERS[u]) & set(FIBERS[v])
]
assert len(KG_EDGES) == len(TRIANGLES) == len(INTERSECTING_PAIRS) == 105

QUOTIENTS = tuple(sorted(permutations((1, 2, 3))))
QUOTIENT_INDEX = {permutation: i for i, permutation in enumerate(QUOTIENTS)}


def quotient_compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[i] - 1] for i in range(3))


def quotient_inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
    inverse = [0] * 3
    for source, target in enumerate(permutation, 1):
        inverse[target - 1] = source
    return tuple(inverse)


QUOTIENT_MUL = tuple(
    tuple(QUOTIENT_INDEX[quotient_compose(left, right)] for right in QUOTIENTS)
    for left in QUOTIENTS
)
QUOTIENT_INV = tuple(QUOTIENT_INDEX[quotient_inverse(value)] for value in QUOTIENTS)
LINEAR_MAP = tuple((0,) + value for value in QUOTIENTS)
LINEAR_APPLY = tuple(tuple(linear[vector] for vector in range(4)) for linear in LINEAR_MAP)


def affine_compose(
    left: tuple[int, int],
    right: tuple[int, int],
) -> tuple[int, int]:
    """Return the affine map ``left`` after ``right``."""
    left_linear, left_translation = left
    right_linear, right_translation = right
    return (
        QUOTIENT_MUL[left_linear][right_linear],
        LINEAR_APPLY[left_linear][right_translation] ^ left_translation,
    )


def permutation_matrix(linear: int, translation: int) -> tuple[int, ...]:
    permutation = tuple(LINEAR_APPLY[linear][point] ^ translation for point in range(4))
    return tuple(
        int(permutation[source] == target)
        for source in range(4)
        for target in range(4)
    )


PERMUTATION_MATRICES = {
    (linear, translation): permutation_matrix(linear, translation)
    for linear in range(6)
    for translation in range(4)
}
IDENTITY_MATRIX = tuple(int(i == j) for i in range(4) for j in range(4))
CYCLE_MATRIX = tuple(
    int(i != j and (i ^ j) != 3)
    for i in range(4)
    for j in range(4)
)


def conjugated_cycle(linear: int) -> tuple[int, ...]:
    permutation = LINEAR_MAP[linear]
    return tuple(CYCLE_MATRIX[4 * permutation[i] + permutation[j]] for i in range(4) for j in range(4))


CONJUGATED_CYCLES = tuple(conjugated_cycle(linear) for linear in range(6))


def load_representatives(path: Path) -> dict[str, object]:
    compressed = base64.b64decode(path.read_text().strip())
    data = json.loads(gzip.decompress(compressed))
    assert data["PASS"]
    assert data["support_weight"] == 48
    assert data["physical_linear_orbits"] == 90
    assert len(data["representatives"]) == 90
    assert all(len(representative) == 105 for representative in data["representatives"])
    return data


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


class LiftModel:
    def __init__(self, configuration: list[int]):
        assert len(configuration) == 105
        assert all(0 <= value < 6 for value in configuration)
        self.configuration = configuration
        self.domains: list[list[int]] = []
        self.scopes: list[tuple[int, ...]] = []
        self.tables: list[tuple[tuple[int, ...], ...]] = []
        self.edge_variables = [self.new_domain() for _ in range(105)]
        self._build_tables()

    def new_domain(self) -> int:
        self.domains.append([])
        return len(self.domains) - 1

    def add_table(self, scope, rows) -> None:
        rows = tuple(dict.fromkeys(tuple(map(int, row)) for row in rows))
        assert rows
        assert all(len(row) == len(scope) for row in rows)
        self.scopes.append(tuple(scope))
        self.tables.append(rows)

    def oriented_descriptor(self, u: int, v: int) -> tuple[int, int, tuple[int, ...]]:
        edge = EDGE_INDEX[(min(u, v), max(u, v))]
        linear = self.configuration[edge]
        if u < v:
            return edge, linear, (0, 1, 2, 3)
        inverse = QUOTIENT_INV[linear]
        return edge, inverse, tuple(LINEAR_APPLY[inverse][translation] for translation in range(4))

    @staticmethod
    def evaluate_descriptor(descriptor, stored_translation: int) -> tuple[int, int]:
        return descriptor[1], descriptor[2][stored_translation]

    @staticmethod
    def intersecting_target(u: int, v: int) -> tuple[int, ...]:
        shared = next(iter(set(FIBERS[u]) & set(FIBERS[v])))
        bit_u = 1 if FIBERS[u][0] == shared else 0
        bit_v = 1 if FIBERS[v][0] == shared else 0
        same_sign = tuple(
            int(((x >> bit_u) & 1) == ((y >> bit_v) & 1))
            for x in range(4)
            for y in range(4)
        )
        return tuple(2 - value for value in same_sign)

    def _build_tables(self) -> None:
        holonomy_variable: dict[tuple[int, int], int] = {}
        holonomy_linear: dict[tuple[int, int], int] = {}

        # Every edge-triangle incidence receives its based holonomy translation.
        for edge, (u, v) in enumerate(KG_EDGES):
            for triangle_index in EDGE_TRIANGLES[edge]:
                triangle = TRIANGLES[triangle_index]
                w = next(vertex for vertex in triangle if vertex not in (u, v))
                variable = self.new_domain()
                holonomy_variable[(edge, triangle_index)] = variable
                triangle_edges = [EDGE_INDEX[item] for item in combinations(triangle, 2)]
                first = self.oriented_descriptor(v, u)
                second = self.oriented_descriptor(w, v)
                third = self.oriented_descriptor(u, w)
                linear = affine_compose(
                    (first[1], 0),
                    affine_compose((second[1], 0), (third[1], 0)),
                )[0]
                holonomy_linear[(edge, triangle_index)] = linear
                rows = []
                for translations in product(range(4), repeat=3):
                    assignment = dict(zip(triangle_edges, translations))
                    holonomy = affine_compose(
                        self.evaluate_descriptor(first, assignment[first[0]]),
                        affine_compose(
                            self.evaluate_descriptor(second, assignment[second[0]]),
                            self.evaluate_descriptor(third, assignment[third[0]]),
                        ),
                    )
                    rows.append(translations + (holonomy[1],))
                self.add_table(
                    [self.edge_variables[item] for item in triangle_edges] + [variable],
                    rows,
                )

        # Three triangle holonomies around each disjoint-fiber edge.
        for edge, _ in enumerate(KG_EDGES):
            triangle_indices = EDGE_TRIANGLES[edge]
            variables = [holonomy_variable[(edge, triangle)] for triangle in triangle_indices]
            linears = [holonomy_linear[(edge, triangle)] for triangle in triangle_indices]
            base = tuple(
                IDENTITY_MATRIX[index]
                + CYCLE_MATRIX[index]
                + CONJUGATED_CYCLES[self.configuration[edge]][index]
                for index in range(16)
            )
            rows = []
            for translations in product(range(4), repeat=3):
                if all(
                    base[index]
                    + sum(
                        PERMUTATION_MATRICES[(linears[position], translations[position])][index]
                        for position in range(3)
                    )
                    == 2
                    for index in range(16)
                ):
                    rows.append(translations)
            self.add_table(variables, rows)

        # Six transports through disjoint third fibers for every intersecting pair.
        for u, v in INTERSECTING_PAIRS:
            thirds = [
                w
                for w in range(21)
                if set(FIBERS[w]).isdisjoint(FIBERS[u])
                and set(FIBERS[w]).isdisjoint(FIBERS[v])
            ]
            assert len(thirds) == 6
            transport_variables = []
            transport_linears = []
            for w in thirds:
                variable = self.new_domain()
                transport_variables.append(variable)
                first = self.oriented_descriptor(w, v)
                second = self.oriented_descriptor(u, w)
                edge_u = second[0]
                edge_v = first[0]
                assert edge_u != edge_v
                linear = affine_compose((first[1], 0), (second[1], 0))[0]
                transport_linears.append(linear)
                rows = []
                for translation_u, translation_v in product(range(4), repeat=2):
                    transport = affine_compose(
                        self.evaluate_descriptor(first, translation_v),
                        self.evaluate_descriptor(second, translation_u),
                    )
                    rows.append((translation_u, translation_v, transport[1]))
                self.add_table(
                    [self.edge_variables[edge_u], self.edge_variables[edge_v], variable],
                    rows,
                )

            target = self.intersecting_target(u, v)
            matrices = [
                [PERMUTATION_MATRICES[(linear, translation)] for translation in range(4)]
                for linear in transport_linears
            ]
            rows = []
            for translations in product(range(4), repeat=6):
                if all(
                    sum(matrices[position][translations[position]][index] for position in range(6))
                    == target[index]
                    for index in range(16)
                ):
                    rows.append(translations)
            self.add_table(transport_variables, rows)

        assert len(self.domains) == 1050
        assert len(self.scopes) == len(self.tables) == 1155

    def encode_cnf(self) -> tuple[int, list[list[int]], list[tuple[int, ...]]]:
        clauses: list[list[int]] = []
        domain_literals: list[tuple[int, ...]] = []
        next_variable = 1
        for _ in self.domains:
            literals = tuple(range(next_variable, next_variable + 4))
            next_variable += 4
            domain_literals.append(literals)
            clauses.append(list(literals))
            for left, right in combinations(literals, 2):
                clauses.append([-left, -right])

        for scope, rows in zip(self.scopes, self.tables):
            selectors = tuple(range(next_variable, next_variable + len(rows)))
            next_variable += len(rows)
            clauses.append(list(selectors))
            for selector, row in zip(selectors, rows):
                for domain, value in zip(scope, row):
                    clauses.append([-selector, domain_literals[domain][value]])
            # Reverse support clauses improve propagation and make each table
            # independently auditable from the CNF.
            for position, domain in enumerate(scope):
                for value in range(4):
                    support = [
                        selectors[row_index]
                        for row_index, row in enumerate(rows)
                        if row[position] == value
                    ]
                    clauses.append([-domain_literals[domain][value], *support])

        return next_variable - 1, clauses, domain_literals

    def reconstruct_edges(self, translations: list[int]) -> list[tuple[int, int]]:
        from s84_cover_sat import C0, MEMBERS

        edges = set(C0)
        for edge, (fiber_u, fiber_v) in enumerate(KG_EDGES):
            linear = LINEAR_APPLY[self.configuration[edge]]
            translation = translations[edge]
            for point in range(4):
                target = linear[point] ^ translation
                u = MEMBERS[FIBERS[fiber_u]][point]
                v = MEMBERS[FIBERS[fiber_v]][target]
                edges.add((u, v) if u < v else (v, u))
        assert len(edges) == 504
        return sorted(edges)


def write_dimacs(path: Path, variables: int, clauses: list[list[int]]) -> None:
    with path.open("w") as handle:
        handle.write(f"p cnf {variables} {len(clauses)}\n")
        for clause in clauses:
            handle.write(" ".join(map(str, clause)) + " 0\n")


def main() -> None:
    default_representatives = (
        Path(__file__).resolve().parents[1]
        / "certificates"
        / "s84_weight48_linear_orbits.json.gz.b64"
    )
    parser = argparse.ArgumentParser()
    parser.add_argument("--representatives", type=Path, default=default_representatives)
    parser.add_argument("--orbit", type=int, required=True)
    parser.add_argument("--cnf", type=Path)
    parser.add_argument("--emit-only", action="store_true")
    parser.add_argument("--solver", default="glucose4")
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--witness", type=Path)
    args = parser.parse_args()

    data = load_representatives(args.representatives)
    if not 0 <= args.orbit < 90:
        parser.error("--orbit must lie in 0..89")
    configuration = list(map(int, data["representatives"][args.orbit]))

    started = time.time()
    model = LiftModel(configuration)
    variables, clauses, domain_literals = model.encode_cnf()
    metadata = {
        "branch": "s=84, curvature weight 48",
        "orbit": args.orbit,
        "finite_domain_variables": len(model.domains),
        "table_constraints": len(model.tables),
        "table_size_histogram": {
            str(size): count
            for size, count in sorted(Counter(map(len, model.tables)).items())
        },
        "variables": variables,
        "clauses": len(clauses),
        "build_seconds": time.time() - started,
        "representatives_sha256": sha256(args.representatives),
    }
    if args.cnf:
        write_dimacs(args.cnf, variables, clauses)
        metadata["cnf"] = str(args.cnf)
        metadata["cnf_sha256"] = sha256(args.cnf)
    print("RESULT_JSON " + json.dumps({"event": "emitted", **metadata}, sort_keys=True), flush=True)
    if args.emit_only:
        return

    from pysat.solvers import Solver

    with Solver(
        name=args.solver,
        bootstrap_with=clauses,
        with_proof=bool(args.proof),
    ) as solver:
        solve_started = time.time()
        satisfiable = solver.solve()
        result = {
            **metadata,
            "solver": args.solver,
            "status": "SAT" if satisfiable else "UNSAT",
            "solve_seconds": time.time() - solve_started,
        }
        if satisfiable:
            positive = {literal for literal in solver.get_model() if literal > 0}
            translations = []
            for edge_variable in model.edge_variables:
                values = [
                    value
                    for value, literal in enumerate(domain_literals[edge_variable])
                    if literal in positive
                ]
                assert len(values) == 1
                translations.append(values[0])
            edges = model.reconstruct_edges(translations)
            from model import make_root_model
            from verify import verify_reduced

            verify_reduced(make_root_model(14), edges)
            if args.witness:
                args.witness.write_text(
                    json.dumps(
                        {
                            "k": 14,
                            "orbit": args.orbit,
                            "translations": translations,
                            "edges": [list(edge) for edge in edges],
                        },
                        indent=2,
                        sort_keys=True,
                    )
                    + "\n"
                )
                result["witness"] = str(args.witness)
                result["witness_sha256"] = sha256(args.witness)
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
