#!/usr/bin/env python3
"""Exact intact-core CP-SAT relaxation for the 41 ``s = 76`` core types.

For every intact four-vertex fiber, saturation forces one neighbor in each
relevant outside fiber. Hence every cross block incident with an intact fiber
is a 4-by-4 permutation matrix. This model keeps those S4 blocks and imposes
all original common-neighbor block equations whose two endpoint fibers are
intact:

* the three-holonomy equation for disjoint intact fibers;
* the six-path equation for intersecting intact fibers.

A feasible core is only a necessary condition for a Conway graph. An
``INFEASIBLE`` CP-SAT result is discovery evidence until converted to a checked
SAT/XOR certificate.
"""
from __future__ import annotations

import argparse
import json
import time
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path

from ortools.sat.python import cp_model

from s76_core_profiles import FIBERS, KG_EDGES, audit as core_profile_audit

PERMS = tuple(permutations(range(4)))
PERM_INDEX = {permutation: index for index, permutation in enumerate(PERMS)}
IDENTITY = PERM_INDEX[(0, 1, 2, 3)]
POINTS = range(4)
A4 = tuple(
    tuple(int(left != right and (left ^ right) != 3) for right in POINTS)
    for left in POINTS
)
I4 = tuple(tuple(int(left == right) for right in POINTS) for left in POINTS)
PMATS = tuple(
    tuple(
        tuple(int(permutation[left] == right) for right in POINTS)
        for left in POINTS
    )
    for permutation in PERMS
)
PMAT_INDEX = {matrix: index for index, matrix in enumerate(PMATS)}
EDGE_INDEX = {edge: index for index, edge in enumerate(KG_EDGES)}
COMMON_THIRDS = {
    edge: tuple(
        vertex
        for vertex in range(21)
        if vertex not in edge
        and set(FIBERS[vertex]).isdisjoint(FIBERS[edge[0]])
        and set(FIBERS[vertex]).isdisjoint(FIBERS[edge[1]])
    )
    for edge in KG_EDGES
}


def compose(left, right):
    return tuple(left[right[index]] for index in range(4))


def inverse(permutation):
    output = [0] * 4
    for left, right in enumerate(permutation):
        output[right] = left
    return tuple(output)


INVERSES = tuple(PERM_INDEX[inverse(permutation)] for permutation in PERMS)
COMPOSE = tuple(
    tuple(PERM_INDEX[compose(PERMS[left], PERMS[right])] for right in range(24))
    for left in range(24)
)


def oriented_value(edge, source, target, value):
    assert {source, target} == set(edge)
    return value if source < target else INVERSES[value]


def matrix_residual(target, *matrices):
    return tuple(
        tuple(
            target[left][right]
            - sum(matrix[left][right] for matrix in matrices)
            for right in POINTS
        )
        for left in POINTS
    )


@lru_cache(maxsize=1)
def local_holonomy_tuples():
    """Allowed ``(central edge, h1, h2, h3)`` tuples."""
    allowed = []
    for central, permutation in enumerate(PERMS):
        pulled_cycle = tuple(
            tuple(A4[permutation[left]][permutation[right]] for right in POINTS)
            for left in POINTS
        )
        target = tuple(
            tuple(
                2 - I4[left][right] - A4[left][right] - pulled_cycle[left][right]
                for right in POINTS
            )
            for left in POINTS
        )
        for first, second in product(range(24), repeat=2):
            needed = matrix_residual(target, PMATS[first], PMATS[second])
            third = PMAT_INDEX.get(needed)
            if third is not None:
                allowed.append((central, first, second, third))
    assert len(allowed) == 456
    return tuple(allowed)


@lru_cache(maxsize=4)
def intersecting_path_tuples(position_left: int, position_right: int):
    """Ordered six-permutation decompositions of the intersecting-fiber target."""
    same_sign = tuple(
        tuple(
            int(
                ((left >> position_left) & 1)
                == ((right >> position_right) & 1)
            )
            for right in POINTS
        )
        for left in POINTS
    )
    target = tuple(
        2 - same_sign[left][right]
        for left in POINTS
        for right in POINTS
    )
    flat_matrices = tuple(
        tuple(entry for row in matrix for entry in row) for matrix in PMATS
    )
    answers = []

    def visit(remaining: int, residual: tuple[int, ...], chosen: tuple[int, ...]):
        if remaining == 0:
            if not any(residual):
                answers.append(chosen)
            return
        for permutation, matrix in enumerate(flat_matrices):
            next_residual = tuple(
                left - right for left, right in zip(residual, matrix)
            )
            if min(next_residual) >= 0:
                visit(remaining - 1, next_residual, chosen + (permutation,))

    visit(6, target, ())
    assert len(answers) == 35_280
    return tuple(answers)


def composition_tuples(edge_one, source, middle, edge_two, target):
    allowed = []
    for first, second in product(range(24), repeat=2):
        first_oriented = oriented_value(edge_one, source, middle, first)
        second_oriented = oriented_value(edge_two, middle, target, second)
        path = COMPOSE[second_oriented][first_oriented]
        allowed.append((first, second, path))
    assert len(allowed) == 576
    return allowed


def holonomy_tuples(central_edge):
    # The central edge is oriented lower -> higher; the based loop returns
    # higher -> lower before applying the two-edge path lower -> higher.
    allowed = []
    for central, path in product(range(24), repeat=2):
        holonomy = COMPOSE[INVERSES[central]][path]
        allowed.append((central, path, holonomy))
    return allowed


def build_model(profile_index: int):
    profiles = core_profile_audit()["profiles"]
    if not 0 <= profile_index < len(profiles):
        raise ValueError(f"profile index must lie in [0,{len(profiles)-1}]")
    profile = profiles[profile_index]
    mask = int(profile["mask"])
    intact = {vertex for vertex in range(21) if (mask >> vertex) & 1}

    used_edges = [
        edge
        for edge in KG_EDGES
        if edge[0] in intact or edge[1] in intact
    ]
    edge_variables = {}
    model = cp_model.CpModel()
    for edge in used_edges:
        edge_variables[edge] = model.NewIntVar(0, 23, f"edge_{edge[0]}_{edge[1]}")

    intact_disjoint_edges = [
        edge for edge in KG_EDGES if edge[0] in intact and edge[1] in intact
    ]
    holonomy_variables = {}
    path_variables = {}
    local_tuples = local_holonomy_tuples()
    central_holonomy_tuples = holonomy_tuples(None)

    for central_edge in intact_disjoint_edges:
        left, right = central_edge
        based_holonomies = []
        for third in COMMON_THIRDS[central_edge]:
            first_edge = tuple(sorted((left, third)))
            second_edge = tuple(sorted((right, third)))
            assert first_edge in edge_variables and second_edge in edge_variables
            path_key = (left, third, right)
            path = model.NewIntVar(0, 23, f"path_{left}_{third}_{right}")
            path_variables[path_key] = path
            model.AddAllowedAssignments(
                [
                    edge_variables[first_edge],
                    edge_variables[second_edge],
                    path,
                ],
                composition_tuples(
                    first_edge, left, third, second_edge, right
                ),
            )
            holonomy = model.NewIntVar(
                0, 23, f"holonomy_{left}_{right}_{third}"
            )
            holonomy_variables[(central_edge, third)] = holonomy
            model.AddAllowedAssignments(
                [edge_variables[central_edge], path, holonomy],
                central_holonomy_tuples,
            )
            based_holonomies.append(holonomy)
        model.AddAllowedAssignments(
            [edge_variables[central_edge], *based_holonomies],
            local_tuples,
        )

    intact_intersecting_pairs = [
        (left, right)
        for left, right in combinations(sorted(intact), 2)
        if not set(FIBERS[left]).isdisjoint(FIBERS[right])
    ]
    six_path_variables = {}
    for left, right in intact_intersecting_pairs:
        shared = next(iter(set(FIBERS[left]) & set(FIBERS[right])))
        position_left = 0 if FIBERS[left][0] == shared else 1
        position_right = 0 if FIBERS[right][0] == shared else 1
        paths = []
        thirds = [
            third
            for third in range(21)
            if set(FIBERS[third]).isdisjoint(FIBERS[left])
            and set(FIBERS[third]).isdisjoint(FIBERS[right])
        ]
        assert len(thirds) == 6
        for third in thirds:
            first_edge = tuple(sorted((left, third)))
            second_edge = tuple(sorted((right, third)))
            assert first_edge in edge_variables and second_edge in edge_variables
            key = (left, third, right)
            path = model.NewIntVar(0, 23, f"six_path_{left}_{third}_{right}")
            six_path_variables[key] = path
            model.AddAllowedAssignments(
                [
                    edge_variables[first_edge],
                    edge_variables[second_edge],
                    path,
                ],
                composition_tuples(
                    first_edge, left, third, second_edge, right
                ),
            )
            paths.append(path)
        model.AddAllowedAssignments(
            paths,
            intersecting_path_tuples(position_left, position_right),
        )

    metadata = {
        "profile_index": profile_index,
        "profile": profile,
        "intact_fibers": len(intact),
        "edge_variables": len(edge_variables),
        "intact_disjoint_edges": len(intact_disjoint_edges),
        "intact_intersecting_pairs": len(intact_intersecting_pairs),
        "holonomy_variables": len(holonomy_variables),
        "three_path_variables": len(path_variables),
        "six_path_variables": len(six_path_variables),
    }
    context = {
        "intact": intact,
        "edge_variables": edge_variables,
        "profile": profile,
    }
    return model, context, metadata


def verify_core(context, solver):
    intact = context["intact"]
    values = {
        edge: solver.Value(variable)
        for edge, variable in context["edge_variables"].items()
    }

    def oriented(edge, source, target):
        return oriented_value(edge, source, target, values[edge])

    for central_edge in KG_EDGES:
        left, right = central_edge
        if left not in intact or right not in intact:
            continue
        central = PERMS[values[central_edge]]
        pulled = tuple(
            tuple(A4[central[x]][central[y]] for y in POINTS)
            for x in POINTS
        )
        holonomies = []
        for third in COMMON_THIRDS[central_edge]:
            first_edge = tuple(sorted((left, third)))
            second_edge = tuple(sorted((right, third)))
            path = compose(
                PERMS[oriented(second_edge, third, right)],
                PERMS[oriented(first_edge, left, third)],
            )
            holonomies.append(compose(PERMS[INVERSES[values[central_edge]]], path))
        for x, y in product(POINTS, repeat=2):
            total = I4[x][y] + A4[x][y] + pulled[x][y]
            total += sum(int(holonomy[x] == y) for holonomy in holonomies)
            assert total == 2

    for left, right in combinations(sorted(intact), 2):
        if set(FIBERS[left]).isdisjoint(FIBERS[right]):
            continue
        shared = next(iter(set(FIBERS[left]) & set(FIBERS[right])))
        position_left = 0 if FIBERS[left][0] == shared else 1
        position_right = 0 if FIBERS[right][0] == shared else 1
        paths = []
        for third in range(21):
            if not (
                set(FIBERS[third]).isdisjoint(FIBERS[left])
                and set(FIBERS[third]).isdisjoint(FIBERS[right])
            ):
                continue
            first_edge = tuple(sorted((left, third)))
            second_edge = tuple(sorted((right, third)))
            paths.append(
                compose(
                    PERMS[oriented(second_edge, third, right)],
                    PERMS[oriented(first_edge, left, third)],
                )
            )
        assert len(paths) == 6
        for x, y in product(POINTS, repeat=2):
            same_sign = int(
                ((x >> position_left) & 1) == ((y >> position_right) & 1)
            )
            assert same_sign + sum(int(path[x] == y) for path in paths) == 2

    return {
        "profile": context["profile"],
        "edge_permutations": {
            f"{edge[0]}-{edge[1]}": value for edge, value in sorted(values.items())
        },
    }


def solve_profile(profile_index: int, time_limit: float, workers: int, witness=None):
    started = time.time()
    model, context, metadata = build_model(profile_index)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    status = solver.Solve(model)
    result = {
        **metadata,
        "status": solver.StatusName(status),
        "seconds": time.time() - started,
        "branches": solver.NumBranches(),
        "conflicts": solver.NumConflicts(),
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        core = verify_core(context, solver)
        result["verified_core"] = True
        if witness:
            Path(witness).write_text(json.dumps(core, indent=2, sort_keys=True) + "\n")
            result["witness"] = witness
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", type=int)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--time-limit", type=float, default=300)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--out")
    args = parser.parse_args()
    if args.all == (args.profile is not None):
        parser.error("choose exactly one of --profile or --all")

    if args.all:
        count = len(core_profile_audit()["profiles"])
        results = [
            solve_profile(index, args.time_limit, args.workers)
            for index in range(count)
        ]
    else:
        results = [
            solve_profile(args.profile, args.time_limit, args.workers, args.out)
        ]
    print("RESULT_JSON " + json.dumps(results, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
