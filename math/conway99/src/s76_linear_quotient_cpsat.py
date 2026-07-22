#!/usr/bin/env python3
"""Exact ``S4 -> GL(2,2) = S3`` quotient for the 41 ``s = 76`` core types.

The full intact-core model uses affine permutations of the four sign states.
Projecting an affine permutation to its linear part gives a six-valued edge
variable.  This is a necessary relaxation, but it is substantially stronger
than permutation parity.

A critical detail is retained explicitly: the six-path table depends on which
coordinate of each endpoint fiber is the shared base point.  The four projected
tables all have 2,192 tuples, but they are not the same set.

A feasible quotient is only a necessary condition.  ``INFEASIBLE`` is solver
evidence until converted to a proof-producing CNF certificate.
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
from s76_intact_core_cpsat import (
    PERMS,
    composition_tuples,
    holonomy_tuples,
    intersecting_path_tuples,
    local_holonomy_tuples,
)


NONZERO = (1, 2, 3)
LINEAR = tuple((0, NONZERO[p[0]], NONZERO[p[1]], NONZERO[p[2]]) for p in permutations(range(3)))
LINEAR_INDEX = {permutation: index for index, permutation in enumerate(LINEAR)}


def compose(left, right):
    return tuple(left[right[index]] for index in range(4))


def inverse(permutation):
    output = [0] * 4
    for left, right in enumerate(permutation):
        output[right] = left
    return tuple(output)


LINEAR_INVERSES = tuple(LINEAR_INDEX[inverse(permutation)] for permutation in LINEAR)
LINEAR_COMPOSE = tuple(
    tuple(LINEAR_INDEX[compose(left, right)] for right in LINEAR)
    for left in LINEAR
)


def affine_parts(permutation_index: int) -> tuple[int, int]:
    permutation = PERMS[permutation_index]
    translation = permutation[0]
    linear = tuple(permutation[value] ^ translation for value in range(4))
    return LINEAR_INDEX[linear], translation


@lru_cache(maxsize=1)
def quotient_local_tuples() -> tuple[tuple[int, int, int, int], ...]:
    projected = {
        tuple(affine_parts(value)[0] for value in row)
        for row in local_holonomy_tuples()
    }
    assert len(projected) == 48
    return tuple(sorted(projected))


@lru_cache(maxsize=4)
def quotient_six_path_tuples(
    position_left: int, position_right: int
) -> tuple[tuple[int, int, int, int, int, int], ...]:
    projected = {
        tuple(affine_parts(value)[0] for value in row)
        for row in intersecting_path_tuples(position_left, position_right)
    }
    assert len(projected) == 2_192
    return tuple(sorted(projected))


def quotient_table_audit() -> dict[str, object]:
    tables = {
        (left, right): quotient_six_path_tuples(left, right)
        for left in (0, 1)
        for right in (0, 1)
    }
    symmetric_differences = {
        f"{a[0]}{a[1]}-{b[0]}{b[1]}": len(set(tables[a]) ^ set(tables[b]))
        for a, b in combinations(sorted(tables), 2)
    }
    assert all(value > 0 for value in symmetric_differences.values())
    assert symmetric_differences == {
        "00-01": 1024,
        "00-10": 1024,
        "00-11": 722,
        "01-10": 722,
        "01-11": 1024,
        "10-11": 1024,
    }
    return {
        "PASS": True,
        "local_quotient_tuples": len(quotient_local_tuples()),
        "six_path_quotient_tuples": {
            f"{left}{right}": len(tables[(left, right)])
            for left in (0, 1)
            for right in (0, 1)
        },
        "pairwise_symmetric_differences": symmetric_differences,
        "consequence": "the shared-coordinate positions cannot be identified in the S3 quotient",
    }


def oriented_linear(edge, source: int, target: int, value: int) -> int:
    assert {source, target} == set(edge)
    return value if source < target else LINEAR_INVERSES[value]


def quotient_composition_tuples(edge_one, source, middle, edge_two, target):
    allowed = []
    for first, second in product(range(6), repeat=2):
        first_oriented = oriented_linear(edge_one, source, middle, first)
        second_oriented = oriented_linear(edge_two, middle, target, second)
        path = LINEAR_COMPOSE[second_oriented][first_oriented]
        allowed.append((first, second, path))
    assert len(allowed) == 36
    return allowed


def quotient_holonomy_tuples():
    return tuple(
        (
            central,
            path,
            LINEAR_COMPOSE[LINEAR_INVERSES[central]][path],
        )
        for central, path in product(range(6), repeat=2)
    )


def build_model(profile_index: int):
    profiles = core_profile_audit()["profiles"]
    if not 0 <= profile_index < len(profiles):
        raise ValueError(f"profile index must lie in [0,{len(profiles)-1}]")
    profile = profiles[profile_index]
    mask = int(profile["mask"])
    intact = {vertex for vertex in range(21) if (mask >> vertex) & 1}

    used_edges = [
        edge for edge in KG_EDGES if edge[0] in intact or edge[1] in intact
    ]
    model = cp_model.CpModel()
    edge_variables = {
        edge: model.NewIntVar(0, 5, f"linear_edge_{edge[0]}_{edge[1]}")
        for edge in used_edges
    }

    common_thirds = {
        edge: tuple(
            vertex
            for vertex in range(21)
            if vertex not in edge
            and set(FIBERS[vertex]).isdisjoint(FIBERS[edge[0]])
            and set(FIBERS[vertex]).isdisjoint(FIBERS[edge[1]])
        )
        for edge in KG_EDGES
    }

    intact_disjoint_edges = [
        edge for edge in KG_EDGES if edge[0] in intact and edge[1] in intact
    ]
    holonomy_variables = {}
    three_path_variables = {}
    for central_edge in intact_disjoint_edges:
        left, right = central_edge
        based_holonomies = []
        for third in common_thirds[central_edge]:
            first_edge = tuple(sorted((left, third)))
            second_edge = tuple(sorted((right, third)))
            path = model.NewIntVar(0, 5, f"linear_path_{left}_{third}_{right}")
            three_path_variables[(left, third, right)] = path
            model.AddAllowedAssignments(
                [edge_variables[first_edge], edge_variables[second_edge], path],
                quotient_composition_tuples(
                    first_edge, left, third, second_edge, right
                ),
            )
            holonomy = model.NewIntVar(
                0, 5, f"linear_holonomy_{left}_{right}_{third}"
            )
            holonomy_variables[(central_edge, third)] = holonomy
            model.AddAllowedAssignments(
                [edge_variables[central_edge], path, holonomy],
                quotient_holonomy_tuples(),
            )
            based_holonomies.append(holonomy)
        model.AddAllowedAssignments(
            [edge_variables[central_edge], *based_holonomies],
            quotient_local_tuples(),
        )

    intact_intersecting_pairs = [
        (left, right)
        for left, right in combinations(sorted(intact), 2)
        if not set(FIBERS[left]).isdisjoint(FIBERS[right])
    ]
    six_path_variables = {}
    position_histogram = {"00": 0, "01": 0, "10": 0, "11": 0}
    for left, right in intact_intersecting_pairs:
        shared = next(iter(set(FIBERS[left]) & set(FIBERS[right])))
        position_left = 0 if FIBERS[left][0] == shared else 1
        position_right = 0 if FIBERS[right][0] == shared else 1
        position_histogram[f"{position_left}{position_right}"] += 1
        paths = []
        for third in range(21):
            if not (
                set(FIBERS[third]).isdisjoint(FIBERS[left])
                and set(FIBERS[third]).isdisjoint(FIBERS[right])
            ):
                continue
            first_edge = tuple(sorted((left, third)))
            second_edge = tuple(sorted((right, third)))
            path = model.NewIntVar(
                0, 5, f"linear_six_path_{left}_{third}_{right}"
            )
            six_path_variables[(left, third, right)] = path
            model.AddAllowedAssignments(
                [edge_variables[first_edge], edge_variables[second_edge], path],
                quotient_composition_tuples(
                    first_edge, left, third, second_edge, right
                ),
            )
            paths.append(path)
        assert len(paths) == 6
        model.AddAllowedAssignments(
            paths,
            quotient_six_path_tuples(position_left, position_right),
        )

    metadata = {
        "profile_index": profile_index,
        "profile": profile,
        "intact_fibers": len(intact),
        "edge_variables": len(edge_variables),
        "intact_disjoint_edges": len(intact_disjoint_edges),
        "intact_intersecting_pairs": len(intact_intersecting_pairs),
        "holonomy_variables": len(holonomy_variables),
        "three_path_variables": len(three_path_variables),
        "six_path_variables": len(six_path_variables),
        "position_histogram": position_histogram,
    }
    context = {
        "intact": intact,
        "edge_variables": edge_variables,
        "profile": profile,
    }
    return model, context, metadata


def verify_quotient(context, solver):
    intact = context["intact"]
    values = {
        edge: solver.Value(variable)
        for edge, variable in context["edge_variables"].items()
    }

    def oriented(edge, source, target):
        return oriented_linear(edge, source, target, values[edge])

    for central_edge in KG_EDGES:
        left, right = central_edge
        if left not in intact or right not in intact:
            continue
        holonomies = []
        for third in range(21):
            if third in central_edge:
                continue
            if not (
                set(FIBERS[third]).isdisjoint(FIBERS[left])
                and set(FIBERS[third]).isdisjoint(FIBERS[right])
            ):
                continue
            first_edge = tuple(sorted((left, third)))
            second_edge = tuple(sorted((right, third)))
            path = LINEAR_COMPOSE[
                oriented(second_edge, third, right)
            ][oriented(first_edge, left, third)]
            holonomies.append(
                LINEAR_COMPOSE[LINEAR_INVERSES[values[central_edge]]][path]
            )
        assert (values[central_edge], *holonomies) in quotient_local_tuples()

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
                LINEAR_COMPOSE[
                    oriented(second_edge, third, right)
                ][oriented(first_edge, left, third)]
            )
        assert tuple(paths) in quotient_six_path_tuples(
            position_left, position_right
        )

    return {
        "profile": context["profile"],
        "linear_edge_permutations": {
            f"{edge[0]}-{edge[1]}": value for edge, value in sorted(values.items())
        },
    }


def solve_profile(profile_index: int, time_limit: float, workers: int, witness=None):
    started = time.time()
    model, context, metadata = build_model(profile_index)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = 0
    status = solver.Solve(model)
    result = {
        **metadata,
        "status": solver.StatusName(status),
        "seconds": time.time() - started,
        "branches": solver.NumBranches(),
        "conflicts": solver.NumConflicts(),
        "qualification": "SAT is a necessary quotient witness; INFEASIBLE needs a checked certificate",
    }
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        quotient = verify_quotient(context, solver)
        result["verified_quotient"] = True
        if witness:
            Path(witness).write_text(json.dumps(quotient, indent=2, sort_keys=True) + "\n")
            result["witness"] = witness
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", type=int)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--time-limit", type=float, default=300)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--out")
    parser.add_argument("--audit-tables", action="store_true")
    args = parser.parse_args()
    if args.audit_tables:
        print(json.dumps(quotient_table_audit(), indent=2, sort_keys=True))
        return
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
