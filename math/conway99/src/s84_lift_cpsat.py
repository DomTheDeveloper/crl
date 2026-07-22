#!/usr/bin/env python3
"""Exact CP-SAT discovery model for the final ``s = 84`` lift.

A SAT result is reconstructed as the complete 84-vertex reduced graph and
checked directly. An INFEASIBLE result is computational evidence only until a
proof-producing backend independently certifies it.
"""
from __future__ import annotations

import argparse
import json
import time
from itertools import combinations, permutations, product
from pathlib import Path

from ortools.sat.python import cp_model

from s84_connection_data import build, edge_elements, s3_permutation

NZ = (1, 2, 3)
GL = tuple((0, NZ[p[0]], NZ[p[1]], NZ[p[2]]) for p in permutations(range(3)))


def compose(p, q):
    return tuple(p[q[i]] for i in range(4))


def inverse(p):
    out = [0] * 4
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def extend_s3(pair):
    p = s3_permutation(*pair)
    return (0, NZ[p[0]], NZ[p[1]], NZ[p[2]])


def affine_comp(left, right):
    linear_left, translation_left = left
    linear_right, translation_right = right
    return (
        compose(linear_left, linear_right),
        linear_left[translation_right] ^ translation_left,
    )


def cycle_type(p):
    seen = set()
    out = []
    for i in range(4):
        if i in seen:
            continue
        j = i
        length = 0
        while j not in seen:
            seen.add(j)
            length += 1
            j = p[j]
        out.append(length)
    return tuple(sorted(out, reverse=True))


def c4_adjacent(axis, x, y):
    return int(x != y and (x ^ y) != axis)


def build_model(parameter):
    data = build()
    fibers = data["fibers"]
    edges = data["edges"]
    edge_index = data["edge_index"]
    triangles = data["triangles"]
    edge_triangles = data["edge_triangles"]
    support = data["support"]
    class_bits = data["class_bits"]
    elements = edge_elements(data, parameter)

    def oriented_pair(u, v):
        edge = edge_index[(min(u, v), max(u, v))]
        coordinate, parity = elements[edge]
        if u < v:
            return coordinate, parity
        return ((coordinate if parity else -coordinate) % 3, parity)

    def oriented_linear(u, v):
        return extend_s3(oriented_pair(u, v))

    def oriented_affine(u, v, translations):
        edge = edge_index[(min(u, v), max(u, v))]
        linear = extend_s3(elements[edge])
        translation = translations[edge]
        if u < v:
            return linear, translation
        inverse_linear = inverse(linear)
        return inverse_linear, inverse_linear[translation]

    def holonomy(triangle_index, base, translations):
        a, b, c = triangles[triangle_index]
        path = (
            (a, c, b, a)
            if base == a
            else ((b, a, c, b) if base == b else (c, b, a, c))
        )
        return affine_comp(
            oriented_affine(path[2], path[3], translations),
            affine_comp(
                oriented_affine(path[1], path[2], translations),
                oriented_affine(path[0], path[1], translations),
            ),
        )

    model = cp_model.CpModel()
    frames = [model.NewIntVar(0, 5, f"frame_{vertex}") for vertex in range(21)]
    # A simultaneous linear change of coordinates at all fibers is harmless.
    # Running all three quotient parameters makes this normalization exhaustive.
    model.Add(frames[0] == 0)
    translations = [model.NewIntVar(0, 3, f"translation_{edge}") for edge in range(105)]

    zero_translations = [0] * 105
    holonomy_translations = {}
    holonomy_linears = {}
    for triangle_index, triangle in enumerate(triangles):
        for base in triangle:
            linear, _ = holonomy(triangle_index, base, zero_translations)
            holonomy_linears[(triangle_index, base)] = linear
            curved = (support >> triangle_index) & 1
            class_bit = class_bits[triangle_index]
            allowed = []
            for translation in range(4):
                kind = cycle_type(tuple(linear[x] ^ translation for x in range(4)))
                valid = (
                    (
                        not curved
                        and (
                            (class_bit and kind == (1, 1, 1, 1))
                            or (not class_bit and kind == (2, 2))
                        )
                    )
                    or (
                        curved
                        and (
                            (not class_bit and kind == (2, 1, 1))
                            or (class_bit and kind == (4,))
                        )
                    )
                )
                if valid:
                    allowed.append(translation)
            assert allowed
            holonomy_translations[(triangle_index, base)] = model.NewIntVarFromDomain(
                cp_model.Domain.FromValues(allowed),
                f"holonomy_translation_{triangle_index}_{base}",
            )

    # Triangle closure: each based holonomy translation is the exact affine
    # composition of the three edge translations.
    for triangle_index, (a, b, c) in enumerate(triangles):
        edge_ids = (
            edge_index[(a, b)],
            edge_index[(b, c)],
            edge_index[(a, c)],
        )
        for base in (a, b, c):
            allowed = []
            for values in product(range(4), repeat=3):
                trial = [0] * 105
                for edge, value in zip(edge_ids, values):
                    trial[edge] = value
                linear, translation = holonomy(triangle_index, base, trial)
                assert linear == holonomy_linears[(triangle_index, base)]
                allowed.append(values + (translation,))
            model.AddAllowedAssignments(
                [translations[edge] for edge in edge_ids]
                + [holonomy_translations[(triangle_index, base)]],
                allowed,
            )

    # Six-path translations for pairs of intersecting fibers.
    intersecting_pairs = []
    path_translations = {}
    path_linears = {}
    for u, v in combinations(range(21), 2):
        if set(fibers[u]).isdisjoint(fibers[v]):
            continue
        intersecting_pairs.append((u, v))
        for middle in range(21):
            if not (
                set(fibers[middle]).isdisjoint(fibers[u])
                and set(fibers[middle]).isdisjoint(fibers[v])
            ):
                continue
            key = (u, v, middle)
            path_translations[key] = model.NewIntVar(0, 3, f"path_{u}_{v}_{middle}")
            edge_one = edge_index[(min(u, middle), max(u, middle))]
            edge_two = edge_index[(min(middle, v), max(middle, v))]
            allowed = []
            for first, second in product(range(4), repeat=2):
                trial = [0] * 105
                trial[edge_one] = first
                trial[edge_two] = second
                linear, translation = affine_comp(
                    oriented_affine(middle, v, trial),
                    oriented_affine(u, middle, trial),
                )
                path_linears[key] = linear
                allowed.append((first, second, translation))
            model.AddAllowedAssignments(
                [translations[edge_one], translations[edge_two], path_translations[key]],
                allowed,
            )

    def element(index, values, name):
        output = model.NewBoolVar(name)
        model.AddElement(index, values, output)
        return output

    # Exact block equations for disjoint fibers.
    for edge, (u, v) in enumerate(edges):
        linear = oriented_linear(u, v)
        inverse_linear = inverse(linear)
        incident_triangles = edge_triangles[edge]
        for x, y in product(range(4), repeat=2):
            terms = [
                element(
                    frames[u],
                    [c4_adjacent(GL[frame][3], x, y) for frame in range(6)],
                    f"internal_u_{edge}_{x}_{y}",
                ),
                element(
                    frames[v],
                    [c4_adjacent(inverse_linear[GL[frame][3]], x, y) for frame in range(6)],
                    f"internal_v_{edge}_{x}_{y}",
                ),
            ]
            for triangle_index in incident_triangles:
                holonomy_linear = holonomy_linears[(triangle_index, u)]
                terms.append(
                    element(
                        holonomy_translations[(triangle_index, u)],
                        [int(holonomy_linear[x] ^ translation == y) for translation in range(4)],
                        f"holonomy_term_{edge}_{triangle_index}_{x}_{y}",
                    )
                )
            model.Add(sum(terms) == 2 - int(x == y))

    # Exact block equations for intersecting fibers.
    for pair_index, (u, v) in enumerate(intersecting_pairs):
        shared = next(iter(set(fibers[u]) & set(fibers[v])))
        position_u = 0 if fibers[u][0] == shared else 1
        position_v = 0 if fibers[v][0] == shared else 1
        paths = [key for key in path_translations if key[:2] == (u, v)]
        assert len(paths) == 6
        for x, y in product(range(4), repeat=2):
            same_sign = model.NewBoolVar(f"same_sign_{pair_index}_{x}_{y}")
            allowed = []
            for frame_u, frame_v in product(range(6), repeat=2):
                bit_u = (inverse(GL[frame_u])[x] >> position_u) & 1
                bit_v = (inverse(GL[frame_v])[y] >> position_v) & 1
                allowed.append((frame_u, frame_v, int(bit_u == bit_v)))
            model.AddAllowedAssignments([frames[u], frames[v], same_sign], allowed)

            terms = [same_sign]
            for key in paths:
                linear = path_linears[key]
                terms.append(
                    element(
                        path_translations[key],
                        [int(linear[x] ^ translation == y) for translation in range(4)],
                        f"path_term_{pair_index}_{key[2]}_{x}_{y}",
                    )
                )
            model.Add(sum(terms) == 2)

    context = {
        "data": data,
        "elements": elements,
        "frames": frames,
        "translations": translations,
        "parameter": parameter,
    }
    stats = {
        "parameter": parameter,
        "frame_variables": len(frames),
        "edge_translation_variables": len(translations),
        "triangle_holonomy_variables": len(holonomy_translations),
        "six_path_variables": len(path_translations),
        "intersecting_fiber_pairs": len(intersecting_pairs),
    }
    return model, context, stats


def verify_solution(context, solver):
    data = context["data"]
    fibers = data["fibers"]
    edges = data["edges"]
    elements = context["elements"]
    frames = [solver.Value(variable) for variable in context["frames"]]
    translations = [solver.Value(variable) for variable in context["translations"]]

    def linear_map(edge):
        permutation = s3_permutation(*elements[edge])
        return (0, NZ[permutation[0]], NZ[permutation[1]], NZ[permutation[2]])

    adjacency = [set() for _ in range(84)]
    for fiber in range(21):
        axis = GL[frames[fiber]][3]
        for x, y in combinations(range(4), 2):
            if c4_adjacent(axis, x, y):
                adjacency[4 * fiber + x].add(4 * fiber + y)
                adjacency[4 * fiber + y].add(4 * fiber + x)

    for edge, (u, v) in enumerate(edges):
        linear = linear_map(edge)
        translation = translations[edge]
        for x in range(4):
            y = linear[x] ^ translation
            adjacency[4 * u + x].add(4 * v + y)
            adjacency[4 * v + y].add(4 * u + x)

    assert all(len(neighbors) == 12 for neighbors in adjacency)

    labels = []
    for fiber, (a, b) in enumerate(fibers):
        inverse_frame = inverse(GL[frames[fiber]])
        for x in range(4):
            physical = inverse_frame[x]
            labels.append(
                (
                    2 * a + (physical & 1),
                    2 * b + ((physical >> 1) & 1),
                )
            )

    for u, v in combinations(range(84), 2):
        common = len(adjacency[u] & adjacency[v])
        edge = int(v in adjacency[u])
        intersection = len(set(labels[u]) & set(labels[v]))
        assert common + edge == 2 - intersection, (
            u,
            v,
            common,
            edge,
            intersection,
        )

    reduced_edges = [
        [u, v]
        for u in range(84)
        for v in sorted(adjacency[u])
        if u < v
    ]
    return {
        "parameter": context["parameter"],
        "frames": frames,
        "translations": translations,
        "reduced_edges": reduced_edges,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--parameter", type=int, choices=(0, 1, 2), required=True)
    parser.add_argument("--time-limit", type=float, default=1200)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--out")
    args = parser.parse_args()

    started = time.time()
    model, context, stats = build_model(args.parameter)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time_limit
    solver.parameters.num_search_workers = args.workers
    solver.parameters.log_search_progress = True
    status = solver.Solve(model)
    status_name = solver.StatusName(status)
    result = {
        **stats,
        "status": status_name,
        "seconds": time.time() - started,
        "branches": solver.NumBranches(),
        "conflicts": solver.NumConflicts(),
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        witness = verify_solution(context, solver)
        result["verified_witness"] = True
        if args.out:
            Path(args.out).write_text(
                json.dumps(witness, indent=2, sort_keys=True) + "\n"
            )
            result["witness"] = args.out

    print("RESULT_JSON " + json.dumps(result, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
