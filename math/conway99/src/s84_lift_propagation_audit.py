#!/usr/bin/env python3
"""Exact propagation audit for the final ``s = 84`` lift.

The constraints are the complete disjoint-fiber and intersecting-fiber block
equations. Every pruning step is generalized arc consistency on a finite
relation or an exact small integer-sum relation; a reported empty domain is
therefore a checkable contradiction, not a heuristic solver status.
"""
from __future__ import annotations

import json
from collections import Counter, deque
from itertools import combinations, permutations, product

from s84_connection_data import build as build_connection
from s84_connection_data import edge_elements, s3_permutation

POINTS = range(4)
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
    lengths = []
    for i in range(4):
        if i in seen:
            continue
        j = i
        length = 0
        while j not in seen:
            seen.add(j)
            length += 1
            j = p[j]
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))


def c4_adjacent(axis, x, y):
    return int(x != y and (x ^ y) != axis)


class TableConstraint:
    __slots__ = ("scope", "tuples")

    def __init__(self, scope, tuples):
        self.scope = tuple(scope)
        self.tuples = tuple(tuples)

    def revise(self, domains):
        support = [0] * len(self.scope)
        found = False
        for values in self.tuples:
            if all(
                (domains[variable] >> values[i]) & 1
                for i, variable in enumerate(self.scope)
            ):
                found = True
                for i, value in enumerate(values):
                    support[i] |= 1 << value
        if not found:
            return None
        changed = []
        for i, variable in enumerate(self.scope):
            new_domain = domains[variable] & support[i]
            if not new_domain:
                return None
            if new_domain != domains[variable]:
                domains[variable] = new_domain
                changed.append(variable)
        return changed


class UnarySumConstraint:
    __slots__ = ("scope", "values", "target")

    def __init__(self, scope, values, target):
        self.scope = tuple(scope)
        self.values = tuple(tuple(x) for x in values)
        self.target = target

    @staticmethod
    def sums(items):
        possible = {0}
        for values in items:
            possible = {left + right for left in possible for right in values}
        return possible

    def revise(self, domains):
        possible_values = []
        for variable, values in zip(self.scope, self.values):
            available = {
                values[i]
                for i in range(len(values))
                if (domains[variable] >> i) & 1
            }
            if not available:
                return None
            possible_values.append(available)
        if self.target not in self.sums(possible_values):
            return None

        changed = []
        for i, (variable, values) in enumerate(zip(self.scope, self.values)):
            other_sums = self.sums(possible_values[:i] + possible_values[i + 1 :])
            supported = 0
            for value, contribution in enumerate(values):
                if (
                    (domains[variable] >> value) & 1
                    and self.target - contribution in other_sums
                ):
                    supported |= 1 << value
            new_domain = domains[variable] & supported
            if not new_domain:
                return None
            if new_domain != domains[variable]:
                domains[variable] = new_domain
                changed.append(variable)
        return changed


class PairSumConstraint:
    __slots__ = ("a", "b", "joint", "scope", "values", "target", "all_scope")

    def __init__(self, a, b, joint, scope, values, target):
        self.a = a
        self.b = b
        self.joint = joint
        self.scope = tuple(scope)
        self.values = tuple(tuple(x) for x in values)
        self.target = target
        self.all_scope = (a, b) + self.scope

    @staticmethod
    def sums(items):
        possible = {0}
        for values in items:
            possible = {left + right for left in possible for right in values}
        return possible

    def revise(self, domains):
        possible_values = []
        for variable, values in zip(self.scope, self.values):
            available = {
                values[i]
                for i in range(len(values))
                if (domains[variable] >> i) & 1
            }
            if not available:
                return None
            possible_values.append(available)
        path_sums = self.sums(possible_values)

        valid_pairs = []
        for left, row in enumerate(self.joint):
            if not ((domains[self.a] >> left) & 1):
                continue
            for right, contribution in enumerate(row):
                if (
                    (domains[self.b] >> right) & 1
                    and self.target - contribution in path_sums
                ):
                    valid_pairs.append((left, right, contribution))
        if not valid_pairs:
            return None

        changed = []
        support_a = 0
        support_b = 0
        for left, right, _ in valid_pairs:
            support_a |= 1 << left
            support_b |= 1 << right
        for variable, support in ((self.a, support_a), (self.b, support_b)):
            new_domain = domains[variable] & support
            if not new_domain:
                return None
            if new_domain != domains[variable]:
                domains[variable] = new_domain
                changed.append(variable)

        pair_contributions = {value for _, _, value in valid_pairs}
        for i, (variable, values) in enumerate(zip(self.scope, self.values)):
            other_sums = self.sums(possible_values[:i] + possible_values[i + 1 :])
            supported = 0
            for value, contribution in enumerate(values):
                if not ((domains[variable] >> value) & 1):
                    continue
                if any(
                    self.target - contribution - pair_value in other_sums
                    for pair_value in pair_contributions
                ):
                    supported |= 1 << value
            new_domain = domains[variable] & supported
            if not new_domain:
                return None
            if new_domain != domains[variable]:
                domains[variable] = new_domain
                changed.append(variable)
        return changed


def build_model(parameter):
    data = build_connection()
    support = data["support"]
    class_bits = data["class_bits"]
    fibers = data["fibers"]
    edges = data["edges"]
    edge_index = data["edge_index"]
    triangles = data["triangles"]
    edge_triangles = data["edge_triangles"]
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

    frame_variables = list(range(21))
    translation_variables = [21 + edge for edge in range(105)]
    next_variable = 126

    holonomy_variables = {}
    for triangle_index, triangle in enumerate(triangles):
        for base in triangle:
            holonomy_variables[(triangle_index, base)] = next_variable
            next_variable += 1

    intersecting_pairs = [
        (u, v)
        for u, v in combinations(range(21), 2)
        if not set(fibers[u]).isdisjoint(fibers[v])
    ]
    path_variables = {}
    for u, v in intersecting_pairs:
        for middle in range(21):
            if (
                set(fibers[middle]).isdisjoint(fibers[u])
                and set(fibers[middle]).isdisjoint(fibers[v])
            ):
                path_variables[(u, v, middle)] = next_variable
                next_variable += 1

    domains = [0] * next_variable
    for variable in frame_variables:
        domains[variable] = (1 << 6) - 1
    for variable in translation_variables:
        domains[variable] = 15

    zero_translations = [0] * 105
    holonomy_linears = {}
    for key, variable in holonomy_variables.items():
        triangle_index, base = key
        linear, _ = holonomy(triangle_index, base, zero_translations)
        holonomy_linears[key] = linear
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
        domains[variable] = sum(1 << translation for translation in allowed)

    for variable in path_variables.values():
        domains[variable] = 15

    constraints = []
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
            constraints.append(
                TableConstraint(
                    [translation_variables[edge] for edge in edge_ids]
                    + [holonomy_variables[(triangle_index, base)]],
                    allowed,
                )
            )

    path_linears = {}
    for u, v in intersecting_pairs:
        for middle in range(21):
            key = (u, v, middle)
            if key not in path_variables:
                continue
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
                allowed.append((first, second, translation))
                path_linears[key] = linear
            constraints.append(
                TableConstraint(
                    (
                        translation_variables[edge_one],
                        translation_variables[edge_two],
                        path_variables[key],
                    ),
                    allowed,
                )
            )

    for edge, (u, v) in enumerate(edges):
        linear = oriented_linear(u, v)
        inverse_linear = inverse(linear)
        incident = edge_triangles[edge]
        for x, y in product(range(4), repeat=2):
            scope = [frame_variables[u], frame_variables[v]] + [
                holonomy_variables[(triangle_index, u)]
                for triangle_index in incident
            ]
            values = [
                [c4_adjacent(GL[frame][3], x, y) for frame in range(6)],
                [
                    c4_adjacent(inverse_linear[GL[frame][3]], x, y)
                    for frame in range(6)
                ],
            ]
            for triangle_index in incident:
                holonomy_linear = holonomy_linears[(triangle_index, u)]
                values.append(
                    [
                        int(holonomy_linear[x] ^ translation == y)
                        for translation in range(4)
                    ]
                )
            constraints.append(
                UnarySumConstraint(scope, values, 2 - int(x == y))
            )

    for u, v in intersecting_pairs:
        shared = next(iter(set(fibers[u]) & set(fibers[v])))
        position_u = 0 if fibers[u][0] == shared else 1
        position_v = 0 if fibers[v][0] == shared else 1
        paths = [
            (u, v, middle)
            for middle in range(21)
            if (u, v, middle) in path_variables
        ]
        assert len(paths) == 6
        for x, y in product(range(4), repeat=2):
            joint = []
            for frame_u in range(6):
                row = []
                inverse_u = inverse(GL[frame_u])
                bit_u = (inverse_u[x] >> position_u) & 1
                for frame_v in range(6):
                    inverse_v = inverse(GL[frame_v])
                    bit_v = (inverse_v[y] >> position_v) & 1
                    row.append(int(bit_u == bit_v))
                joint.append(row)
            scope = [path_variables[key] for key in paths]
            values = []
            for key in paths:
                linear = path_linears[key]
                values.append(
                    [
                        int(linear[x] ^ translation == y)
                        for translation in range(4)
                    ]
                )
            constraints.append(
                PairSumConstraint(
                    frame_variables[u],
                    frame_variables[v],
                    joint,
                    scope,
                    values,
                    2,
                )
            )

    incidence = [[] for _ in domains]
    for constraint_index, constraint in enumerate(constraints):
        scope = constraint.scope if hasattr(constraint, "scope") else constraint.all_scope
        for variable in scope:
            incidence[variable].append(constraint_index)

    return domains, constraints, incidence, {
        "parameter": parameter,
        "variables": len(domains),
        "constraints": len(constraints),
        "frames": 21,
        "edge_translations": 105,
        "triangle_holonomies": 315,
        "path_translations": 630,
    }


def propagate(domains, constraints, incidence, initial=None):
    queue = deque(range(len(constraints)) if initial is None else initial)
    queued = set(queue)
    steps = 0
    while queue:
        constraint_index = queue.popleft()
        queued.discard(constraint_index)
        steps += 1
        changed = constraints[constraint_index].revise(domains)
        if changed is None:
            return False, steps
        for variable in changed:
            for neighbor in incidence[variable]:
                if neighbor not in queued:
                    queue.append(neighbor)
                    queued.add(neighbor)
    return True, steps


def audit():
    reports = []
    parameter_one_root = None
    parameter_one_constraints = None
    parameter_one_incidence = None

    for parameter in (0, 1, 2):
        domains, constraints, incidence, metadata = build_model(parameter)
        domains[0] = 1
        consistent, steps = propagate(domains, constraints, incidence)
        reports.append(
            {
                **metadata,
                "root_consistent": consistent,
                "propagation_steps": steps,
            }
        )
        if parameter in (0, 2):
            assert not consistent
        else:
            assert consistent
            parameter_one_root = domains
            parameter_one_constraints = constraints
            parameter_one_incidence = incidence

    assert GL[0][3] == GL[2][3] == 3
    probes = []
    for vertex in range(1, 21):
        surviving = []
        for frame_value in range(6):
            domains = parameter_one_root.copy()
            domains[vertex] = 1 << frame_value
            consistent, steps = propagate(
                domains,
                parameter_one_constraints,
                parameter_one_incidence,
                parameter_one_incidence[vertex],
            )
            probes.append(
                {
                    "vertex": vertex,
                    "frame_value": frame_value,
                    "consistent": consistent,
                    "propagation_steps": steps,
                }
            )
            if consistent:
                surviving.append(frame_value)
        assert surviving == [0, 2]

    return {
        "PASS": True,
        "parameter_reports": reports,
        "frame_probes": len(probes),
        "forbidden_frame_probes_rejected": sum(
            not item["consistent"] and item["frame_value"] in (1, 3, 4, 5)
            for item in probes
        ),
        "allowed_frame_probes_survive": sum(
            item["consistent"] and item["frame_value"] in (0, 2)
            for item in probes
        ),
        "forced_common_axis": 3,
        "consequence": (
            "After fixing one global frame, parameters 0 and 2 contradict the "
            "exact block CSP by propagation. In parameter 1 every remaining "
            "fiber frame is forced into values 0 or 2, both of which preserve "
            "the same C4 axis."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
