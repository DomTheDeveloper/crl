#!/usr/bin/env python3
"""Exact GF(2) contradiction for the final ``s = 84`` translation lift.

The preceding propagation audit forces every physical fiber frame onto the
same internal C4 axis. The disjoint-fiber equations can then be enumerated
locally and force the based triangle holonomy translations into the central
axis subgroup. Triangle closure is linear over F2. A deterministic 54-row XOR
certificate sums to the impossible equation 0 = 1.
"""
from __future__ import annotations

import hashlib
import json
from collections import Counter
from itertools import permutations, product

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


def extend(pair):
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


def connection():
    data = build()
    elements = edge_elements(data, 1)
    edge_index = data["edge_index"]

    def oriented(u, v, translations):
        edge = edge_index[(min(u, v), max(u, v))]
        linear = extend(elements[edge])
        translation = translations[edge]
        if u < v:
            return linear, translation
        inverse_linear = inverse(linear)
        return inverse_linear, inverse_linear[translation]

    def holonomy(triangle_index, base, translations):
        a, b, c = data["triangles"][triangle_index]
        path = (
            (a, c, b, a)
            if base == a
            else ((b, a, c, b) if base == b else (c, b, a, c))
        )
        return affine_comp(
            oriented(path[2], path[3], translations),
            affine_comp(
                oriented(path[1], path[2], translations),
                oriented(path[0], path[1], translations),
            ),
        )

    return data, elements, holonomy


def local_rule_audit(data, elements, holonomy):
    zero = [0] * 105
    flat_edges = 0
    curved_edges = 0
    allowed_histogram = Counter()

    for edge, (u, v) in enumerate(data["edges"]):
        incident = data["edge_triangles"][edge]
        linear = extend(elements[edge])
        inverse_linear = inverse(linear)
        domains = []
        linears = []

        for triangle_index in incident:
            holonomy_linear, translation = holonomy(triangle_index, u, zero)
            assert translation == 0
            linears.append(holonomy_linear)
            values = []
            curved = (data["support"] >> triangle_index) & 1
            class_bit = data["class_bits"][triangle_index]
            for candidate in range(4):
                kind = cycle_type(
                    tuple(holonomy_linear[x] ^ candidate for x in range(4))
                )
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
                    values.append(candidate)
            domains.append(values)

        allowed = set()
        for frame_u, frame_v in product((0, 2), repeat=2):
            axis_u = GL[frame_u][3]
            axis_v = inverse_linear[GL[frame_v][3]]
            assert axis_u == axis_v == 3
            for translations in product(*domains):
                valid = all(
                    c4_adjacent(axis_u, x, y)
                    + c4_adjacent(axis_v, x, y)
                    + sum(
                        int(holonomy_linear[x] ^ translation == y)
                        for holonomy_linear, translation in zip(
                            linears, translations
                        )
                    )
                    == 2 - int(x == y)
                    for x, y in product(range(4), repeat=2)
                )
                if valid:
                    allowed.add(tuple(translations))

        curved_positions = [
            i
            for i, triangle_index in enumerate(incident)
            if (data["support"] >> triangle_index) & 1
        ]
        if not curved_positions:
            flat_edges += 1
            expected = tuple(
                0 if data["class_bits"][triangle_index] else 3
                for triangle_index in incident
            )
            assert allowed == {expected}
        else:
            curved_edges += 1
            assert len(curved_positions) == 2
            uncurved = next(
                i
                for i, triangle_index in enumerate(incident)
                if not ((data["support"] >> triangle_index) & 1)
            )
            expected = set()
            for first in (0, 3):
                values = [None] * 3
                values[uncurved] = 3
                values[curved_positions[0]] = first
                values[curved_positions[1]] = first ^ 3
                expected.add(tuple(values))
            assert allowed == expected
        allowed_histogram[len(allowed)] += 1

    assert (flat_edges, curved_edges) == (21, 84)
    assert allowed_histogram == Counter({2: 84, 1: 21})
    return {
        "flat_edges": flat_edges,
        "curved_edges": curved_edges,
        "allowed_triple_histogram": dict(sorted(allowed_histogram.items())),
        "flat_rule": (
            "identity translation 0 and both double-transposition translations 3"
        ),
        "curved_rule": (
            "uncurved translation 3; the two curved translations are 0 and 3 "
            "in either order"
        ),
    }


def build_linear_system(data, holonomy):
    forms = {}
    zero = [0] * 105
    for triangle_index, triangle in enumerate(data["triangles"]):
        for base in triangle:
            linear, translation = holonomy(triangle_index, base, zero)
            assert translation == 0
            for output_bit in range(2):
                row = 0
                for edge in range(105):
                    for input_bit in range(2):
                        trial = [0] * 105
                        trial[edge] = 1 << input_bit
                        check_linear, candidate = holonomy(
                            triangle_index, base, trial
                        )
                        assert check_linear == linear
                        if (candidate >> output_bit) & 1:
                            row |= 1 << (2 * edge + input_bit)
                forms[(triangle_index, base, output_bit)] = row

    equations = []
    metadata = []

    def add(row, rhs, description):
        equations.append(row | (rhs << 210))
        metadata.append(description)

    for triangle_index, triangle in enumerate(data["triangles"]):
        curved = (data["support"] >> triangle_index) & 1
        class_bit = data["class_bits"][triangle_index]
        if not curved and class_bit:
            for base in triangle:
                for bit in range(2):
                    add(
                        forms[(triangle_index, base, bit)],
                        0,
                        ("identity", triangle_index, base, bit),
                    )
        elif not curved:
            for base in triangle:
                for bit in range(2):
                    add(
                        forms[(triangle_index, base, bit)],
                        1,
                        ("central_double", triangle_index, base, bit),
                    )
        else:
            for base in triangle:
                add(
                    forms[(triangle_index, base, 0)]
                    ^ forms[(triangle_index, base, 1)],
                    0,
                    ("curved_axis", triangle_index, base),
                )

    for edge, (u, _) in enumerate(data["edges"]):
        curved = [
            triangle_index
            for triangle_index in data["edge_triangles"][edge]
            if (data["support"] >> triangle_index) & 1
        ]
        if len(curved) == 2:
            add(
                forms[(curved[0], u, 0)] ^ forms[(curved[1], u, 0)],
                1,
                ("curved_pair", edge, u, curved[0], curved[1]),
            )
        else:
            assert not curved

    return equations, metadata


def xor_certificate(equations, metadata):
    rows = equations[:]
    provenance = [1 << i for i in range(len(rows))]
    rank = 0
    for column in range(210):
        pivot = next(
            (i for i in range(rank, len(rows)) if (rows[i] >> column) & 1),
            None,
        )
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        provenance[rank], provenance[pivot] = (
            provenance[pivot],
            provenance[rank],
        )
        for i in range(len(rows)):
            if i != rank and ((rows[i] >> column) & 1):
                rows[i] ^= rows[rank]
                provenance[i] ^= provenance[rank]
        rank += 1

    proof = next(
        certificate
        for row, certificate in zip(rows, provenance)
        if row == 1 << 210
    )
    identifiers = [
        i for i in range(len(equations)) if (proof >> i) & 1
    ]
    combined = 0
    for identifier in identifiers:
        combined ^= equations[identifier]
    assert combined == 1 << 210

    descriptions = [metadata[i] for i in identifiers]
    payload = json.dumps(
        {"ids": identifiers, "descriptions": descriptions},
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return {
        "coefficient_rank": rank,
        "augmented_rank": rank + 1,
        "certificate_equations": len(identifiers),
        "certificate_type_counts": dict(
            sorted(Counter(item[0] for item in descriptions).items())
        ),
        "certificate_sha256": hashlib.sha256(payload).hexdigest(),
        "certificate_ids": identifiers,
    }


def audit():
    data, elements, holonomy = connection()
    local_rules = local_rule_audit(data, elements, holonomy)
    equations, metadata = build_linear_system(data, holonomy)
    certificate = xor_certificate(equations, metadata)
    assert len(equations) == 546
    assert certificate["certificate_equations"] == 54
    return {
        "PASS": True,
        "translation_variables_over_F2": 210,
        "linear_equations": len(equations),
        "local_rules": local_rules,
        **certificate,
        "consequence": (
            "The forced-axis parameter-1 lift has no edge-translation assignment."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
