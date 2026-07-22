#!/usr/bin/env python3
"""Solve one exhaustive symmetry orbit of the N=6, D=3 mod-2 system.

An integer solution reduces modulo two.  Each perfect-matching monomial gets a
Tseitin variable, while the sum of the fifteen monomials is retained as one
native XOR constraint.  The active monochromatic perfect matchings have eight
orbits under vertex and colour relabelling; these representatives are checked
by brute-force orbit enumeration before solving.
"""

from __future__ import annotations

import argparse
import itertools
import json
import time
from pycryptosat import Solver

N = 6
D = 3


def norm_matching(matching):
    return tuple(sorted(tuple(sorted(edge)) for edge in matching))


def perfect_matchings(vertices):
    vertices = tuple(vertices)
    if not vertices:
        yield ()
        return
    u = vertices[0]
    for k in range(1, len(vertices)):
        v = vertices[k]
        rest = vertices[1:k] + vertices[k + 1 :]
        for matching in perfect_matchings(rest):
            yield norm_matching(((u, v),) + matching)


MATCHINGS = tuple(sorted(set(perfect_matchings(range(N)))))
assert len(MATCHINGS) == 15
MATCHING_INDEX = {m: i for i, m in enumerate(MATCHINGS)}

# Canonical orbit representatives under S_6 x S_3.
EXPECTED_REPS = (
    (0, 0, 0),
    (0, 0, 1),
    (0, 0, 4),
    (0, 1, 2),
    (0, 1, 3),
    (0, 1, 5),
    (0, 4, 8),
    (0, 4, 13),
)


def permute_matching(matching, permutation):
    return norm_matching((permutation[u], permutation[v]) for u, v in matching)


def transform_triple(triple, vertex_perm, colour_perm):
    transformed = [None] * D
    for old_colour, matching_index in enumerate(triple):
        new_colour = colour_perm[old_colour]
        transformed[new_colour] = MATCHING_INDEX[
            permute_matching(MATCHINGS[matching_index], vertex_perm)
        ]
    return tuple(transformed)


def canonical_triple(triple):
    return min(
        transform_triple(triple, vp, cp)
        for vp in itertools.permutations(range(N))
        for cp in itertools.permutations(range(D))
    )


def verify_orbits():
    representatives = sorted(
        {canonical_triple(t) for t in itertools.product(range(len(MATCHINGS)), repeat=D)}
    )
    if tuple(representatives) != EXPECTED_REPS:
        raise RuntimeError(
            f"orbit classification mismatch: {representatives!r} != {EXPECTED_REPS!r}"
        )
    return representatives


def weight_key(u, v, i, j):
    assert u < v
    return u, v, i, j


def solve_orbit(orbit_index: int, time_limit: float, threads: int):
    representatives = verify_orbits()
    triple = representatives[orbit_index]

    solver = Solver(threads=threads, time_limit=time_limit, verbose=1)
    next_var = 1
    weights = {}
    for u in range(N):
        for v in range(u + 1, N):
            for i in range(D):
                for j in range(D):
                    weights[weight_key(u, v, i, j)] = next_var
                    next_var += 1

    # Every monochromatic equation has odd parity, so it contains an active
    # perfect matching.  Fix one active matching for each colour according to
    # the exhaustive S_6 x S_3 orbit representative.
    for colour, matching_index in enumerate(triple):
        for u, v in MATCHINGS[matching_index]:
            solver.add_clause([weights[weight_key(u, v, colour, colour)]])

    equation_terms = []
    for colours in itertools.product(range(D), repeat=N):
        terms = []
        for matching in MATCHINGS:
            factors = [weights[weight_key(u, v, colours[u], colours[v])] for u, v in matching]
            t = next_var
            next_var += 1
            a, b, c = factors
            # t iff a and b and c.
            solver.add_clause([-t, a])
            solver.add_clause([-t, b])
            solver.add_clause([-t, c])
            solver.add_clause([t, -a, -b, -c])
            terms.append(t)
        target = len(set(colours)) == 1
        solver.add_xor_clause(terms, target)
        equation_terms.append((colours, terms, target))

    started = time.time()
    result, model = solver.solve()
    elapsed = time.time() - started
    summary = {
        "orbit_index": orbit_index,
        "active_matching_indices": triple,
        "result": "sat" if result is True else "unsat" if result is False else "unknown",
        "elapsed_seconds": elapsed,
        "variables": next_var - 1,
        "weight_variables": len(weights),
        "equations": len(equation_terms),
        "threads": threads,
    }

    if result is True:
        bad = []
        for equation_index, (colours, terms, target) in enumerate(equation_terms):
            parity = sum(bool(model[t]) for t in terms) % 2
            if parity != target:
                bad.append(equation_index)
        summary["model_verification_failures"] = bad
        if bad:
            raise RuntimeError(f"solver returned an invalid model: {bad[:20]}")
    print(json.dumps(summary, indent=2, sort_keys=True), flush=True)
    return 0 if result is False else 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--orbit", type=int, choices=range(8), required=True)
    parser.add_argument("--time-limit", type=float, default=6800.0)
    parser.add_argument("--threads", type=int, default=4)
    args = parser.parse_args()
    raise SystemExit(solve_orbit(args.orbit, args.time_limit, args.threads))


if __name__ == "__main__":
    main()
