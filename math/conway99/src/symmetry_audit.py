#!/usr/bin/env python3
"""Exact orbit audit for the seed branches.

Aut(7K2) is the wreath product C2 wr S7. Fix seed label {0,2}. The incidence
equations force a unique selected seed-neighbor q0 containing 0 and a unique
q2 containing 2. This script enumerates all 121 admissible ordered pairs and
quotients by the full setwise stabilizer of {0,2}, including endpoint swaps.
"""
from __future__ import annotations
from itertools import combinations, permutations, product
import json
from model import SEED_BRANCHES

K = 14
SEED = (0, 2)
def mate(i): return i ^ 1
def canon(e): return tuple(sorted(e))
LABELS = set((a, b) for a, b in combinations(range(K), 2) if mate(a) != b)

def stabilizer_maps():
    for edge_perm in permutations(range(7)):
        for flips in product((0, 1), repeat=7):
            g = tuple(2 * edge_perm[x // 2] + ((x % 2) ^ flips[x // 2]) for x in range(K))
            if {g[0], g[2]} == set(SEED):
                yield g

def admissible_states():
    q0s = [e for e in LABELS if 0 in e and 2 not in e]
    q2s = [e for e in LABELS if 2 in e and 0 not in e]
    return sorted((q0, q2) for q0 in q0s for q2 in q2s)

def act(state, g):
    q0, q2 = state
    a = canon(g[x] for x in q0)
    b = canon(g[x] for x in q2)
    if g[0] == 0:
        return a, b
    assert g[0] == 2 and g[2] == 0
    return b, a

def audit():
    maps = list(stabilizer_maps())
    states = admissible_states()
    state_set = set(states)
    assert len(maps) == 2 * 120 * 32 == 7680
    assert len(states) == 121
    unseen = set(states)
    orbits = []
    while unseen:
        seed = min(unseen)
        orbit = {act(seed, g) for g in maps}
        assert orbit <= state_set
        unseen -= orbit
        orbits.append(sorted(orbit))
    orbit_id = {state: i for i, orbit in enumerate(orbits) for state in orbit}
    named = {name: (canon(q0), canon(q2)) for name, (q0, q2) in SEED_BRANCHES.items()}
    named_ids = {name: orbit_id[state] for name, state in named.items()}
    assert len(orbits) == 5
    assert len(set(named_ids.values())) == 5
    return {
        "stabilizer_size": len(maps),
        "admissible_ordered_pairs": len(states),
        "orbit_count": len(orbits),
        "orbit_sizes": sorted(len(o) for o in orbits),
        "named_orbit_ids": named_ids,
        "named_representatives": {n: [list(a), list(b)] for n, (a, b) in named.items()},
        "canonical_representatives": [[list(a), list(b)] for a, b in (o[0] for o in orbits)],
        "old_B1_equivalent_to": "A2",
        "PASS": True,
    }

def main():
    print(json.dumps(audit(), indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
