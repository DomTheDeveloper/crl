#!/usr/bin/env python3
"""Check the finite arithmetic layer of the A248380(16) odd-response reduction.

This proves only semigroup arithmetic, coverage, legality, and canonicalization.
The P labels still require independent replay of the large outcome memo.
"""
import csv
import heapq
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent


def apery(gens):
    m = min(gens)
    inf = 10**18
    dist = [inf] * m
    dist[0] = 0
    queue = [(0, 0)]
    while queue:
        value, residue = heapq.heappop(queue)
        if value != dist[residue]:
            continue
        for generator in gens:
            nxt = value + generator
            nxt_residue = nxt % m
            if nxt < dist[nxt_residue]:
                dist[nxt_residue] = nxt
                heapq.heappush(queue, (nxt, nxt_residue))
    return dist


def semigroup_data(gens):
    divisor = 0
    for generator in gens:
        divisor = math.gcd(divisor, generator)
    assert divisor == 1
    dist = apery(gens)
    multiplicity = min(gens)
    frobenius = max(dist) - multiplicity
    gaps = [n for n in range(1, frobenius + 1) if n < dist[n % multiplicity]]
    return frobenius, gaps


def canonical(gens):
    frobenius, gaps = semigroup_data(gens)
    gap_set = set(gaps)
    limit = frobenius + min(gens)
    reachable = [False] * (limit + 1)
    reachable[0] = True
    result = []
    for n in range(2, limit + 1):
        illegal = n > frobenius or n not in gap_set
        if illegal and not reachable[n]:
            result.append(n)
            for start in range(limit + 1):
                if reachable[start]:
                    value = start + n
                    while value <= limit:
                        reachable[value] = True
                        value += n
    return result


frobenius, quotient_gaps = semigroup_data([8, 13])
assert frobenius == 83
assert len(quotient_gaps) == 42
odd_exceptions = sorted(n for n in quotient_gaps if n % 2 == 1 and n != 1)

rows = []
with open(HERE / "odd_witnesses.csv", newline="") as source:
    for row in csv.DictReader(source):
        rows.append(
            (
                int(row["odd_response"]),
                int(row["winning_reply"]),
                [int(x) for x in row["p_child"].split()],
            )
        )

assert odd_exceptions == sorted(n for n, _, _ in rows)
recorded_children = []
for odd_response, winning_reply, expected_child in rows:
    _, root_gaps = semigroup_data([16, 26, odd_response])
    assert winning_reply in root_gaps, (odd_response, winning_reply, "illegal reply")
    child = canonical([16, 26, odd_response, winning_reply])
    assert child == expected_child, (odd_response, child, expected_child)
    recorded_children.append(tuple(child))

file_children = []
for line in open(HERE / "odd_p_positions.txt"):
    values = [int(x) for x in line.split()]
    assert values[-1] == 0
    file_children.append(tuple(values[:-1]))
assert sorted(recorded_children) == sorted(file_children)

print("PASS: <8,13> has Frobenius 83 and exactly 42 gaps")
print("PASS: all 23 exceptional odd gaps are covered exactly once")
print("PASS: every listed response is legal and every child is canonical")
print("BOUNDARY: P-label replay is not performed by this script")
