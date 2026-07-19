#!/usr/bin/env python3
from __future__ import annotations

import itertools

from generate_cnf import CnfBuilder, add_at_least, build_instance


def clause_value(clause: tuple[int, ...], assignment: dict[int, bool]) -> bool:
    return any((lit > 0) == assignment[abs(lit)] for lit in clause)


def exists_aux(builder: CnfBuilder, primary_assignment: dict[int, bool], primary_count: int) -> bool:
    aux = list(range(primary_count + 1, builder.variable_count + 1))
    for bits in itertools.product((False, True), repeat=len(aux)):
        assignment = dict(primary_assignment)
        assignment.update(dict(zip(aux, bits)))
        if all(clause_value(clause, assignment) for clause in builder.clauses):
            return True
    return False


def test_counter() -> None:
    for n in range(1, 6):
        for k in range(0, n + 2):
            builder = CnfBuilder(n)
            add_at_least(builder, list(range(1, n + 1)), k)
            for bits in itertools.product((False, True), repeat=n):
                assignment = {i + 1: bits[i] for i in range(n)}
                expected = sum(bits) >= k
                assert exists_aux(builder, assignment, n) == expected, (n, k, bits)


def test_instances() -> None:
    for n in range(2, 6):
        for parity in (0, 1):
            point_count = len([(x, y) for x in range(n) for y in range(n) if (x + y) % 2 == parity])
            for minimum in range(0, min(4, point_count) + 1):
                points, lines, builder, metadata = build_instance(n, parity, minimum)
                assert metadata["point_count"] == len(points)
                assert metadata["maximal_line_count"] == len(lines)
                assert metadata["clause_count"] == len(builder.clauses)


if __name__ == "__main__":
    test_counter()
    test_instances()
    print("encoding tests passed")
