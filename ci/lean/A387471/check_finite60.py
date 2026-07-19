#!/usr/bin/env python3
"""Independent exact-integer cross-check for A387471Finite60.lean."""

from itertools import permutations, product

ZERO16 = (0,) * 16


def step(v: tuple[int, ...]) -> tuple[int, ...]:
    assert len(v) == 16
    return (
        -v[15], v[0], v[1] - v[15], v[2], v[3], v[4],
        v[5] + v[15], v[6], v[7] + v[15], v[8],
        v[9] + v[15], v[10], v[11], v[12], v[13] - v[15], v[14],
    )


def power_vectors() -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []
    v = (1,) + (0,) * 15
    for _ in range(60):
        out.append(v)
        v = step(v)
    return out


POW = power_vectors()


def sine_vector(a: int) -> tuple[int, ...]:
    return tuple(x - y for x, y in zip(POW[a % 60], POW[(-a) % 60]))


def relation_vector(a: int, b: int, c: int) -> tuple[int, ...]:
    return tuple(x + y + z for x, y, z in zip(sine_vector(a), sine_vector(b), sine_vector(c)))


def admissible(a: int, b: int, c: int) -> bool:
    return abs(a + b) < 10 and abs(a + c) < 10 and abs(b + c) < 10


def ordinary(a: int, b: int, c: int) -> bool:
    return (a == 0 and b == -c) or (b == 0 and a == -c) or (c == 0 and a == -b)


EXCEPTIONAL = set(permutations((-5, -3, 9))) | set(permutations((-9, 3, 5)))


def classified(a: int, b: int, c: int) -> bool:
    return ordinary(a, b, c) or (a, b, c) in EXCEPTIONAL


def main() -> None:
    solutions: list[tuple[int, int, int]] = []
    bad: list[tuple[int, int, int]] = []
    for a, b, c in product(range(-14, 15), repeat=3):
        if admissible(a, b, c) and relation_vector(a, b, c) == ZERO16:
            solutions.append((a, b, c))
            if not classified(a, b, c):
                bad.append((a, b, c))
    ordinary_count = sum(ordinary(*triple) for triple in solutions)
    exceptional = {triple for triple in solutions if triple in EXCEPTIONAL}
    assert not bad, f"unclassified vanishing triples: {bad}"
    assert len(solutions) == 67, len(solutions)
    assert ordinary_count == 55, ordinary_count
    assert exceptional == EXCEPTIONAL, (exceptional, EXCEPTIONAL)
    assert len(exceptional) == 12
    print("checked triples: 24389")
    print("admissible vanishing triples: 67")
    print("ordinary triples: 55")
    print("exceptional triples: 12")
    print("unclassified triples: 0")


if __name__ == "__main__":
    main()
