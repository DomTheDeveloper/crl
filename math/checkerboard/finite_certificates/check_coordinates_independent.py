#!/usr/bin/env python3
"""Independent geometric checker for stored construction certificates.

Unlike ``check_model.py``, this checker does not enumerate point triples.
It constructs every exact integer line determined by a selected pair and
rejects the certificate if a third selected point has the same normalized
line key.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


def line_key(p: tuple[int, int], q: tuple[int, int]) -> tuple[int, int, int]:
    x1, y1 = p
    x2, y2 = q
    dx, dy = x2 - x1, y2 - y1
    divisor = math.gcd(abs(dx), abs(dy))
    if divisor == 0:
        raise ValueError("duplicate points")
    a, b = dy // divisor, -dx // divisor
    if a < 0 or (a == 0 and b < 0):
        a, b = -a, -b
    return a, b, a * x1 + b * y1


def check(path: Path) -> dict[str, int | str]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    n = int(payload["n"])
    parity = int(payload["parity"])
    expected_size = int(payload["size"])
    selected = [tuple(map(int, point)) for point in payload["points"]]

    assert payload["format"] == "checkerboard-ntil-construction-v1"
    assert parity in (0, 1)
    assert len(selected) == expected_size
    assert len(set(selected)) == expected_size
    assert all(0 <= x < n and 0 <= y < n for x, y in selected)
    assert all((x + y) % 2 == parity for x, y in selected)

    first_pair: dict[tuple[int, int, int], tuple[int, int]] = {}
    for left in range(expected_size):
        for right in range(left + 1, expected_size):
            key = line_key(selected[left], selected[right])
            previous = first_pair.get(key)
            if previous is None:
                first_pair[key] = (left, right)
                continue
            used = {previous[0], previous[1], left, right}
            if len(used) >= 3:
                indices = sorted(used)[:3]
                bad = [selected[index] for index in indices]
                raise AssertionError(f"three selected points share line {key}: {bad}")

    return {
        "file": path.name,
        "n": n,
        "parity": parity,
        "size": expected_size,
        "pair_count": expected_size * (expected_size - 1) // 2,
        "status": "PASS",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificates", type=Path, nargs="+")
    args = parser.parse_args()
    for certificate in args.certificates:
        result = check(certificate)
        print(" ".join(f"{key}={value}" for key, value in result.items()))


if __name__ == "__main__":
    main()
