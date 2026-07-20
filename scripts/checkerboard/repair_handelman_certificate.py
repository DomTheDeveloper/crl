#!/usr/bin/env python3
"""Recover and deterministically repair the generated Handelman Lean module.

The archived gzip member has localized corruption in a repeated, generated
case-dispatch suffix.  The intact raw DEFLATE stream still contains every
coefficient proof, every cell certificate, and the terminal global theorem.
This script applies only the mechanically identifiable textual repairs caused
by that corruption.  The repaired module is not trusted: the Lean kernel must
recheck every coefficient sign, polynomial identity, cell implication, and the
final global obstacle theorem.
"""

from __future__ import annotations

import base64
import hashlib
import re
import struct
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PARTS = [
    ROOT / "math/checkerboard/lp/certificates/dual_handelman_payload_0.txt",
    ROOT / "math/checkerboard/lp/certificates/dual_handelman_payload_1.txt",
    ROOT / "math/checkerboard/lp/certificates/dual_handelman_payload_2.txt",
]
OUTPUT = ROOT / "proofs/lean/Checkerboard/Checkerboard/LP/DualHandelmanData.lean"
MANIFEST = ROOT / "proofs/lean/Checkerboard/handelman-repair.txt"


def inflate_raw_gzip_member(data: bytes) -> bytes:
    if len(data) < 18 or data[:2] != b"\x1f\x8b" or data[2] != 8:
        raise ValueError("not a supported gzip/DEFLATE member")
    flags = data[3]
    pos = 10
    if flags & 0x04:
        if pos + 2 > len(data):
            raise ValueError("truncated gzip extra header")
        xlen = struct.unpack_from("<H", data, pos)[0]
        pos += 2 + xlen
    for bit in (0x08, 0x10):
        if flags & bit:
            end = data.find(b"\x00", pos)
            if end < 0:
                raise ValueError("unterminated gzip string header")
            pos = end + 1
    if flags & 0x02:
        pos += 2
    if pos >= len(data) - 8:
        raise ValueError("empty or truncated DEFLATE body")
    return zlib.decompress(data[pos:-8], wbits=-zlib.MAX_WBITS)


def repair(text: str) -> tuple[str, list[tuple[str, int]]]:
    changes: list[tuple[str, int]] = []

    def literal(old: str, new: str) -> None:
        nonlocal text
        count = text.count(old)
        if count:
            text = text.replace(old, new)
        changes.append((old, count))

    def regex(pattern: str, replacement: str) -> None:
        nonlocal text
        text, count = re.subn(pattern, replacement, text)
        changes.append((pattern, count))

    # Localized identifier damage.
    literal("primalElF", "primalE")
    literal("primalFlF", "primalF")
    literal("dualHandelmanCoef6", "dualHandelmanCoeff46")
    regex(r"dualHandelmanCoe(?=\d)", "dualHandelmanCoeff")

    # Localized parenthesis/argument damage in generated affine identities.
    literal("primalC(v))", "primalC))")
    literal("primalD(v))", "primalD))")
    literal("primalF(v))", "primalF))")
    literal("))v))", ")))")

    # Localized loss of plus signs between generated nonnegative summands.
    literal(")) 1 *", ")) + 1 *")
    literal(")) 2 *", ")) + 2 *")
    literal(")) 0 :=", ")) + 0 :=")
    literal(")) (1 / 2 : ℝ) *", ")) + (1 / 2 : ℝ) *")

    return text, changes


def validate_structure(text: str) -> None:
    coeffs = sorted({int(x) for x in re.findall(r"def dualHandelmanCoeff(\d+)", text)})
    cells = sorted({int(x) for x in re.findall(r"theorem dualCell(\d+)_nonneg", text)})
    if coeffs != list(range(91)):
        raise SystemExit(f"expected coefficients 0..90, found {coeffs}")
    if cells != list(range(24)):
        raise SystemExit(f"expected cell theorems 0..23, found {cells}")
    for name in (
        "dualCell13Triangle0_nonneg",
        "dualCell13Triangle1_nonneg",
        "dualCell13Triangle2_nonneg",
        "dualCell13_nonneg",
        "certifiedDualSlackUV_nonneg",
        "certifiedDualSlackXY_nonneg",
    ):
        if f"theorem {name}" not in text:
            raise SystemExit(f"missing terminal theorem {name}")
    forbidden = (
        "primalElF",
        "primalFlF",
        "dualHandelmanCoef6",
        "primalC(v)",
        "primalD(v)",
        "primalF(v)",
    )
    for token in forbidden:
        if token in text:
            raise SystemExit(f"unrepaired corruption token remains: {token}")
    if re.search(r"dualHandelmanCoe\d", text):
        raise SystemExit("unrepaired coefficient identifier remains")
    for lineno, line in enumerate(text.splitlines(), 1):
        if lineno >= 5290 and "have hid_" in line and line.count("(") != line.count(")"):
            raise SystemExit(f"unbalanced repaired identity at line {lineno}: {line}")


def main() -> None:
    encoded = "".join(path.read_text(encoding="ascii").strip() for path in PARTS)
    packed = base64.b64decode(encoded, validate=False)
    source = inflate_raw_gzip_member(packed)
    original_hash = hashlib.sha256(source).hexdigest()
    original_text = source.decode("utf-8")
    repaired, changes = repair(original_text)
    validate_structure(repaired)

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(repaired, encoding="utf-8")
    repaired_hash = hashlib.sha256(repaired.encode("utf-8")).hexdigest()
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(
        "\n".join(
            [
                f"packed_sha256={hashlib.sha256(packed).hexdigest()}",
                f"inflated_sha256={original_hash}",
                f"inflated_lines={len(original_text.splitlines())}",
                f"repaired_sha256={repaired_hash}",
                f"repaired_lines={len(repaired.splitlines())}",
                f"coefficients={len(set(re.findall(r'def dualHandelmanCoeff(\\d+)', repaired)))}",
                f"cell_theorems={len(set(re.findall(r'theorem dualCell(\\d+)_nonneg', repaired)))}",
            ]
            + [f"repair_count[{old}]={count}" for old, count in changes]
        )
        + "\n",
        encoding="utf-8",
    )
    print(MANIFEST.read_text(encoding="utf-8"), end="")


if __name__ == "__main__":
    main()
