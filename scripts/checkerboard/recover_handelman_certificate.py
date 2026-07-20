#!/usr/bin/env python3
"""Recover the exact generated Handelman Lean source.

The archived payload's gzip trailer is damaged, but the raw DEFLATE body may
still be intact.  Recovery is accepted only when the resulting source matches
the pre-recorded SHA-256 digest and exact line count.
"""

from __future__ import annotations

import base64
import gzip
import hashlib
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
MANIFEST = ROOT / "proofs/lean/Checkerboard/handelman-recovery.txt"
EXPECTED_SHA256 = "258056bf2cded9ea19b5419f4f3a837e6476373d7594b4158b7d54accba0febf"
EXPECTED_LINES = 10589


def raw_gzip_deflate(data: bytes) -> bytes:
    """Inflate a gzip member while ignoring only its 8-byte CRC/size trailer."""
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


def validate(source: bytes, method: str) -> None:
    text = source.decode("utf-8")
    digest = hashlib.sha256(source).hexdigest()
    lines = len(text.splitlines())
    print(f"method={method}")
    print(f"sha256={digest}")
    print(f"lines={lines}")
    if digest != EXPECTED_SHA256:
        raise SystemExit(f"recovered source digest mismatch: {digest}")
    if lines != EXPECTED_LINES:
        raise SystemExit(f"recovered source line-count mismatch: {lines}")
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_bytes(source)
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(
        f"method={method}\nsha256={digest}\nlines={lines}\noutput={OUTPUT}\n",
        encoding="utf-8",
    )


def main() -> None:
    encoded = "".join(path.read_text(encoding="ascii").strip() for path in PARTS)
    packed = base64.b64decode(encoded, validate=False)
    try:
        source = gzip.decompress(packed)
        method = "gzip-verified"
    except (gzip.BadGzipFile, EOFError, zlib.error) as exc:
        print(f"verified gzip failed: {type(exc).__name__}: {exc}")
        source = raw_gzip_deflate(packed)
        method = "raw-deflate-with-trailer-ignored"
    validate(source, method)


if __name__ == "__main__":
    main()
