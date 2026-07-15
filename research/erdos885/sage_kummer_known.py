#!/usr/bin/env python3
"""Classify the 32 compatible four-factor Kummer tuples against the known
projective rational points of the best four-row curve.

This reruns the rigorous local sieve, records the complete reduction signature
of every surviving global tuple, and compares it with the signatures of:
  * all 16 sign choices above each of the three known affine columns; and
  * all eight projective points at infinity.
If the reduction signatures are injective on the survivor set, a signature
match identifies the actual global mod-2 tuple, not merely a local lookalike.
"""
from __future__ import annotations

import itertools
import json
import math
import os
import sys
from pathlib import Path

from sage.all import EllipticCurve, GF, Integer

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sage_kummer_compat as kc

KNOWN_T = [-5585184, 0, 35994816]


def exact_known_points():
    pts = []
    for t in KNOWN_T:
        roots = []
        for r in kc.ROWS:
            n = Integer(t) + r*r
            if n < 0 or not n.is_square():
                raise RuntimeError(f"bad known column t={t}, row={r}")
            roots.append(Integer(n.sqrt()))
        for signs in itertools.product([1, -1], repeat=4):
            pts.append({
                "id": f"t={t};signs={''.join('+' if s == 1 else '-' for s in signs)}",
                "kind": "affine",
                "t": int(t),
                "roots": [int(signs[i] * roots[i]) for i in range(4)],
            })
    for tail in itertools.product([1, -1], repeat=3):
        signs = (1,) + tail
        pts.append({
            "id": f"infinity;signs={''.join('+' if s == 1 else '-' for s in signs)}",
            "kind": "infinity",
            "signs": list(signs),
        })
    return pts


def build_local_context(prime, factors, class_points):
    F = GF(prime)
    local_curves = []
    glabs = []
    for (inds, E0, p, q), reps in zip(factors, class_points):
        Ep = EllipticCurve(F, [F(x) for x in E0.a_invariants()])
        labels, _, _ = kc.quotient_labels(Ep)
        glabs.append([labels[kc.reduce_projective_point(P, Ep, prime)] for P in reps])
        local_curves.append((inds, Ep, F(p), F(q), labels))
    return F, local_curves, glabs


def point_local_tuple(point, F, local_curves):
    labs = []
    if point["kind"] == "affine":
        us = [F(x) for x in point["roots"]]
        for inds, Ep, pp, qq, labels in local_curves:
            ia, ib, ic = inds
            u, v, w = us[ia], us[ib], us[ic]
            X = F(4) * (v-u) * (w-u)
            Y = F(8) * (v-u) * (w-u) * (v+w)
            labs.append(labels[Ep(X, Y)])
    else:
        signs = point["signs"]
        for inds, Ep, pp, qq, labels in local_curves:
            ia, ib, ic = inds
            Q = kc.infinity_image(Ep, pp, qq, signs[ia], signs[ib], signs[ic])
            labs.append(labels[Q])
    return tuple(labs)


def main():
    factors = []
    class_points = []
    factor_report = []
    for inds in kc.TRIPLES:
        E0, p, q = kc.input_curve(inds)
        gens, rank = kc.certified_basis_on_input(E0)
        basis, reps = kc.global_classes(E0, p, gens)
        factors.append((inds, E0, p, q))
        class_points.append(reps)
        factor_report.append({"indices": list(inds), "rank": rank, "classes": len(reps)})

    sizes = [len(x) for x in class_points]
    survivors = None
    survivor_signatures = {}
    known_points = exact_known_points()
    known_signatures = {P["id"]: [] for P in known_points}
    used_primes = []

    for prime in kc.PRIMES:
        if any(Integer(E0.discriminant()) % prime == 0 for _, E0, _, _ in factors):
            continue
        if len({int((r*r) % prime) for r in kc.ROWS}) < 4:
            continue

        local = kc.local_data(prime, factors, class_points)
        allowed = local["local_image"]
        F, local_curves, glabs = build_local_context(prime, factors, class_points)
        used_primes.append(prime)

        if survivors is None:
            survivors = []
            for vals in itertools.product(*[range(s) for s in sizes]):
                lt = tuple(glabs[j][vals[j]] for j in range(4))
                if lt in allowed:
                    survivors.append(kc.encode(vals, sizes))
        else:
            survivors = [
                code for code in survivors
                if tuple(glabs[j][kc.decode(code, sizes)[j]] for j in range(4)) in allowed
            ]

        # Extend stable signatures for all current/future final survivors by storing
        # the factor label arrays for this prime.
        survivor_signatures[prime] = glabs
        for P in known_points:
            known_signatures[P["id"]].append(point_local_tuple(P, F, local_curves))

    if survivors is None:
        raise RuntimeError("no usable primes")

    final_sig_to_codes = {}
    code_to_sig = {}
    for code in survivors:
        vals = kc.decode(code, sizes)
        sig = tuple(
            tuple(survivor_signatures[p][j][vals[j]] for j in range(4))
            for p in used_primes
        )
        code_to_sig[code] = sig
        final_sig_to_codes.setdefault(sig, []).append(code)

    known_sig_to_points = {}
    for P in known_points:
        sig = tuple(known_signatures[P["id"]])
        known_sig_to_points.setdefault(sig, []).append(P["id"])

    matched = []
    unmatched = []
    for code in survivors:
        sig = code_to_sig[code]
        entry = {
            "indices": kc.decode(code, sizes),
            "known_points": known_sig_to_points.get(sig, []),
            "signature_collision_count_among_survivors": len(final_sig_to_codes[sig]),
        }
        if entry["known_points"]:
            matched.append(entry)
        else:
            unmatched.append(entry)

    out = {
        "rows": [int(x) for x in kc.ROWS],
        "used_primes": used_primes,
        "factor_report": factor_report,
        "known_projective_point_count": len(known_points),
        "distinct_known_reduction_signatures": len(known_sig_to_points),
        "survivor_count": len(survivors),
        "distinct_survivor_reduction_signatures": len(final_sig_to_codes),
        "reduction_signature_injective_on_survivors": len(final_sig_to_codes) == len(survivors),
        "matched_survivor_count": len(matched),
        "unmatched_survivor_count": len(unmatched),
        "matched_survivors": matched,
        "unmatched_survivors": unmatched,
        "interpretation": "When signatures are injective on survivors, every matched survivor is exactly the same global four-factor mod-2 tuple as a known projective rational point.",
    }
    Path("results").mkdir(exist_ok=True)
    Path("results/kummer_known.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "survivors": len(survivors),
        "distinct_survivor_signatures": len(final_sig_to_codes),
        "matched": len(matched),
        "unmatched": len(unmatched),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
