#!/usr/bin/env python3
"""Compute a rigorous compatible Kummer-image upper bound for the best
four-row diagonal genus-5 curve.

We use the four explicit triple quotient maps

    X = 4(v-u)(w-u),  Y = 8(v-u)(w-u)(v+w)

onto E: Y^2 = X(X+4p)(X+4q).  Each factor's full group
E(Q)/2E(Q) is enumerated from a certified Mordell-Weil basis and the two
independent rational 2-torsion points.  At good primes we enumerate every
point of the projective diagonal curve, including its eight points at
infinity, and retain only global tuples whose reductions occur locally.

Omitting the fifth (quartic) elliptic quotient makes this an upper bound,
so every deletion is rigorous.
"""
from __future__ import annotations

import itertools
import json
import math
import time
from pathlib import Path

from sage.all import EllipticCurve, GF, Integer, QQ, ZZ, proof

ROWS = [Integer(x) for x in [2578, 5553, 5922, 3222]]
TRIPLES = list(itertools.combinations(range(4), 3))
PRIMES = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]


def input_curve(inds):
    a, b, c = [ROWS[i] for i in inds]
    p = b*b - a*a
    q = c*c - a*a
    E = EllipticCurve(QQ, [0, 4*(p+q), 0, 16*p*q, 0])
    return E, p, q


def certified_basis_on_input(E0):
    E = E0.global_minimal_model()
    proof.all(True)
    rank = int(E.rank(proof=True))
    proof.all(False)
    gens = E.gens(proof=False)
    certain = bool(E.gens_certain())
    proof.all(True)
    if len(gens) != rank or not certain:
        raise RuntimeError(f"uncertain basis: rank={rank}, gens={len(gens)}, certain={certain}")
    try:
        iso = E.isomorphism_to(E0)
    except Exception:
        iso = E.isomorphisms(E0)[0]
    return [iso(P) for P in gens], rank


def global_classes(E0, p, free_gens):
    # Two independent rational 2-torsion points on the input model.
    basis = list(free_gens) + [E0(0, 0), E0(-4*p, 0)]
    out = []
    for mask in range(1 << len(basis)):
        P = E0(0)
        for j, G in enumerate(basis):
            if (mask >> j) & 1:
                P += G
        out.append(P)
    return basis, out


def reduce_q_mod_p(x, p, F):
    x = QQ(x)
    if x == 0:
        return F(0)
    den = Integer(x.denominator())
    num = Integer(x.numerator())
    return F(num % p) / F(den % p)


def reduce_projective_point(P, Ep, p):
    if P.is_zero():
        return Ep(0)
    coords = [QQ(P[i]) for i in range(3)]
    vals = [x.valuation(p) if x != 0 else math.inf for x in coords]
    mv = min(vals)
    scale = QQ(p) ** (-Integer(mv))
    scaled = [x * scale for x in coords]
    F = Ep.base_field()
    red = [reduce_q_mod_p(x, p, F) for x in scaled]
    return Ep(red)


def quotient_labels(Ep):
    pts = list(Ep)
    H = {2*P for P in pts}
    labels = {}
    next_label = 0
    for P in pts:
        if P in labels:
            continue
        for Q in H:
            labels[P + Q] = next_label
        next_label += 1
    return labels, len(H), next_label


def infinity_image(Ep, p, q, sa, sb, sc):
    eb = sb * sa
    ec = sc * sa
    if eb == 1 and ec == 1:
        return Ep(0, 0)
    if eb == 1 and ec == -1:
        return Ep(-4*Ep.base_field()(p), 0)
    if eb == -1 and ec == 1:
        return Ep(-4*Ep.base_field()(q), 0)
    return Ep(0)


def local_data(prime, factors, class_points):
    F = GF(prime)
    local_curves = []
    factor_class_labels = []
    quotient_meta = []

    for (inds, E0, p, q), reps in zip(factors, class_points):
        Ep = EllipticCurve(F, [F(x) for x in E0.a_invariants()])
        labels, double_size, quotient_size = quotient_labels(Ep)
        glabels = [labels[reduce_projective_point(P, Ep, prime)] for P in reps]
        local_curves.append((inds, Ep, F(p), F(q), labels))
        factor_class_labels.append(glabels)
        quotient_meta.append({
            "group_order": int(Ep.cardinality()),
            "double_subgroup_order": int(double_size),
            "quotient_size": int(quotient_size),
        })

    roots = {F(x): [] for x in range(prime)}
    for y in F:
        roots[y*y].append(y)

    image = set()
    affine_points = 0
    valid_t = 0
    for t0 in F:
        rlists = [roots[t0 + F(r*r)] for r in ROWS]
        if any(not xs for xs in rlists):
            continue
        valid_t += 1
        for us in itertools.product(*rlists):
            labs = []
            for inds, Ep, pp, qq, labels in local_curves:
                ia, ib, ic = inds
                u, v, w = us[ia], us[ib], us[ic]
                X = F(4) * (v-u) * (w-u)
                Y = F(8) * (v-u) * (w-u) * (v+w)
                Q = Ep(X, Y)
                labs.append(labels[Q])
            image.add(tuple(labs))
            affine_points += 1

    # Eight projective points at infinity, normalized by s_0 = +1.
    infinity_points = 0
    for tail in itertools.product([1, -1], repeat=3):
        signs = (1,) + tail
        labs = []
        for inds, Ep, pp, qq, labels in local_curves:
            ia, ib, ic = inds
            Q = infinity_image(Ep, pp, qq, signs[ia], signs[ib], signs[ic])
            labs.append(labels[Q])
        image.add(tuple(labs))
        infinity_points += 1

    return {
        "prime": prime,
        "local_image": image,
        "factor_class_labels": factor_class_labels,
        "valid_affine_t": valid_t,
        "affine_projective_points_counted": affine_points,
        "infinity_points_counted": infinity_points,
        "local_image_size": len(image),
        "quotients": quotient_meta,
    }


def decode(code, sizes):
    vals = []
    for size in sizes:
        vals.append(code % size)
        code //= size
    return vals


def encode(vals, sizes):
    code = 0
    mult = 1
    for v, size in zip(vals, sizes):
        code += mult * v
        mult *= size
    return code


def main():
    started = time.time()
    factors = []
    bases = []
    class_points = []
    factor_report = []
    for inds in TRIPLES:
        E0, p, q = input_curve(inds)
        gens, rank = certified_basis_on_input(E0)
        basis, reps = global_classes(E0, p, gens)
        factors.append((inds, E0, p, q))
        bases.append(basis)
        class_points.append(reps)
        factor_report.append({
            "indices": list(inds),
            "rows": [int(ROWS[i]) for i in inds],
            "rank_proved": rank,
            "basis_dimension_mod_2": len(basis),
            "class_count": len(reps),
            "input_ainvs": [str(x) for x in E0.a_invariants()],
            "generators_input": [
                [str(P[0]), str(P[1]), str(P[2])] if not P.is_zero() else ["0"]
                for P in gens
            ],
        })

    sizes = [len(x) for x in class_points]
    total = math.prod(sizes)
    survivors = None
    prime_reports = []

    for prime in PRIMES:
        # Require good reduction and four distinct row-square branch values.
        if any(Integer(E0.discriminant()) % prime == 0 for _, E0, _, _ in factors):
            continue
        sqs = [int((r*r) % prime) for r in ROWS]
        if len(set(sqs)) < 4:
            continue
        data = local_data(prime, factors, class_points)
        allowed = data.pop("local_image")
        glabs = data.pop("factor_class_labels")

        if survivors is None:
            survivors = []
            for vals in itertools.product(*[range(s) for s in sizes]):
                labtuple = tuple(glabs[j][vals[j]] for j in range(4))
                if labtuple in allowed:
                    survivors.append(encode(vals, sizes))
        else:
            kept = []
            for code in survivors:
                vals = decode(code, sizes)
                labtuple = tuple(glabs[j][vals[j]] for j in range(4))
                if labtuple in allowed:
                    kept.append(code)
            survivors = kept

        data["survivors_after_prime"] = len(survivors)
        prime_reports.append(data)
        print(f"p={prime}: local={data['local_image_size']} survivors={len(survivors)}", flush=True)
        if len(survivors) <= 256:
            # Enough for the next covering stage; more primes are still harmless,
            # but preserve runtime for certificate generation.
            pass

    if survivors is None:
        raise RuntimeError("no usable good primes")

    decoded = [decode(c, sizes) for c in survivors]
    out = {
        "rows": [int(x) for x in ROWS],
        "triple_order": [list(x) for x in TRIPLES],
        "factors": factor_report,
        "global_product_class_count_upper_bound": total,
        "primes": prime_reports,
        "final_survivor_count_upper_bound": len(survivors),
        "final_survivor_indices": decoded if len(decoded) <= 20000 else None,
        "soundness": "The quartic fifth quotient is omitted, so this is a rigorous upper bound on compatible global Kummer tuples.",
        "elapsed_seconds": round(time.time() - started, 3),
    }
    Path("results").mkdir(exist_ok=True)
    Path("results/kummer_compat.json").write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "final_survivors": len(survivors),
        "total": total,
        "elapsed_seconds": out["elapsed_seconds"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
