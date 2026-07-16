#!/usr/bin/env python3
"""Exact fixed-top specialization for the n=22, target-34 CNF.

This eliminates point-excess terms fixed by the top boundary and removes the
four outer-line deficiency variables after the all-double boundary reduction.
"""
import itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType as CEnc
import n22_data as d
from n22_exact_core import weighted_equals_reduced_bdd


def build(top, canonical=False):
    vp = IDPool(start_from=len(d.P) + 1)
    cnf = CNF()
    for line in d.LINES:
        if len(line) == 3:
            cnf.append([-line[0], -line[1], -line[2]])
        else:
            cnf.extend(CardEnc.atmost(list(line), 2, vpool=vp, encoding=CEnc.seqcounter).clauses)
    cnf.extend(CardEnc.equals(list(range(1, len(d.P) + 1)), 34, vpool=vp, encoding=CEnc.seqcounter).clauses)

    # In the all-double regime, all four outer boundaries contain exactly two points.
    for ids in d.BIDS.values():
        cnf.extend(CardEnc.equals(ids, 2, vpool=vp, encoding=CEnc.seqcounter).clauses)

    top_selected = set()
    for i, var in enumerate(d.BIDS['top']):
        selected = bool((top >> i) & 1)
        cnf.append([var if selected else -var])
        if selected:
            top_selected.add(var)

    # Canonical top boundary is numerically minimal among the four oriented masks.
    for side in ('left', 'rb', 'rr'):
        for mask in d.DOUBLES:
            if mask >= top:
                break
            bits = [i for i in range(11) if (mask >> i) & 1]
            cnf.append([-d.BIDS[side][bits[0]], -d.BIDS[side][bits[1]]])

    fixed_excess = sum(d.COVERAGE[var - 1] - d.DEN for var in top_selected)
    residual = d.BUD - fixed_excess
    literals, weights, high_low = [], [], []
    top_vars = set(d.BIDS['top'])

    for i, coverage in enumerate(d.COVERAGE, 1):
        excess = coverage - d.DEN
        if excess > 0 and i not in top_vars:
            literals.append(i)
            weights.append(excess)

    outer_names = {'x0', 'x21', 'y0', 'y21'}
    for weight, line, name in d.WL:
        if name in outer_names:
            continue
        empty = vp.id(('empty', name))
        low = vp.id(('low', name))
        cnf.append([empty] + list(line))
        for var in line:
            cnf.append([-empty, -var])
        for omitted in range(len(line)):
            cnf.append([low] + [line[j] for j in range(len(line)) if j != omitted])
        for a, b in itertools.combinations(line, 2):
            cnf.append([-low, -a, -b])
        cnf.append([-empty, low])
        literals.extend((empty, low))
        weights.extend((weight, weight))
        if 2 * weight > residual:
            high_low.append(low)
        if weight > residual:
            cnf.extend(CardEnc.equals(list(line), 2, vpool=vp, encoding=CEnc.seqcounter).clauses)
        elif 2 * weight > residual:
            cnf.append(list(line))

    cnf.extend(CardEnc.atmost(high_low, 1, vpool=vp, encoding=CEnc.seqcounter).clauses)
    info = weighted_equals_reduced_bdd(cnf, literals, weights, residual, vp, 'slack')
    info.update(fixed_top_excess=fixed_excess, residual=residual, high_low_amo=len(high_low))

    if canonical:
        all_masks = [mask for mask in d.DOUBLES if mask >= top]
        left_masks = [mask for mask in all_masks if (mask & 1) == (top & 1)]

        def selected(side, mask):
            return [d.BIDS[side][i] for i in range(11) if (mask >> i) & 1]

        def is_canonical(t, left, rb, rr):
            q = (t, left, rb, rr)
            return q == min({q, (left, t, rr, rb), (rb, rr, t, left), (rr, rb, left, t)})

        blocked = 0
        for left in left_masks:
            for rb in all_masks:
                for rr in all_masks:
                    if (rr & 1) != (rb & 1) or is_canonical(top, left, rb, rr):
                        continue
                    clause_vars = sorted(set(selected('left', left) + selected('rb', rb) + selected('rr', rr)))
                    cnf.append([-var for var in clause_vars])
                    blocked += 1
        info['canonical_blocks'] = blocked

    cnf.nv = max(cnf.nv, vp.top)
    return cnf, info
