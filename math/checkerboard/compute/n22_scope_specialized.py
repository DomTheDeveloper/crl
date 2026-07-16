#!/usr/bin/env python3
"""Exact fixed-boundary specialization for n=22 target 34."""
import itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType as CEnc
import n22_data as d
from n22_exact_core import weighted_equals_reduced_bdd


def build(top, left=None, rb=None, rr=None, canonical=True):
    vp = IDPool(start_from=len(d.P) + 1)
    cnf = CNF()
    for line in d.LINES:
        if len(line) == 3:
            cnf.append([-line[0], -line[1], -line[2]])
        else:
            cnf.extend(CardEnc.atmost(list(line), 2, vpool=vp, encoding=CEnc.seqcounter).clauses)
    cnf.extend(CardEnc.equals(list(range(1, len(d.P) + 1)), 34, vpool=vp, encoding=CEnc.seqcounter).clauses)
    for ids in d.BIDS.values():
        cnf.extend(CardEnc.equals(ids, 2, vpool=vp, encoding=CEnc.seqcounter).clauses)

    fixed = {}
    def fix(side, mask):
        if mask is None:
            return
        for i, var in enumerate(d.BIDS[side]):
            value = bool((mask >> i) & 1)
            if var in fixed and fixed[var] != value:
                cnf.append([])
            fixed[var] = value
            cnf.append([var if value else -var])

    fix('top', top)
    fix('left', left)
    fix('rb', rb)
    fix('rr', rr)

    for side in ('left', 'rb', 'rr'):
        for mask in d.DOUBLES:
            if mask >= top:
                break
            bits = [i for i in range(11) if (mask >> i) & 1]
            cnf.append([-d.BIDS[side][bits[0]], -d.BIDS[side][bits[1]]])

    all_masks = [mask for mask in d.DOUBLES if mask >= top]
    def canonical_quad(t, l, b, r):
        q = (t, l, b, r)
        return q == min({q, (l, t, r, b), (b, r, t, l), (r, b, l, t)})
    def selected(side, mask):
        return [d.BIDS[side][i] for i in range(11) if (mask >> i) & 1]

    if canonical and left is not None and rb is None and rr is None:
        for bottom in all_masks:
            for right in all_masks:
                if (bottom & 1) != (right & 1) or canonical_quad(top, left, bottom, right):
                    continue
                cnf.append([-var for var in sorted(set(selected('rb', bottom) + selected('rr', right)))])
    if canonical and left is not None and rb is not None and rr is None:
        for right in all_masks:
            if (rb & 1) != (right & 1) or canonical_quad(top, left, rb, right):
                continue
            cnf.append([-var for var in selected('rr', right)])

    fixed_excess = sum(d.COVERAGE[var - 1] - d.DEN for var, value in fixed.items() if value)
    residual = d.BUD - fixed_excess
    if residual < 0:
        cnf.append([])

    literals, weights, high_low = [], [], []
    outer = {'x0', 'x21', 'y0', 'y21'}
    for i, coverage in enumerate(d.COVERAGE, 1):
        excess = coverage - d.DEN
        if excess > 0 and i not in fixed:
            literals.append(i)
            weights.append(excess)

    for weight, line, name in d.WL:
        if name in outer:
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
    info = weighted_equals_reduced_bdd(cnf, literals, weights, residual, vp, 'slack') if residual >= 0 else {'items': 0, 'states': 0}
    info.update(fixed_excess=fixed_excess, residual=residual, fixed_points=len(fixed), high_low_amo=len(high_low))
    cnf.nv = max(cnf.nv, vp.top)
    return cnf, info
