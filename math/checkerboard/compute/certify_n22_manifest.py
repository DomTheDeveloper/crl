#!/usr/bin/env python3
"""Turn one closed n=22 decision manifest into a minimal LRAT certificate frontier.

The manifest may contain many child solves performed before a parent was later
closed by learned-clause re-probing. This tool keeps the largest closed nodes,
verifies deterministic boundary contradictions directly, and optionally emits
and independently checks DRAT/LRAT proofs for every solver-derived frontier
node. It is resumable: a node with a previously verified metadata record is
not solved again.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import n22_data as d


def mask_ids(side: str, mask: int) -> list[int]:
    return [d.BIDS[side][i] for i in range(11) if (mask >> i) & 1]


def canonical_quad(top: int, left: int, rb: int, rr: int) -> bool:
    q = (top, left, rb, rr)
    return q == min(q, (left, top, rr, rb), (rb, rr, top, left), (rr, rb, left, top))


def required_rrs(top: int, left: int, rb: int) -> list[int]:
    allm = [m for m in d.DOUBLES if m >= top]
    return [rr for rr in allm if (rr & 1) == (rb & 1) and canonical_quad(top, left, rb, rr)]


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def selected_boundary_ids(top: int, left: int | None, rb: int | None, rr: int | None) -> list[int]:
    values = mask_ids('top', top)
    for side, mask in (('left', left), ('rb', rb), ('rr', rr)):
        if mask is not None:
            values.extend(mask_ids(side, mask))
    return sorted(set(values))


def det(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def explicit_certificate(node: dict[str, Any]) -> dict[str, Any]:
    ids = selected_boundary_ids(node['top'], node.get('left'), node.get('rb'), node.get('rr'))
    reason = node['reason']
    if reason == 'boundary_collinear_triple':
        for triple in itertools.combinations(ids, 3):
            pts = [d.P[i - 1] for i in triple]
            if det(*pts) == 0:
                return {
                    'kind': 'boundary_collinear_triple',
                    'selected_boundary_ids': ids,
                    'triple_ids': list(triple),
                    'triple_points': pts,
                    'determinant': 0,
                }
        raise AssertionError(f"manifest claims a boundary triple but none exists: {node}")
    if reason.startswith('boundary_excess_'):
        excesses = {str(i): d.COVERAGE[i - 1] - d.DEN for i in ids}
        total = sum(excesses.values())
        claimed = int(reason.rsplit('_', 1)[1])
        assert total == claimed and total > d.BUD, (node, total, claimed)
        return {
            'kind': 'boundary_excess',
            'selected_boundary_ids': ids,
            'point_excesses': excesses,
            'total_excess': total,
            'slack_budget': d.BUD,
        }
    raise AssertionError(f'unknown explicit reason: {reason}')


def latest_closure(rows: list[dict[str, Any]], events: tuple[str, ...], **scope: int) -> dict[str, Any] | None:
    ans = None
    for row in rows:
        if row.get('event') not in events or row.get('status') != 'UNSAT':
            continue
        if all(row.get(k) == v for k, v in scope.items()):
            ans = row
    return ans


def make_node(top: int, row: dict[str, Any]) -> dict[str, Any]:
    return {
        'top': top,
        'left': row.get('left'),
        'rb': row.get('rb'),
        'rr': row.get('rr'),
        'source_event': row['event'],
        'reason': row.get('reason'),
    }


def frontier(rows: list[dict[str, Any]]) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    summaries = [r for r in rows if r.get('event') == 'shard_summary']
    assert len(summaries) == 1 and summaries[0].get('closed') and summaries[0].get('status') == 'UNSAT'
    summary = summaries[0]
    top = summary['top']
    allm = [m for m in d.DOUBLES if m >= top]
    nodes: list[dict[str, Any]] = []
    for left in summary['assigned_lefts']:
        row = latest_closure(rows, ('left', 'left_refined'), left=left)
        if row is not None:
            nodes.append(make_node(top, row))
            continue
        for rb in allm:
            rr_values = required_rrs(top, left, rb)
            if not rr_values:
                continue
            row = latest_closure(rows, ('rb', 'rb_refined'), left=left, rb=rb)
            if row is not None:
                nodes.append(make_node(top, row))
                continue
            for rr in rr_values:
                row = latest_closure(rows, ('leaf',), left=left, rb=rb, rr=rr)
                assert row is not None, f'missing terminal closure top={top} left={left} rb={rb} rr={rr}'
                nodes.append(make_node(top, row))
    return summary, nodes


def node_name(node: dict[str, Any]) -> str:
    parts = [f"t{node['top']}"]
    for short in ('left', 'rb', 'rr'):
        value = node.get(short)
        if value is not None:
            parts.append(f"{short}{value}")
    return '_'.join(parts)


def checked_solver_certificate(node: dict[str, Any], args: argparse.Namespace, out_dir: Path) -> dict[str, Any]:
    name = node_name(node)
    prefix = out_dir / name
    final_meta = out_dir / f'{name}.verified.json'
    if final_meta.exists():
        previous = json.loads(final_meta.read_text())
        for key in ('cnf', 'drat', 'lrat', 'drat_log', 'lrat_log'):
            path = out_dir / previous[key]
            assert path.exists() and sha256(path) == previous[f'{key}_sha256']
        return previous

    cmd = [sys.executable, str(Path(__file__).with_name('emit_scope_drat.py')), '--top', str(node['top']), '--solver', args.solver, '--out', str(prefix)]
    for flag in ('left', 'rb', 'rr'):
        if node.get(flag) is not None:
            cmd.extend([f'--{flag}', str(node[flag])])
    subprocess.run(cmd, check=True, timeout=args.solve_timeout)

    cnf = Path(str(prefix) + '.cnf')
    drat = Path(str(prefix) + '.drat')
    lrat = Path(str(prefix) + '.lrat')
    drat_log = Path(str(prefix) + '.drat-verify.log')
    lrat_log = Path(str(prefix) + '.lrat-verify.log')
    with drat_log.open('w') as log:
        subprocess.run([args.drat_trim, str(cnf), str(drat), '-L', str(lrat)], stdout=log, stderr=subprocess.STDOUT, check=True, timeout=args.check_timeout)
    assert 's VERIFIED' in drat_log.read_text()
    with lrat_log.open('w') as log:
        subprocess.run([args.lrat_check, str(cnf), str(lrat)], stdout=log, stderr=subprocess.STDOUT, check=True, timeout=args.check_timeout)
    assert 's VERIFIED' in lrat_log.read_text()

    record: dict[str, Any] = {'kind': 'solver_lrat', **node}
    for key, path in (('cnf', cnf), ('drat', drat), ('lrat', lrat), ('drat_log', drat_log), ('lrat_log', lrat_log)):
        record[key] = path.name
        record[f'{key}_sha256'] = sha256(path)
    final_meta.write_text(json.dumps(record, indent=2) + '\n')
    return record


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--manifest', required=True)
    ap.add_argument('--out-dir', required=True)
    ap.add_argument('--plan-only', action='store_true')
    ap.add_argument('--solver', default='cadical195')
    ap.add_argument('--drat-trim', default='drat-trim')
    ap.add_argument('--lrat-check', default='lrat-check')
    ap.add_argument('--solve-timeout', type=int, default=7200)
    ap.add_argument('--check-timeout', type=int, default=7200)
    args = ap.parse_args()

    rows = [json.loads(line) for line in Path(args.manifest).read_text().splitlines() if line.strip()]
    assert not any(r.get('event') == 'WITNESS' or r.get('status') == 'SAT' for r in rows)
    summary, nodes = frontier(rows)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    plan = {
        'top': summary['top'],
        'shard': summary['shard'],
        'assigned_lefts': summary['assigned_lefts'],
        'frontier_nodes': len(nodes),
        'explicit_nodes': sum(n.get('reason') is not None for n in nodes),
        'solver_nodes': sum(n.get('reason') is None for n in nodes),
        'nodes': nodes,
    }
    (out_dir / 'frontier-plan.json').write_text(json.dumps(plan, indent=2) + '\n')
    print(json.dumps({k: v for k, v in plan.items() if k != 'nodes'}, indent=2))
    if args.plan_only:
        return 0

    certificates: list[dict[str, Any]] = []
    for index, node in enumerate(nodes, 1):
        print(json.dumps({'event': 'certificate_start', 'index': index, 'total': len(nodes), 'node': node}), flush=True)
        if node.get('reason') is not None:
            certificates.append({'kind': 'explicit', **node, 'certificate': explicit_certificate(node)})
        else:
            certificates.append(checked_solver_certificate(node, args, out_dir))
    report = {
        'status': 'VERIFIED_UNSAT_FRONTIER',
        'symmetry': 'parity-preserving Klein-four lexicographic canonicalization',
        'top': summary['top'],
        'shard': summary['shard'],
        'nodes': len(certificates),
        'explicit_nodes': sum(c['kind'] == 'explicit' for c in certificates),
        'lrat_nodes': sum(c['kind'] == 'solver_lrat' for c in certificates),
        'certificates': certificates,
    }
    (out_dir / 'certificate-frontier.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'certificates'}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
