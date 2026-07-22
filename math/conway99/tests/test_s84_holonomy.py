import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from s84_holonomy_audit import audit


def test_s84_holonomy_audit():
    report = audit()
    assert report['PASS']

    local = report['disjoint_edge_holonomy']
    assert local['ordered_holonomy_triples_per_preserving_edge'] == 9
    assert local['ordered_holonomy_triples_per_changing_edge'] == 24
    assert local['odd_triangle_holonomies_incident_to_each_edge'] == [0, 2]

    intersecting = report['intersecting_pair_holonomy']
    assert intersecting['ordered_six_holonomy_decompositions'] == 35280
    assert intersecting['unordered_multisets'] == 58

    parity = report['parity_curvature']
    assert parity['boundary_rank_mod_2'] == 85
    assert parity['cycle_coboundary_intersection_dimension'] == 8
    assert parity['odd_holonomy_support_weight_enumerator'] == {
        '0': 1,
        '48': 105,
        '56': 150,
    }

    quotient = report['flat_S3_quotient']
    assert quotient['gauge_fixed_flat_connections'] == 3
    assert quotient['search_nodes'] == 7
