import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from s84_quotient_curvature_audit import audit


def test_s84_quotient_curvature_audit():
    report = audit()
    assert report['PASS']
    assert report['parity_support_S7_orbits'] == [
        {
            'support_weight': 0,
            'S7_orbit_size': 1,
            'uncurved_triangle_equations': 105,
            'rank_over_F3': 84,
            'gauge_fixed_F3_nullity': 1,
        },
        {
            'support_weight': 48,
            'S7_orbit_size': 105,
            'uncurved_triangle_equations': 57,
            'rank_over_F3': 57,
            'gauge_fixed_F3_nullity': 28,
        },
        {
            'support_weight': 56,
            'S7_orbit_size': 30,
            'uncurved_triangle_equations': 49,
            'rank_over_F3': 49,
            'gauge_fixed_F3_nullity': 36,
        },
        {
            'support_weight': 56,
            'S7_orbit_size': 120,
            'uncurved_triangle_equations': 49,
            'rank_over_F3': 49,
            'gauge_fixed_F3_nullity': 36,
        },
    ]
