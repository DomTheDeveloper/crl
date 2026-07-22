import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from s84_weight48_translation_sat import LiftModel, load_representatives


def test_weight48_translation_certificate_and_first_cnf():
    certificate = (
        ROOT / 'certificates' / 's84_weight48_linear_orbits.json.gz.b64'
    )
    data = load_representatives(certificate)
    assert data['frame_solutions_per_quotient'] == [7680, 7680, 7680]
    assert data['unique_physical_linear_configurations'] == 3840
    assert data['support_stabilizer_size'] == 48
    assert data['physical_linear_orbits'] == 90
    assert data['orbit_size_histogram'] == {
        '8': 2,
        '16': 2,
        '24': 14,
        '48': 72,
    }

    model = LiftModel(list(map(int, data['representatives'][0])))
    assert len(model.domains) == 1050
    assert len(model.tables) == 1155
    assert Counter(map(len, model.tables)) == Counter({
        16: 630,
        64: 315,
        48: 78,
        2: 72,
        3: 21,
        180: 15,
        6: 12,
        60: 12,
    })
    variables, clauses, _ = model.encode_cnf()
    assert variables == 41883
    assert len(clauses) == 179586
