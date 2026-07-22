import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s76_parity_class_sat import Model


def test_complete_intact_parity_class_projection_dimensions():
    profile = {
        "mask": (1 << 21) - 1,
        "branches": 0,
        "intact_fibers": 21,
    }
    model = Model(profile)
    assert len(model.edge_parity) == 105
    assert len(model.central_edges) == 105
    assert len(model.intersecting_pairs) == 105
    assert len(model.triangle_parity) == 105
    assert len(model.triangle_class) == 105
    assert len(model.path_parity) == 630
    assert model.variables == 945
    assert len(model.clauses) == 10_395
