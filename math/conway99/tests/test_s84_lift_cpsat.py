import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s84_lift_cpsat import build_model


def test_s84_lift_model_dimensions():
    model, context, stats = build_model(0)
    assert model is not None
    assert context["parameter"] == 0
    assert stats == {
        "parameter": 0,
        "frame_variables": 21,
        "edge_translation_variables": 105,
        "triangle_holonomy_variables": 315,
        "six_path_variables": 630,
        "intersecting_fiber_pairs": 105,
    }
