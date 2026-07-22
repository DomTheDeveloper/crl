import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from s84_translation_parity_audit import audit


def test_s84_translation_parity_audit():
    report = audit()
    assert report["PASS"]
    assert report["translation_variables_over_F2"] == 210
    assert report["linear_equations"] == 546
    assert report["coefficient_rank"] == 169
    assert report["augmented_rank"] == 170
    assert report["certificate_equations"] == 54
    assert report["certificate_type_counts"] == {
        "central_double": 27,
        "curved_axis": 14,
        "curved_pair": 12,
        "identity": 1,
    }
    assert (
        report["certificate_sha256"]
        == "5a5bdfbf3df68bdf3cc02e1c46d0ea41044643f9da56dfb57948331bd813f65c"
    )
    assert report["local_rules"]["flat_edges"] == 21
    assert report["local_rules"]["curved_edges"] == 84
    assert report["local_rules"]["allowed_triple_histogram"] == {1: 21, 2: 84}
