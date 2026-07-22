import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from verify_s84_translation_xor import verify


def test_verify_s84_translation_xor():
    report = verify()
    assert report["PASS"]
    assert report["selected_rows"] == 54
    assert report["coefficient_rank"] == 169
    assert report["augmented_rank"] == 170
    assert report["contradiction"] == "0 = 1 over F2"
    assert (
        report["certificate_sha256"]
        == "5a5bdfbf3df68bdf3cc02e1c46d0ea41044643f9da56dfb57948331bd813f65c"
    )
