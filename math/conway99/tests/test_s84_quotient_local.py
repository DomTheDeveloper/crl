import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from s84_quotient_local_audit import audit


def test_s84_quotient_local_audit():
    report = audit()
    assert report['PASS']
    assert report['supports_checked'] == 256
    assert report['signature_counts'] == {
        '(0, 0, 105, 84, 1)': 1,
        '(48, 72, 129, 84, 1)': 105,
        '(56, 84, 133, 84, 1)': 150,
    }
