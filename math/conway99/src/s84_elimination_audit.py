#!/usr/bin/env python3
"""Aggregate exact certificate that eliminates the complete ``s = 84`` branch."""
from __future__ import annotations

import json

from s84_conjugacy_filter_audit import audit as conjugacy_audit
from s84_connection_data import audit as connection_audit
from s84_fano_geometry_audit import audit as fano_audit
from s84_lift_propagation_audit import audit as propagation_audit
from s84_translation_parity_audit import audit as translation_audit
from verify_s84_translation_xor import verify as verify_translation_certificate


def audit():
    conjugacy = conjugacy_audit()
    fano = fano_audit()
    connection = connection_audit()
    propagation = propagation_audit()
    translation = translation_audit()
    replay = verify_translation_certificate()

    assert conjugacy["surviving_supports"] == 30
    assert conjugacy["surviving_support_weight"] == 56
    assert conjugacy["surviving_class_assignment_is_unique"]
    assert fano["surviving_support_orbit_size"] == 30
    assert fano["stabilizer_order"] == 168
    assert connection["support_orbit_size"] == 30
    assert connection["F3_nullity"] == 1
    assert [item["parameter"] for item in connection["connections"]] == [0, 1, 2]
    assert [
        item["root_consistent"] for item in propagation["parameter_reports"]
    ] == [False, True, False]
    assert propagation["forced_common_axis"] == 3
    assert translation["augmented_rank"] == translation["coefficient_rank"] + 1
    assert translation["certificate_equations"] == 54
    assert replay["PASS"]

    return {
        "PASS": True,
        "branch": "s=84",
        "status": "ELIMINATED",
        "curvature_supports_before_conjugacy_filter": 256,
        "surviving_support_orbit_size": 30,
        "surviving_quotient_parameters": 3,
        "parameters_eliminated_by_propagation": [0, 2],
        "parameter_eliminated_by_xor_certificate": 1,
        "xor_certificate_rows": 54,
        "xor_certificate_sha256": replay["certificate_sha256"],
        "current_global_implication": "Every putative Conway graph has s <= 76.",
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
