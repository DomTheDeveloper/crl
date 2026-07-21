# Exact-head verification failure at `8d562200bc46e0b416992740289b861e7e26f146`

GitHub Actions run: `29791535407` (`Bernstein obstacle Lean audit`, run 876).

The pinned cache downloaded successfully and Lean compiled both newly added modules:

- `BernsteinObstacle.SobolevH01Port`;
- the dependencies leading into the assembled theorem layer.

The build then reported four mechanical compatibility failures:

1. `ScheduledRecovery.lean`: explicit predicate elaboration required for `Nat.findGreatest_spec`;
2. `MinkowskiSaturation.lean`: definitions depending on real square root/division require a noncomputable section;
3. `MonotoneInnerConeVI.lean`: use componentwise `add_le_add` to preserve summand order;
4. `OptimalGrading.lean`: use componentwise `add_le_add` to preserve summand order.

The successor verification branch applies only these checker repairs before rerunning the complete build and axiom audit.
