# Final-five-percent PR summary

This branch removes two artificial recovery assumptions from the terminal
Bernstein–Bézier obstacle theorem.

## 1. Ordinary FEM convergence now reaches the terminal theorem

`AsymptoticSobolevFEMRecoveryData` already records the hypotheses normally
proved by a finite-element argument for each fixed smooth target: eventual
feasibility and recovery error tending to zero. The new
`AsymptoticGrandTheorem.lean` composes that interface directly with:

- moving-obstacle Mosco convergence;
- strong convergence of constrained minimizers;
- the consistency-limited codimension-growth grand theorem;
- the quadratic-contact `hGamma * sqrt hGamma` specialization.

No explicit threshold schedule is supplied by the caller; it is extracted
internally.

## 2. Eventual feasibility follows from strict clearance

`ClearanceRecovery.lean` formalizes the standard physical argument. For every
fixed smooth stage, assume:

- a strictly positive feasibility clearance;
- strong FEM convergence to that smooth stage;
- feasibility whenever the recovery error is smaller than the clearance.

Then the norm error is eventually below the clearance, hence the recovery is
eventually feasible. This canonically constructs
`AsymptoticSobolevFEMRecoveryData` and closes the entire moving/grand theorem
stack.

## New audited endpoints

- `eventually_norm_lt_clearance`;
- `ClearanceSobolevFEMRecoveryData.toAsymptoticData`;
- clearance and asymptotic Mosco/minimizer endpoints;
- clearance and asymptotic moving-obstacle endpoints;
- clearance and asymptotic general grand theorems;
- clearance and asymptotic quadratic-contact grand theorems.

The root library imports both modules. `GrandCanonicalAudit.lean` and
`FinalFivePercentAudit.lean` check and print axioms for every new endpoint. The
pinned workflow builds the full library, runs both audits, rejects `sorryAx`,
and requires the new theorem names in the transcript.

## Trust boundary

This PR closes the logical recovery composition. It does not claim to have
created a complete concrete `H₀¹(Ω)` or `W₀^{1,p}(Ω)` library. A physical PDE
instantiation must still provide strict smooth density/clearance, the conforming
mesh recovery and interpolation estimate, and PDE-specific multiplier and
free-boundary hypotheses.

No exact-head machine-verification claim is made until the new pinned workflow
passes and the axiom transcript is inspected.
