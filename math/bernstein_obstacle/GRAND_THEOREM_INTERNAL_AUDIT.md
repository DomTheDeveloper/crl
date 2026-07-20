# Internal audit of the Bernstein grand theorem

## Verdict

**PASS AS A CONDITIONAL ANALYTICAL THEOREM PACKAGE**

The abstract nonlinear estimate is algebraically complete. The obstacle and
planar Signorini corollaries are complete under their explicit regularity,
multiplier, conservative-data, mesh, and stable-lifting hypotheses.

This is not an independent expert verdict.

## A1. Nonlinear Falk sign audit

The key inequality is

\[
\alpha\|u_h-u\|_V^2
\le
L\|u_h-u\|_V\|u-v_h\|_V
+\langle F(u),v_h-u\rangle.
\]

The sign chain uses exactly two feasibility facts:

1. the discrete VI gives
   \[
   \langle F(u_h),u_h-v_h\rangle\le0;
   \]
2. the exact inner inclusion `K_h subset K` permits the continuous test
   `v=u_h`, giving
   \[
   \langle F(u),u_h-u\rangle\ge0.
   \]

No symmetry identity and no potential energy are used.

**Status:** PASS.

## A2. Numerical falsification test

`verification/verify_nonlinear_falk_bound.py` generated 1,000 deterministic
random linear variational inequalities with:

- dimensions 2 through 8;
- positive-definite symmetric parts;
- nonzero skew-symmetric parts;
- continuous feasible set `x >= 0`;
- certified inner set `x >= q >= 0`.

Both VIs were solved through Fischer--Burmeister complementarity equations.
The recorded result was:

- violations below `-1e-7`: `0`;
- worst inequality margin: `-2.79e-25`;
- maximum complementarity residual: `9.44e-13`;
- maximum squared-error/bound ratio: `0.600002`.

The tiny negative worst margin is floating-point roundoff. This experiment is
falsification evidence only; the proof is A1.

**Status:** PASS.

## A3. Codimension repair scaling

Let the constraint manifold have ambient codimension `c`. Its active-set
interface has dimension `d-c-1`, so the number of affected quasi-uniform ambient
elements is

\[
O(h_\Sigma^{-(d-c-1)}).
\]

A lifted coefficient correction of amplitude `O(h_Sigma^2)` has gradient
amplitude `O(h_Sigma)`, and hence one-element squared `H^1` size

\[
O(h_\Sigma^{d+2}).
\]

Multiplication gives

\[
O(h_\Sigma^{c+3}),
\]

so

\[
\|d_h\|_V=O(h_\Sigma^{(c+3)/2}).
\]

Checks:

- `c=0`: `h_Sigma^(3/2)` for a volume obstacle;
- `c=1`: `h_Sigma^2` for boundary contact.

**Status:** PASS under the stable local lifting and patch-count assumptions.

## A4. Universal multiplier exponent

On the active transition strip inside the constraint manifold:

- repaired gap amplitude is `O(h_Sigma^2)`;
- strip measure in the constraint manifold is `O(h_Sigma)`;
- multiplier density is bounded.

Therefore

\[
\langle F(u),v_h-u\rangle=O(h_\Sigma^3).
\]

The nonlinear Falk estimate takes a square root of this contribution, producing
`O(h_Sigma^(3/2))` for both codimensions zero and one.

**Status:** PASS.

## A5. Planar Signorini lifting

For constant normal `n`, clearance coefficient `g_i`, and vector displacement
coefficient `U_i`, define

\[
c_i=g_i-U_i\cdot n.
\]

The update

\[
\widetilde U_i=U_i+\min(c_i,0)n
\]

gives

\[
g_i-\widetilde U_i\cdot n=\max(c_i,0).
\]

Updating each global contact control degree of freedom once preserves conformity
and tangential components. The theorem assumes that the resulting lift belongs
to the essential-boundary-compatible finite-element space; in particular,
contact transition degrees of freedom cannot be subject to incompatible fixed
displacement constraints.

**Status:** PASS for planar constant-normal contact under the stated compatibility
and stable-lifting hypotheses.

## A6. Conservative data direction

To retain an exact inner set:

- obstacle constraint `v >= psi`: require `psi_h^+ >= psi`;
- contact gap `g-v.n >= 0`: require `g_h^- <= g`.

Both choices make the discrete problem more restrictive, never less safe.

**Status:** PASS.

## A7. Prior-art boundary

The nonlinear strongly monotone estimate, Bernstein range certificate, obstacle
and Signorini formulations, and Falk-type approximation philosophy all have
classical neighboring literature. The precise combined theorem and the
codimension-universal interpretation have not received a qualified exhaustive
novelty audit.

**Status:** OPEN EXTERNAL QUESTION.

## A8. Formal verification boundary

The existing Lean project verifies finite coefficient, clipping, assembly,
energy, Mosco-interface, and Hilbert-space infrastructure. The new nonlinear
Falk theorem and codimension geometry are not yet machine checked.

A local pinned Lean attempt could not be run in the current execution environment
because Lean/Lake were not installed and the container could not resolve GitHub
to install the pinned toolchain. No GitHub Actions run was triggered merely for
iteration.

**Status:** ANALYTICAL ONLY; FORMALIZATION OPEN.

## Final internal rating

- Mathematical breadth: **10/10**.
- Abstract proof completeness: **10/10**.
- Conditional geometric proof completeness: **9.5/10**.
- External novelty confidence: **unrated pending search**.
- Independent verification: **not yet**.
