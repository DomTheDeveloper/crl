# Panel E: monotone-operator Bernstein grand theorem

## Audit target

Review `math/bernstein_obstacle/GRAND_THEOREM_V6.md` against branch
`research/bernstein-v6-grand-inner-cone`.

The central claim is that the Bernstein inner-cone construction and the sharp
regular-interface recovery estimate extend from symmetric quadratic obstacle
energies to all hemicontinuous, strongly monotone, Lipschitz operators.

The proposed estimate is

\[
\|u-u_n^B\|_{H^1(\Omega)}
\le C\bigl(h_n^r+h_{\Gamma,n}^{3/2}\bigr),
\]

without symmetry or linearity.

Return `PASS`, `PASS AFTER STATED CORRECTION`, or `FAIL` separately for E1--E9.

---

## E1. Abstract inner-cone Mosco theorem

Hypotheses:

\[
K_n\subset K,
\qquad
\forall v\in K\ \exists v_n\in K_n:\ v_n\to v.
\]

Claim: `K_n -> K` in the Mosco sense because `K` is closed and convex and
therefore weakly closed.

**Failure criterion:** produce a Hilbert-space counterexample under the exact
inclusion and recovery hypotheses.

---

## E2. Nonlinear Falk inequality

For `A:V->V*` that is `alpha`-strongly monotone and `L`-Lipschitz, and VI
solutions over `K` and `K_n subset K`, the claim is

\[
\alpha\|u_n-u\|^2
\le L\|u_n-u\|\,\|v_n-u\|
 +\langle A(u)-f,v_n-u\rangle.
\]

Required sign checks:

1. continuous VI tested with `u_n`;
2. discrete VI tested with `v_n`;
3. subtraction of the continuous residual;
4. replacement of `u_n-u` by `(u_n-v_n)+(v_n-u)`;
5. Lipschitz estimate on `A(u_n)-A(u)`.

**Failure criterion:** identify a reversed inequality, an illegitimate test
function, or a missing assumption.

---

## E3. Squared-error and strong convergence

Young's inequality gives

\[
\|u_n-u\|^2
\le
\frac{L^2}{\alpha^2}\|v_n-u\|^2
+\frac2\alpha\langle A(u)-f,v_n-u\rangle.
\]

A strong recovery sequence makes both terms vanish.

**Failure criterion:** show that the residual need not vanish despite
`v_n->u`, or that uniqueness/existence requires an unstated hypothesis.

The panel should distinguish:

- hypotheses needed for the algebraic estimate;
- hypotheses needed for existence of the VI solutions.

---

## E4. Rate-transfer principle

If

\[
\|v_n-u\|\le C\rho_n,
\qquad
\langle A(u)-f,v_n-u\rangle\le C\rho_n^2,
\]

then `||u_n-u|| <= C rho_n`.

**Failure criterion:** find a missing positivity or square-root argument.

---

## E5. Bernstein realization

The general Bernstein cone has:

1. exact inclusion in the pointwise nonnegative cone;
2. strong feasible recovery through positive smooth density and Bernstein
   sampling.

Claim: these geometric facts are independent of the operator and therefore
activate E1--E4 for every strongly monotone Lipschitz VI.

**Failure criterion:** identify an operator-dependent step hidden in the
Bernstein recovery construction.

---

## E6. Nonzero translated obstacles

For `psi in V`, majorants `psi_n in V_n` with

\[
\psi_n\ge\psi,
\qquad
\psi_n\to\psi,
\]

and

\[
K_{n,\psi_n}^B=\psi_n+K_n^B,
\]

claim:

\[
K_{n,\psi_n}^B\xrightarrow{M}\psi+K.
\]

**Failure criterion:** expose a boundary-trace, affine-space, or majorant
problem under the exact stated translation-compatible hypotheses.

The reviewer must separately state whether the theorem can be extended to the
usual condition `psi<=0` on the physical boundary without assuming
`psi in H_0^1`.

---

## E7. Grand regular-interface rate

Use the existing recovery

\[
\|v_n^B-u\|_{H^1}
\le C(h_n^r+h_{\Gamma,n}^{3/2})
\]

and multiplier consistency

\[
\langle\lambda,v_n^B-u\rangle
\le Ch_{\Gamma,n}^3.
\]

Claim: E4 gives the identical sharp rate for nonlinear and nonsymmetric
operators when `lambda=A(u)-f` is a bounded nonnegative density supported on
contact.

Checks required:

1. complementarity and sign of `lambda` for the chosen convention;
2. pointwise `O(h_Gamma^2)` bound of the repaired field on contact;
3. `h_Gamma^3 <= (h^r+h_Gamma^(3/2))^2`;
4. no use of symmetry anywhere in E2;
5. mesh-independent dependence on `alpha` and `L`.

**Failure criterion:** identify an operator-specific regularity or
complementarity step that invalidates the claimed class.

---

## E8. Same-cone perturbation theorem

Let `u_n^*` solve `(A,f)` over `K_n`, and let `u_n^delta` solve `(A_n,f_n)`
over the same `K_n`.  If `A_n` is `alpha_n`-strongly monotone, define

\[
\epsilon_n
=\|(A-A_n)u_n^*-(f-f_n)\|_{V^*}.
\]

Claim:

\[
\|u_n^\delta-u_n^*\|
\le\epsilon_n/\alpha_n.
\]

Required tests:

- exact VI tested with `u_n^delta`;
- perturbed VI tested with `u_n^*`.

**Failure criterion:** locate a sign error or show the estimate needs
Lipschitz continuity, symmetry, or linearity.

---

## E9. Novelty boundary

The reviewer must distinguish classical ingredients from the candidate new
synthesis.

Classical or adjacent:

- Mosco stability of variational inequalities;
- Falk estimates;
- Strang--Falk perturbation estimates;
- higher-order finite-element obstacle analysis;
- strongly monotone VI stability.

Candidate project contribution:

- arbitrary-degree Bernstein coefficient inner cones with exact pointwise
  feasibility;
- concrete positive Mosco recovery on simplicial meshes;
- codimension-one clipping with a `3/2` energy scale;
- transfer of that exact sharp scale to nonsymmetric and nonlinear strongly
  monotone operators.

**Failure criterion:** locate prior work containing the complete combination,
or show that the operator extension is an immediate previously stated
corollary with no new Bernstein-specific content.

---

## Required final report

The signed report should state:

1. verdict for E1--E9;
2. corrected strongest theorem, if narrower;
3. whether symmetry is genuinely eliminated;
4. whether global Lipschitz continuity can be weakened to local Lipschitz or
   bounded-set continuity;
5. whether the translated-obstacle theorem is useful as stated;
6. whether the `3/2` rate survives for a representative quasilinear operator;
7. the closest prior-art theorem and the exact remaining novelty;
8. which theorem should be formalized in Lean first.
