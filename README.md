# Math Proof Playground

A **static web app** — a living library of famous math problems, both **solved** and **unsolved**.

- **Solved** problems ship with real, machine-checked proofs in **Coq**, **Lean 4**, **Isabelle/HOL**, **HOL Light** and more — and where possible you can **run the verifier right in your browser**.
- **Open** problems (Goldbach, P vs NP, Riemann, Collatz, the Erdős problems, …) invite you to **give them a try** with interactive explorers.

The whole thing is plain HTML/CSS/JS — no build step, no framework, no server. It lives in [`/math/`](./math/) and deploys to **GitHub Pages**.

👉 **Live site:** once Pages is enabled, the app is at `https://<user>.github.io/<repo>/math/` (the repo root redirects there automatically).

---

## What's inside

| Feature | How it works |
| --- | --- |
| **Coq proofs that run** | [jsCoq](https://github.com/jscoq/jscoq) (the Coq toolchain compiled to WebAssembly) is loaded on demand from a CDN. Runnable proofs (e.g. Gauss's sum, addition is commutative) can be checked live. |
| **Live logic verifier** | A from-scratch propositional-logic engine (`logic.js`) tokenizes, parses, and decides a formula by exhaustive truth table — a genuine, complete proof procedure. It *proves* De Morgan's law, Peirce's law, etc. with **zero dependencies**, even offline. |
| **Number-theory explorers** | `numtools.js` has exact (BigInt + deterministic Miller–Rabin) helpers powering interactive "give it a try" widgets for Goldbach, Collatz, twin primes, Erdős–Straus, Legendre, Mersenne primes, and a tiny DPLL **SAT solver** for the P-vs-NP demo. |
| **Multiple proof systems** | Each problem can carry proofs/statements in several systems; a tabbed viewer with syntax highlighting shows all of them and flags whether each is *verified*. |
| **Solved vs. unsolved** | Every problem is clearly badged **Solved / Open / Partial**, and solved ones link the code proof. |

## Problem set (a taste)

- **Solved & runnable:** Gauss's summation formula, addition is commutative, even + even is even (live Coq); De Morgan / Peirce / contraposition (live JS logic).
- **Solved & formalized:** infinitude of primes, √2 is irrational, the Four Color Theorem (Gonthier/Coq), the Kepler Conjecture (Flyspeck), Fermat's Last Theorem, the Erdős Discrepancy Problem, and an IMO 2024 problem solved by **DeepMind's AlphaProof**.
- **Open:** Goldbach, Collatz, Twin Primes, Erdős–Straus, Legendre, Mersenne primes, and the Millennium Problems — **P vs NP**, Riemann Hypothesis, Navier–Stokes, Birch–Swinnerton-Dyer, Hodge, Yang–Mills — plus the disputed **abc conjecture**.

OEIS **A-numbers** are linked where relevant (e.g. Goldbach → A002375, Mersenne → A000668).

## Featured research projects

- [**OEIS A317940**](./math/a317940/) — complete Lean-verified positivity proof and submission package.
- [**Checkerboard no-three-in-line**](./math/checkerboard/) — defect-moment bounds, exact four-direction certificates, and a partial sorry-free Lean formalization. The all-slope lower-bound conjecture remains open.

## Run locally

It's fully static, so any static server works:

```bash
# from the repo root
python3 -m http.server 8000
# then open http://localhost:8000/math/
```

Opening `math/index.html` directly via `file://` also works for everything
except the on-demand jsCoq load (which needs `http(s)`); the built-in logic
verifier and all number-theory explorers work offline regardless.

## Deploy to GitHub Pages

A workflow is included at [`.github/workflows/pages.yml`](./.github/workflows/pages.yml):

1. Push to `main`.
2. In the repo, go to **Settings → Pages → Build and deployment** and set **Source: GitHub Actions**.
3. The workflow uploads the whole repo and deploys it; your app is at `…/math/`.

## Add a problem

Everything is data-driven. Append an object to the array in
[`math/assets/js/data.js`](./math/assets/js/data.js) — give it an `id`,
`status`, `statement`, optional `proofs` (per system, with `runnable: true`
for live-checkable Coq), and an optional `playground` for interactivity.
No rebuild needed.

## Project layout

```
/
├── index.html                 # redirects to ./math/
├── .nojekyll                  # let Pages serve files as-is
├── .github/workflows/pages.yml
└── math/
    ├── index.html             # the app shell
    └── assets/
        ├── css/style.css
        └── js/
            ├── data.js        # the problem catalog (edit me!)
            ├── logic.js       # propositional-logic verifier
            ├── numtools.js    # number-theory + SAT explorers
            ├── coq.js         # jsCoq loader (best-effort)
            └── app.js         # SPA: routing, rendering, playgrounds
```
