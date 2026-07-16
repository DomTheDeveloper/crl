# Math Proof Playground

A **static web app** — a living library of famous math problems, both **solved** and **unsolved**.

- **Solved** problems ship with real, machine-checked proofs in **Coq**, **Lean 4**, **Isabelle/HOL**, **HOL Light** and more — and where possible you can **run the verifier right in your browser**.
- **Open** problems (Goldbach, P vs NP, Riemann, Collatz, the Erdős problems, …) invite you to **give them a try** with interactive explorers.
- **Research progress** is published with explicit evidence grades: kernel-verified exact statement, complete proof candidate, partial/computational progress, or still open.

The whole thing is plain HTML/CSS/JS — no build step, no framework, no server. It lives in [`/math/`](./math/) and deploys to **GitHub Pages**.

👉 **Live site:** https://domthedeveloper.github.io/crl/math/

---

## What's inside

| Feature | How it works |
| --- | --- |
| **Coq proofs that run** | [jsCoq](https://github.com/jscoq/jscoq) (the Coq toolchain compiled to WebAssembly) is loaded on demand from a CDN. Runnable proofs can be checked live. |
| **Live logic verifier** | A from-scratch propositional-logic engine tokenizes, parses, and decides a formula by exhaustive truth table. |
| **Number-theory explorers** | Exact BigInt and deterministic-primality helpers power interactive Goldbach, Collatz, twin-prime, Erdős–Straus, Legendre and Mersenne widgets. |
| **Multiple proof systems** | Each problem can carry proofs/statements in several systems; the viewer records whether each artifact is actually verified. |
| **Research audit pages** | Dedicated pages separate exact formal proofs, paper proofs, partial Lean formalizations, computations and unresolved claims. |

## Featured research projects

- [**Comprehensive research dashboard**](./math/research/) — every substantial campaign, evidence-graded and cross-linked.
- [**OEIS A317940**](./math/a317940/) — complete Lean-verified positivity proof and submission package.
- [**Checkerboard no-three-in-line**](./math/checkerboard/) — defect-moment bounds, exact four-direction certificates, and a partial sorry-free Lean formalization; the all-slope lower bound remains open.
- [**Written on the Wall II**](./math/wowii/) — audited progress on conjectures 65, 133, 143, 160, 314 and 316.
- [**Erdős problems**](./math/erdos/) — exact variants 602, 865 and 1150, plus the open 885 and 366 campaigns.
- [**OEIS A387471**](./math/a387471/) — proof manuscript and Lean formalization frontier.
- [**Open campaign archive**](./math/open-campaigns/) — substantial investigations that did not produce a complete solution.

Machine-readable status: [`math/research/status.json`](./math/research/status.json).

## Problem set (a taste)

- **Solved & runnable:** Gauss's summation formula, addition is commutative, even + even is even, De Morgan, Peirce and contraposition.
- **Solved & formalized:** infinitude of primes, √2 irrationality, the Four Color Theorem, Kepler, Fermat's Last Theorem, the Erdős Discrepancy Problem and selected Formal Conjectures variants.
- **Open:** Goldbach, Collatz, Twin Primes, Erdős–Straus, Legendre, Mersenne primes, P vs NP, Riemann Hypothesis and the other Millennium Problems.

## Run locally

```bash
python3 -m http.server 8000
# open http://localhost:8000/math/
```

Opening `math/index.html` directly via `file://` also works for most features; on-demand WASM provers require `http(s)`.

## Deploy to GitHub Pages

The public site is served from the `gh-pages` branch. The repository also contains `.github/workflows/pages.yml` for GitHub Actions deployment.

## Add a problem

The interactive catalog is data-driven. Append an object to [`math/assets/js/data.js`](./math/assets/js/data.js) with an `id`, `status`, statement, optional proof artifacts and optional playground.

Standalone research projects can use the audited project-page pattern under `math/<project>/`, with explicit sections for:

1. exact claim;
2. proof idea;
3. verification evidence;
4. prior-art/attribution boundary;
5. what remains open.

## Project layout

```text
/
├── index.html
├── .nojekyll
├── .github/workflows/
├── proofs/
└── math/
    ├── index.html
    ├── research/
    ├── a317940/
    ├── checkerboard/
    ├── wowii/
    ├── erdos/
    ├── a387471/
    ├── open-campaigns/
    └── assets/
```
