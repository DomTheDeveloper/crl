# Proofs & continuous verification

Machine-checkable sources for the proofs shown on the site, plus the CI that
re-verifies them on every push.

```
proofs/
├── coq/                     Coq proofs (self-contained; Arith + Lia)
│   ├── gauss_sum.v          2·(1+…+n) = n(n+1)      [induction + nia]
│   ├── add_comm.v           n + m = m + n
│   ├── even_plus_even.v     even + even is even
│   ├── mul_one_r.v          n · 1 = n
│   └── verify.mjs           runs every .v through the jsCoq (Coq-WASM) CLI
└── lean/
    ├── core/                core-Lean proofs (NO Mathlib) — also the ones that
    │   └── Core.lean        run in the in-browser Lean (lean4.js / WASM)
    └── A317940/             the A317940 nonnegativity proof, vs. real Mathlib
        ├── A317940.lean     659-line proof of the DeepMind conjecture
        └── lakefile.toml    requires Mathlib (pinned to the toolchain)
```

## How each layer is verified

| Layer | Verifier | Where |
| --- | --- | --- |
| Coq proofs | jsCoq 0.17.1 (Coq compiled to WebAssembly), CLI mode | `verify-coq.yml` → `proofs/coq/verify.mjs` |
| JS solvers (logic, number theory, A317940 rational) | Node | `verify-solvers.yml` → `tests/run.mjs` |
| Core Lean | real Lean toolchain via `lake build` | `verify-lean.yml` (job `lean-core`) |
| **A317940 vs. Mathlib** | real Lean + Mathlib via `lake build`, with `#print axioms` | `verify-lean.yml` (job `lean-a317940`) |

The **`lean-a317940`** job is the important one: it compiles the full proof
against Mathlib on GitHub's runners and prints its axiom dependencies. A green
run with a `[propext, Classical.choice, Quot.sound]` axiom footprint (no
`sorryAx`) is the independent kernel re-check that a browser/WASM or a sandbox
without a Lean toolchain cannot perform.

## Two ways to run a proof

1. **WASM (in your browser / headless):**
   - Coq — `npm i jscoq@0.17.1 && node proofs/coq/verify.mjs`
   - Lean (core only) — the site's "Run in Lean" button (lean4.js), or the
     [Lean 4 web playground](https://live.lean-lang.org/).
2. **CI (GitHub Actions):** push, and the three `verify-*.yml` workflows run.

> **Why not run A317940 in WASM?** The in-browser Lean (lean4.js) ships only the
> Lean standard library, not Mathlib (~GBs of compiled artifacts). A317940
> imports Mathlib, so it is verified via the Actions/Mathlib path, while core
> proofs run in the browser.

## Toolchain pin

`lean-toolchain` pins `leanprover/lean4:v4.27.0` (the toolchain the A317940
proof was authored against). If Mathlib and the toolchain drift, bump the
`version` in `A317940/lakefile.toml` and the `lean-toolchain` files together.
