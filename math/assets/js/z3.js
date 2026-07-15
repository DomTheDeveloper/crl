/*
 * z3.js — in-browser Z3 SMT solver (WebAssembly). The z3-solver package + its
 * ~7 MB wasm are loaded on demand from a CDN (they are far too large to vendor
 * usefully; the same solver is re-verified headlessly in CI via tests/z3.mjs).
 *
 * Exposes window.MP_Z3 with checkSmtlib(src) -> { result, model }.
 */
(function () {
  "use strict";
  const CDN = "https://cdn.jsdelivr.net/npm/z3-solver@4.16.0/+esm";
  let ctxPromise = null;

  function load() {
    if (ctxPromise) return ctxPromise;
    ctxPromise = import(/* @vite-ignore */ CDN)
      .then((mod) => (mod.init ? mod.init() : mod.default.init()))
      .then(({ Context }) => Context("main"));
    return ctxPromise;
  }

  // Solve an SMT-LIB2 string. Returns { result: "sat"|"unsat"|"unknown", model }.
  async function checkSmtlib(src) {
    const Z = await load();
    const solver = new Z.Solver();
    solver.fromString(src);
    const result = await solver.check();
    let model = "";
    if (result === "sat") { try { model = solver.model().toString(); } catch (e) { model = ""; } }
    return { result, model };
  }

  window.MP_Z3 = {
    available: typeof WebAssembly !== "undefined",
    cdn: CDN,
    load,
    checkSmtlib
  };
})();
