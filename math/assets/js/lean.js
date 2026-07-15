/*
 * lean.js — in-browser Lean 4 (core) verification via lean4.js (WebAssembly).
 *
 * The heavy WASM + Lean stdlib (~300 MB) is fetched on first use from the
 * lean4-wasm CDN and cached in IndexedDB. Only the Lean standard library is
 * available (no Mathlib), so this runs core-Lean proofs. Requires a
 * cross-origin-isolated page (SharedArrayBuffer) — see coi-serviceworker.
 *
 * Exposes window.MP_LEAN (an ES-module sets it so app.js, a classic script,
 * can use it).
 */
import { Lean4 } from "../vendor/lean4.js";

let instance = null;
let initPromise = null;

const MP_LEAN = {
  // SharedArrayBuffer requires cross-origin isolation; the service worker
  // provides it on static hosts. If it's still false, init will explain.
  get isolated() { return typeof window !== "undefined" && window.crossOriginIsolated === true; },
  available: typeof SharedArrayBuffer !== "undefined",
  // Override before first init to self-host the WASM assets; null = default CDN.
  basePath: null,

  init(onProgress) {
    if (initPromise) return initPromise;
    instance = new Lean4({
      basePath: MP_LEAN.basePath || undefined,
      onProgress: (m) => { if (onProgress) onProgress(m); }
    });
    initPromise = instance.init().then(() => instance);
    return initPromise;
  },

  // Run Lean source; resolves to { ok, exitCode, errors, stdout, stderr }.
  async run(code, onProgress) {
    await MP_LEAN.init(onProgress);
    const r = await instance.run(code, { flags: ["--json"] });
    const blob = (r.stdout || "") + "\n" + (r.stderr || "");
    const errors = (blob.match(/"severity"\s*:\s*"error"/g) || []).length;
    return { ok: r.exitCode === 0 && errors === 0, exitCode: r.exitCode, errors, stdout: r.stdout || "", stderr: r.stderr || "" };
  }
};

if (typeof window !== "undefined") window.MP_LEAN = MP_LEAN;
export default MP_LEAN;
