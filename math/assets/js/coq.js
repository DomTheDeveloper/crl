/*
 * coq.js — best-effort in-browser Coq verification via jsCoq.
 *
 * jsCoq (a full Coq toolchain compiled to WebAssembly) is loaded on demand
 * from a CDN the first time the user asks to run a proof. If the CDN is
 * unreachable (e.g. an offline / air-gapped deployment) the caller falls back
 * to showing the proof source with a link to an external playground.
 *
 * Exposed as window.MP_COQ.
 */
(function () {
  "use strict";

  const CDN = "https://cdn.jsdelivr.net/npm/jscoq@0.16.3/";
  let loaderPromise = null;
  let coqInstance = null;

  function loadScript(src) {
    return new Promise((resolve, reject) => {
      const s = document.createElement("script");
      s.type = "text/javascript";
      s.src = src;
      s.onload = () => resolve();
      s.onerror = () => reject(new Error("Failed to load " + src));
      document.head.appendChild(s);
    });
  }

  // Load the jsCoq loader once.
  function ensureLoader() {
    if (loaderPromise) return loaderPromise;
    loaderPromise = loadScript(CDN + "jscoq-loader.js").then(() => {
      if (typeof window.JsCoq === "undefined") throw new Error("jsCoq loader did not register JsCoq");
      return window.JsCoq;
    });
    return loaderPromise;
  }

  /*
   * Start (or reuse) a jsCoq instance attached to `mountEl` and load `code`.
   * Returns a promise resolving to the coq manager. Because jsCoq's exact API
   * varies across releases, we keep this defensive and let the caller handle
   * rejection by falling back to source display.
   */
  function start(mountEl, code) {
    return ensureLoader().then((JsCoq) => {
      const opts = {
        base_path: CDN,
        editor: { mode: { "company-coq": true } },
        show: true,
        focus: false
      };
      // jsCoq 0.16 API: JsCoq.start(base, node_selector_or_el, [packages], opts)
      return JsCoq.start(CDN, mountEl, [], opts).then((coq) => {
        coqInstance = coq;
        return coq;
      });
    });
  }

  window.MP_COQ = {
    available: typeof WebAssembly !== "undefined",
    CDN,
    ensureLoader,
    start,
    externalPlayground: "https://coq.vercel.app/"     // web Coq / jsCoq playground
  };
})();
