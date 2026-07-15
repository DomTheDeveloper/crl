/*
 * coq.js — in-browser Coq verification via a self-hosted jsCoq 0.17.1
 * (Coq compiled to WebAssembly). All assets are vendored under ./vendor/jscoq/
 * so nothing is fetched from a third-party CDN. Requires a cross-origin
 * isolated page (SharedArrayBuffer) — see coi-serviceworker.
 *
 * Exposes window.MP_COQ. It launches the jsCoq IDE (editor + goal panel)
 * inside a mount element; the user steps the proof with jsCoq's own controls.
 */
(function () {
  "use strict";

  const BASE = new URL("../../vendor/jscoq/", document.currentScript ? document.currentScript.src : location.href).href;
  let loaderPromise = null;

  function loadJsCoq() {
    if (loaderPromise) return loaderPromise;
    // jsCoq ships its own stylesheet for the IDE/goal panel.
    if (!document.querySelector('link[data-jscoq]')) {
      const link = document.createElement("link");
      link.rel = "stylesheet"; link.href = BASE + "dist/frontend/index.css"; link.setAttribute("data-jscoq", "1");
      document.head.appendChild(link);
    }
    loaderPromise = import(BASE + "jscoq.js").then((m) => m.JsCoq);
    return loaderPromise;
  }

  // Start a jsCoq IDE. The IDE attaches to the element with id="ide-wrapper"
  // (jsCoq 0.17 finds it in the DOM). Resolves to the CoqManager once ready.
  function start(wrapperEl, code, filename) {
    wrapperEl.classList.add("jscoq-main");
    wrapperEl.id = "ide-wrapper";
    if (filename) wrapperEl.setAttribute("data-filename", filename);
    return loadJsCoq().then((JsCoq) => {
      const opts = {
        backend: "wa",
        base_path: BASE,
        // wacoq's worker resolves OCaml runtime stubs page-relative at
        // ./node_modules/ — they are vendored at math/node_modules/.
        init_pkgs: ["init"],
        all_pkgs: ["init", "coq-base", "coq-arith"],
        implicit_libs: true,
        editor: { mode: { "company-coq": true } },
        theme: "dark"
      };
      return JsCoq.start(opts).then((coq) => {
        window.__mpCoq = coq;
        if (code && coq.provider && coq.provider.load) {
          try { coq.provider.load(code, filename || "playground.v"); } catch (e) { /* editor may already hold code */ }
        }
        return coq;
      });
    });
  }

  window.MP_COQ = {
    available: typeof SharedArrayBuffer !== "undefined",
    get isolated() { return window.crossOriginIsolated === true; },
    base: BASE,
    loadJsCoq,
    start,
    externalPlayground: "https://coq.vercel.app/"
  };
})();
