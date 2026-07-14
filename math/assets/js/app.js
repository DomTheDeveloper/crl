/*
 * app.js — Math Proof Playground front-end.
 * Vanilla JS SPA with hash routing. No build step, no framework.
 */
(function () {
  "use strict";

  const PROBLEMS = window.MP_PROBLEMS || [];
  const LOGIC = window.MP_LOGIC;
  const NUM = window.MP_NUM;
  const COQ = window.MP_COQ;

  /* ---------------- tiny DOM helpers ---------------- */
  function el(tag, attrs, ...kids) {
    const node = document.createElement(tag);
    if (attrs) {
      for (const k in attrs) {
        if (k === "class") node.className = attrs[k];
        else if (k === "html") node.innerHTML = attrs[k];
        else if (k === "text") node.textContent = attrs[k];
        else if (k.startsWith("on") && typeof attrs[k] === "function") node.addEventListener(k.slice(2), attrs[k]);
        else if (attrs[k] != null) node.setAttribute(k, attrs[k]);
      }
    }
    for (const kid of kids) {
      if (kid == null) continue;
      node.appendChild(typeof kid === "string" ? document.createTextNode(kid) : kid);
    }
    return node;
  }
  const $ = (sel, root) => (root || document).querySelector(sel);

  /* ---------------- status metadata ---------------- */
  const STATUS = {
    solved:  { label: "Solved",   icon: "✓", cls: "s-solved"  },
    open:    { label: "Open",     icon: "?", cls: "s-open"    },
    partial: { label: "Partial",  icon: "◐", cls: "s-partial" }
  };
  const SYSTEM_LABEL = {
    coq: "Coq", lean: "Lean 4", isabelle: "Isabelle/HOL", "hol-light": "HOL Light",
    agda: "Agda", builtin: "Live JS Verifier", note: "Notes"
  };

  /* ---------------- lightweight LaTeX -> Unicode (no dependency) ---------------- */
  function prettyLatex(s) {
    if (!s) return "";
    const sym = {
      "\\neg": "¬", "\\wedge": "∧", "\\vee": "∨", "\\leftrightarrow": "↔",
      "\\Longrightarrow": "⟹", "\\Longleftrightarrow": "⟺", "\\Rightarrow": "⇒",
      "\\longrightarrow": "⟶", "\\to": "→", "\\mapsto": "↦",
      "\\forall": "∀", "\\exists": "∃", "\\nexists": "∄", "\\in": "∈", "\\notin": "∉",
      "\\mathbb{N}": "ℕ", "\\mathbb{Z}": "ℤ", "\\mathbb{Q}": "ℚ", "\\mathbb{R}": "ℝ", "\\mathbb{C}": "ℂ",
      "\\mathsf{P}": "P", "\\mathsf{NP}": "NP",
      "\\ge": "≥", "\\geq": "≥", "\\le": "≤", "\\leq": "≤", "\\ne": "≠", "\\neq": "≠",
      "\\subseteq": "⊆", "\\subset": "⊂", "\\cap": "∩", "\\cup": "∪",
      "\\sum": "∑", "\\prod": "∏", "\\infty": "∞", "\\cdot": "·", "\\times": "×",
      "\\pi": "π", "\\Delta": "Δ", "\\delta": "δ", "\\zeta": "ζ", "\\varepsilon": "ε", "\\epsilon": "ε",
      "\\alpha": "α", "\\beta": "β", "\\gamma": "γ", "\\Gamma": "Γ", "\\lambda": "λ", "\\Lambda": "Λ",
      "\\mu": "μ", "\\nu": "ν", "\\rho": "ρ", "\\sigma": "σ", "\\Sigma": "Σ", "\\tau": "τ", "\\theta": "θ",
      "\\phi": "φ", "\\varphi": "φ", "\\Phi": "Φ", "\\psi": "ψ", "\\Psi": "Ψ", "\\omega": "ω", "\\Omega": "Ω", "\\eta": "η",
      "\\chi": "χ", "\\nabla": "∇", "\\partial": "∂", "\\lfloor": "⌊", "\\rfloor": "⌋", "\\lceil": "⌈", "\\rceil": "⌉",
      "\\Re": "Re", "\\Im": "Im", "\\overset": "", "\\quad": "  ", "\\ ": " ", "\\,": " ", "\\!": "",
      "\\big|": "|", "\\Big|": "|", "\\mid": "|", "\\dots": "…", "\\ldots": "…",
      "\\operatorname": "", "\\max": "max", "\\min": "min", "\\sup": "sup", "\\#": "#", "\\%": "%",
      "\\{": "{", "\\}": "}", "\\left": "", "\\right": "", "\\approx": "≈"
    };
    let out = s;
    // remove sizing/style wrappers, keep their content
    out = out.replace(/\\(?:Bigg|bigg|Big|big|Biggl|Biggr|biggl|biggr|Bigl|Bigr|bigl|bigr)\b/g, "");
    out = out.replace(/\\(?:left|right)\b/g, "");
    out = out.replace(/\\(?:displaystyle|textstyle|scriptstyle|limits|nolimits)\b/g, "");
    out = out.replace(/\\;|\\:|\\ |\\,|\\!/g, " ");
    // \text{...}, \mathrm{...}, \mathbf{...}, \operatorname{...} -> inner content
    out = out.replace(/\\(?:text|textrm|textbf|textit|mathrm|mathbf|mathit|mathsf|operatorname)\*?\s*\{([^{}]*)\}/g, (m, a) => a);
    // sqrt first (its braces would otherwise break frac)
    out = out.replace(/\\sqrt\s*\{([^{}]*)\}/g, (m, a) => "√(" + a + ")");
    out = out.replace(/\\sqrt/g, "√");
    // fractions
    out = out.replace(/\\[tdc]?frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, (m, a, b) => a + "/" + b);
    // \overset{top}{bottom} -> top+bottom (keeps e.g. the ? over = in "P ?= NP")
    out = out.replace(/\\overset\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, (m, a, b) => a + b);
    // symbols (longest first)
    for (const k of Object.keys(sym).sort((a, b) => b.length - a.length)) {
      out = out.split(k).join(sym[k]);
    }
    // superscripts ^2 ^n ^{...} — use unicode only when the whole group maps cleanly
    const sup = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹", "n": "ⁿ", "p": "ᵖ", "k": "ᵏ", "i": "ⁱ", "+": "⁺", "-": "⁻", "(": "⁽", ")": "⁾" };
    const supAll = (a) => [...a].every((c) => sup[c]);
    out = out.replace(/\^\{([^{}]*)\}/g, (m, a) => { a = a.trim(); return supAll(a) ? [...a].map((c) => sup[c]).join("") : "^(" + a + ")"; });
    out = out.replace(/\^(\w)/g, (m, c) => sup[c] || ("^" + c));
    const subm = { "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉", "k": "ₖ", "n": "ₙ", "i": "ᵢ", "+": "₊", "-": "₋", "=": "₌", "(": "₍", ")": "₎" };
    const subAll = (a) => [...a].every((c) => subm[c]);
    out = out.replace(/_\{([^{}]*)\}/g, (m, a) => { a = a.trim(); return subAll(a) ? [...a].map((c) => subm[c]).join("") : "_(" + a + ")"; });
    out = out.replace(/_(\w)/g, (m, c) => subm[c] || ("_" + c));
    // strip leftover braces and stray backslashes before letters
    out = out.replace(/[{}]/g, "").replace(/\\(?=[A-Za-z])/g, "").replace(/\\\\/g, " ");
    return out.replace(/\s{2,}/g, " ").trim();
  }

  /* ---------------- lightweight proof syntax highlighting ---------------- */
  function highlight(code, system) {
    let esc = code.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
    // comments
    if (system === "coq") esc = esc.replace(/\(\*[\s\S]*?\*\)/g, (m) => `<span class="c-com">${m}</span>`);
    else esc = esc.replace(/--.*$/gm, (m) => `<span class="c-com">${m}</span>`);
    const kw = {
      coq: /\b(Theorem|Lemma|Proof|Qed|Admitted|Definition|Fixpoint|forall|exists|match|with|end|intros|induction|rewrite|simpl|reflexivity|apply|exact|Require|Import|symmetry|ring|as)\b/g,
      lean: /\b(theorem|lemma|def|by|import|induction|rw|ring|rfl|sorry|exists|forall|fun|with|Nat|Prime|Finset|Real|Irrational|Even)\b/g,
      isabelle: /\b(theorem|lemma|proof|qed|assume|obtain|where|then|show|fix|from)\b/g,
      "hol-light": /\b(packing|CARD|ball|vec|sqrt|pow|pi)\b/g
    }[system];
    if (kw) esc = esc.replace(kw, (m) => `<span class="c-kw">${m}</span>`);
    return esc;
  }

  /* ---------------- catalog view ---------------- */
  let filterState = { q: "", status: "all", category: "all" };

  function renderCatalog(root) {
    const solved = PROBLEMS.filter((p) => p.status === "solved").length;
    const open = PROBLEMS.filter((p) => p.status === "open").length;
    const partial = PROBLEMS.filter((p) => p.status === "partial").length;
    const categories = Array.from(new Set(PROBLEMS.map((p) => p.category))).sort();

    root.innerHTML = "";

    root.appendChild(
      el("section", { class: "hero" },
        el("h1", { class: "hero-title" }, "∑  Math Proof Playground"),
        el("p", { class: "hero-sub" },
          "A living library of famous math problems — the ", el("strong", { class: "s-solved-t" }, "solved"),
          " ones come with real machine-checked proofs in Coq, Lean, Isabelle & more that you can run right here; ",
          "the ", el("strong", { class: "s-open-t" }, "open"), " ones invite you to give them a try."),
        el("div", { class: "stat-row" },
          statChip(solved, "Solved", "s-solved"),
          statChip(open, "Open", "s-open"),
          statChip(partial, "Partial", "s-partial"),
          statChip(PROBLEMS.length, "Total", "s-total"))
      )
    );

    // controls
    const search = el("input", {
      class: "search", type: "search", placeholder: "Search problems, e.g. Goldbach, primes, Erdős…",
      value: filterState.q, oninput: (e) => { filterState.q = e.target.value.toLowerCase(); paintCards(); }
    });
    const statusSel = pill(["all", "solved", "open", "partial"], filterState.status, (v) => { filterState.status = v; paintCards(); },
      (v) => v === "all" ? "All" : STATUS[v].label);
    const catSel = el("select", { class: "select", onchange: (e) => { filterState.category = e.target.value; paintCards(); } },
      el("option", { value: "all" }, "All categories"),
      ...categories.map((c) => el("option", { value: c, selected: filterState.category === c ? "selected" : null }, c)));

    root.appendChild(
      el("section", { class: "controls" },
        search,
        el("div", { class: "control-group" }, el("span", { class: "control-lbl" }, "Status"), statusSel),
        el("div", { class: "control-group" }, el("span", { class: "control-lbl" }, "Category"), catSel))
    );

    const grid = el("section", { class: "grid" });
    root.appendChild(grid);

    function paintCards() {
      grid.innerHTML = "";
      const list = PROBLEMS.filter((p) => {
        if (filterState.status !== "all" && p.status !== filterState.status) return false;
        if (filterState.category !== "all" && p.category !== filterState.category) return false;
        const q = filterState.q;
        if (!q) return true;
        const hay = (p.title + " " + p.category + " " + p.statement + " " + (p.tags || []).join(" ") + " " + (p.by || "") + " " + (p.oeis || "")).toLowerCase();
        return hay.includes(q);
      });
      if (!list.length) { grid.appendChild(el("p", { class: "empty" }, "No problems match your filters.")); return; }
      for (const p of list) grid.appendChild(card(p));
    }
    paintCards();
  }

  function statChip(n, label, cls) {
    return el("div", { class: "stat-chip " + cls }, el("span", { class: "stat-n" }, String(n)), el("span", { class: "stat-l" }, label));
  }

  function pill(values, active, onPick, labelFn) {
    const wrap = el("div", { class: "pillbar" });
    values.forEach((v) => {
      wrap.appendChild(el("button", {
        class: "pill" + (v === active ? " active" : ""),
        onclick: () => { Array.from(wrap.children).forEach((c) => c.classList.remove("active")); event.currentTarget.classList.add("active"); onPick(v); }
      }, labelFn ? labelFn(v) : v));
    });
    return wrap;
  }

  function card(p) {
    const st = STATUS[p.status];
    const systems = Array.from(new Set((p.proofs || []).map((x) => x.system).filter((s) => s !== "note")));
    return el("a", { class: "card", href: "#/p/" + p.id },
      el("div", { class: "card-top" },
        el("span", { class: "badge " + st.cls }, st.icon + " " + st.label),
        el("span", { class: "card-cat" }, p.category)),
      el("h3", { class: "card-title" }, p.title),
      el("p", { class: "card-stmt" }, truncate(p.statement, 140)),
      el("div", { class: "card-foot" },
        el("div", { class: "syschips" }, ...systems.map((s) => el("span", { class: "syschip sys-" + s }, SYSTEM_LABEL[s] || s))),
        p.oeis ? el("span", { class: "oeis" }, p.oeis) : null)
    );
  }
  function truncate(s, n) { return s.length > n ? s.slice(0, n - 1) + "…" : s; }

  /* ---------------- detail view ---------------- */
  function renderDetail(root, id) {
    const p = PROBLEMS.find((x) => x.id === id);
    if (!p) { root.innerHTML = ""; root.appendChild(el("p", { class: "empty" }, "Problem not found. ")); root.appendChild(el("a", { href: "#/" }, "← Back")); return; }
    const st = STATUS[p.status];
    root.innerHTML = "";

    root.appendChild(el("a", { class: "back", href: "#/" }, "← All problems"));

    root.appendChild(
      el("header", { class: "detail-head" },
        el("div", { class: "detail-badges" },
          el("span", { class: "badge big " + st.cls }, st.icon + " " + st.label),
          el("span", { class: "detail-cat" }, p.category),
          p.oeis ? el("a", { class: "oeis link", href: "https://oeis.org/" + p.oeis, target: "_blank", rel: "noopener" }, "OEIS " + p.oeis) : null),
        el("h1", { class: "detail-title" }, p.title),
        el("p", { class: "detail-meta" }, [p.by, p.year].filter(Boolean).join(" · "))
      )
    );

    root.appendChild(
      el("section", { class: "panel statement-panel" },
        el("h2", { class: "panel-h" }, "Statement"),
        el("p", { class: "statement" }, p.statement),
        p.latex ? el("div", { class: "formula" }, prettyLatex(p.latex)) : null,
        el("p", { class: "story" }, p.story),
        p.source ? el("p", { class: "source" }, "Source: ", el("a", { href: p.source.url, target: "_blank", rel: "noopener" }, p.source.name)) : null)
    );

    // Proofs
    if (p.proofs && p.proofs.length) {
      root.appendChild(renderProofs(p));
    }

    // Interactive playground
    if (p.playground) {
      root.appendChild(renderPlayground(p));
    } else if (p.status !== "solved") {
      root.appendChild(el("section", { class: "panel" },
        el("h2", { class: "panel-h" }, "Give it a try"),
        el("p", { class: "muted" }, "This one has no interactive explorer yet — but the statement above is exactly what a proof would need to establish. Fame (and sometimes a $1,000,000 prize) awaits.")));
    }
  }

  function renderProofs(p) {
    const proofs = p.proofs;
    const panel = el("section", { class: "panel" }, el("h2", { class: "panel-h" }, "Formal proofs & statements"));
    const tabs = el("div", { class: "tabs" });
    const body = el("div", { class: "tab-body" });
    panel.appendChild(tabs); panel.appendChild(body);

    proofs.forEach((pr, i) => {
      const tab = el("button", { class: "tab" + (i === 0 ? " active" : "") },
        el("span", {}, SYSTEM_LABEL[pr.system] || pr.system),
        el("span", { class: "vmark " + (pr.verified ? "ok" : "no") }, pr.verified ? "✓ verified" : "unproved"));
      tab.addEventListener("click", () => {
        Array.from(tabs.children).forEach((c) => c.classList.remove("active"));
        tab.classList.add("active");
        showProof(pr);
      });
      tabs.appendChild(tab);
    });

    function showProof(pr) {
      body.innerHTML = "";
      if (pr.note) body.appendChild(el("p", { class: "proof-note" }, pr.note));

      const pre = el("pre", { class: "code" });
      pre.innerHTML = highlight(pr.code, pr.system);
      body.appendChild(pre);

      const actions = el("div", { class: "code-actions" });
      actions.appendChild(el("button", { class: "btn ghost", onclick: () => copy(pr.code) }, "⧉ Copy"));

      if (pr.system === "builtin") {
        actions.appendChild(el("button", { class: "btn primary", onclick: (e) => runBuiltin(pr.code, body, e.currentTarget) }, "▶ Verify live"));
      } else if (pr.system === "coq" && pr.runnable) {
        actions.appendChild(el("button", { class: "btn primary", onclick: (e) => runCoq(pr.code, body, e.currentTarget) }, "▶ Run in Coq"));
      } else if (pr.system === "coq") {
        actions.appendChild(el("a", { class: "btn ghost", href: COQ.externalPlayground, target: "_blank", rel: "noopener" }, "↗ Open Coq playground"));
      } else if (pr.system === "lean") {
        actions.appendChild(el("a", { class: "btn ghost", href: "https://live.lean-lang.org/", target: "_blank", rel: "noopener" }, "↗ Open Lean playground"));
      }
      body.appendChild(actions);
    }

    showProof(proofs[0]);
    return panel;
  }

  /* ---------------- runners ---------------- */
  function runBuiltin(formula, container, btn) {
    let out = $(".live-out", container);
    if (!out) { out = el("div", { class: "live-out" }); container.appendChild(out); }
    out.innerHTML = "";
    try {
      const res = LOGIC.analyze(formula);
      renderLogicResult(out, formula, res);
    } catch (e) {
      out.appendChild(el("div", { class: "verdict bad" }, "Parse error: " + e.message));
    }
  }

  function runCoq(code, container, btn) {
    let mount = $(".coq-mount", container);
    if (!mount) {
      mount = el("div", { class: "coq-mount" });
      container.appendChild(mount);
    }
    mount.innerHTML = "";
    btn.disabled = true; btn.textContent = "⏳ Loading Coq (WASM)…";
    const status = el("div", { class: "coq-status muted" }, "Fetching the Coq toolchain (~a few MB) from the CDN. First run can take a moment…");
    mount.appendChild(status);

    const area = el("textarea", { class: "coq-area", spellcheck: "false" });
    area.value = code;
    mount.appendChild(area);

    COQ.start(mount, code).then((coq) => {
      btn.disabled = false; btn.textContent = "▶ Run in Coq";
      status.className = "coq-status ok";
      status.textContent = "jsCoq loaded — use the panel above; press the ▶ / eval buttons jsCoq provides to step the proof to Qed.";
    }).catch((err) => {
      btn.disabled = false; btn.textContent = "▶ Run in Coq";
      status.className = "coq-status bad";
      status.innerHTML = "";
      status.appendChild(el("p", {}, "Couldn't load jsCoq in this environment (offline, blocked CDN, or unsupported browser)."));
      status.appendChild(el("p", {}, "The proof above is complete and self-contained — copy it and run it in a local Coq or the online playground:"));
      status.appendChild(el("a", { class: "btn ghost", href: COQ.externalPlayground, target: "_blank", rel: "noopener" }, "↗ Open Coq playground"));
    });
  }

  /* ---------------- playgrounds ---------------- */
  function renderPlayground(p) {
    const kind = p.playground.kind;
    const panel = el("section", { class: "panel playground" },
      el("h2", { class: "panel-h" }, p.status === "solved" ? "Interactive" : "🧪 Give it a try"));
    const host = el("div", { class: "pg-host" });
    panel.appendChild(host);
    switch (kind) {
      case "logic": pgLogic(host, p.playground.formula); break;
      case "goldbach": pgGoldbach(host); break;
      case "collatz": pgCollatz(host); break;
      case "twin": pgTwin(host); break;
      case "erdos-straus": pgErdosStraus(host); break;
      case "legendre": pgLegendre(host); break;
      case "mersenne": pgMersenne(host); break;
      case "sat": pgSat(host); break;
      case "coq": pgCoq(host, p.playground); break;
      default: host.appendChild(el("p", { class: "muted" }, "Explorer coming soon."));
    }
    return panel;
  }

  function pgLogic(host, initial) {
    host.appendChild(el("p", { class: "muted" },
      "Type any propositional formula. The verifier builds its full truth table and decides — this is a complete, live proof procedure for propositional logic. Operators: ",
      el("code", {}, "~ & | -> <->"), ", or words ", el("code", {}, "not and or implies iff"),
      ". Use ", el("code", {}, "|-"), " to check an argument (e.g. ", el("code", {}, "A, A -> B |- B"), ")."));
    const input = el("input", { class: "search mono", type: "text", value: initial || "A -> A" });
    const out = el("div", { class: "live-out" });
    const go = () => { out.innerHTML = ""; try { renderLogicResult(out, input.value, LOGIC.analyze(input.value)); } catch (e) { out.appendChild(el("div", { class: "verdict bad" }, "Parse error: " + e.message)); } };
    input.addEventListener("keydown", (e) => { if (e.key === "Enter") go(); });
    host.appendChild(el("div", { class: "row" }, input, el("button", { class: "btn primary", onclick: go }, "▶ Verify")));
    // examples
    const ex = ["A | ~A", "((A -> B) -> A) -> A", "~(A & B) <-> (~A | ~B)", "A, A -> B |- B", "(A -> B) & A -> B"];
    host.appendChild(el("div", { class: "examples" }, el("span", { class: "muted" }, "Try: "),
      ...ex.map((s) => el("button", { class: "chip-btn", onclick: () => { input.value = s; go(); } }, s))));
    host.appendChild(out);
    go();
  }

  function renderLogicResult(out, formula, res) {
    const vmap = { tautology: ["✓ Tautology — valid / a theorem", "good"], contradiction: ["✗ Contradiction — never true", "bad"], contingent: ["◐ Contingent — sometimes true, sometimes false", "warn"] };
    let msg = vmap[res.verdict];
    if (res.isArgument) {
      msg = res.verdict === "tautology"
        ? ["✓ Valid argument — the conclusion follows from the premises", "good"]
        : ["✗ Invalid argument — there is a counterexample (see table)", "bad"];
    }
    out.appendChild(el("div", { class: "verdict " + msg[1] }, msg[0]));
    // truth table
    if (res.vars.length) {
      const table = el("table", { class: "truth" });
      const head = el("tr", {}, ...res.vars.map((v) => el("th", {}, v)), el("th", { class: "res" }, res.isArgument ? "P₁…⇒C" : "value"));
      table.appendChild(el("thead", {}, head));
      const tb = el("tbody");
      res.rows.forEach((r) => {
        const tr = el("tr", { class: r.val ? "" : "false-row" },
          ...res.vars.map((v) => el("td", { class: r.env[v] ? "tv" : "fv" }, r.env[v] ? "T" : "F")),
          el("td", { class: "res " + (r.val ? "tv" : "fv") }, r.val ? "T" : "F"));
        tb.appendChild(tr);
      });
      table.appendChild(tb);
      out.appendChild(el("div", { class: "truth-wrap" }, table));
      out.appendChild(el("p", { class: "muted small" }, res.trues + " of " + res.total + " rows true."));
    } else {
      out.appendChild(el("p", { class: "muted small" }, "No variables — constant formula."));
    }
  }

  function bigInput(placeholder, def) {
    return el("input", { class: "search mono", type: "text", inputmode: "numeric", value: def == null ? "" : String(def), placeholder: placeholder });
  }

  function pgGoldbach(host) {
    host.appendChild(el("p", { class: "muted" }, "Pick an even number > 2. The app finds primes p, q with p + q = your number — you're verifying a case of a 280-year-old open problem."));
    const inp = bigInput("even number, e.g. 100", 100);
    const out = el("div", { class: "live-out" });
    const go = () => {
      out.innerHTML = "";
      let n;
      try { n = BigInt(inp.value.trim()); } catch { out.appendChild(bad("Enter a whole number.")); return; }
      if (n <= 2n || n % 2n !== 0n) { out.appendChild(bad("Goldbach is about even numbers greater than 2.")); return; }
      if (n > 20000000n) { out.appendChild(bad("Keep it under 20,000,000 so your browser stays snappy.")); return; }
      const pairs = NUM.goldbachAll(n, 12);
      if (!pairs.length) { out.appendChild(bad("No pair found (this would be a counterexample — and worldwide news!).")); return; }
      out.appendChild(el("div", { class: "verdict good" }, "✓ " + n + " = " + pairs[0][0] + " + " + pairs[0][1]));
      out.appendChild(el("p", { class: "muted small" }, "Other representations as p + q:"));
      out.appendChild(el("div", { class: "pairs" }, ...pairs.map((pr) => el("span", { class: "pairchip" }, pr[0] + " + " + pr[1]))));
    };
    inp.addEventListener("keydown", (e) => { if (e.key === "Enter") go(); });
    host.appendChild(el("div", { class: "row" }, inp, el("button", { class: "btn primary", onclick: go }, "▶ Find pair")));
    host.appendChild(out); go();
  }

  function pgCollatz(host) {
    host.appendChild(el("p", { class: "muted" }, "Enter a positive integer and watch its 3n+1 trajectory. Conjecturally, every path ends at 1."));
    const inp = bigInput("start, e.g. 27", 27);
    const out = el("div", { class: "live-out" });
    const go = () => {
      out.innerHTML = "";
      let n;
      try { n = BigInt(inp.value.trim()); } catch { out.appendChild(bad("Enter a whole number.")); return; }
      if (n < 1n) { out.appendChild(bad("Use a positive integer.")); return; }
      if (n > 1000000000000n) { out.appendChild(bad("That's a bit large — keep it under 10¹².")); return; }
      const r = NUM.collatz(n, 20000);
      if (!r.reachedOne) { out.appendChild(bad("Did not reach 1 within the step limit (not a disproof — just a display cap).")); return; }
      out.appendChild(el("div", { class: "verdict good" }, "✓ reached 1 in " + r.steps + " steps · peak " + r.peak));
      out.appendChild(sparkline(r.seq));
      out.appendChild(el("div", { class: "seq" }, r.seq.map(String).join("  →  ")));
    };
    inp.addEventListener("keydown", (e) => { if (e.key === "Enter") go(); });
    host.appendChild(el("div", { class: "row" }, inp, el("button", { class: "btn primary", onclick: go }, "▶ Run trajectory")));
    host.appendChild(out); go();
  }

  function sparkline(seq) {
    const w = 620, h = 120, pad = 6;
    const vals = seq.map((x) => Number(x));
    const max = Math.max(...vals), min = Math.min(...vals);
    const span = max - min || 1;
    const step = (w - 2 * pad) / Math.max(1, vals.length - 1);
    let d = "";
    vals.forEach((v, i) => {
      const x = pad + i * step;
      const y = h - pad - ((v - min) / span) * (h - 2 * pad);
      d += (i === 0 ? "M" : "L") + x.toFixed(1) + " " + y.toFixed(1) + " ";
    });
    const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
    svg.setAttribute("viewBox", "0 0 " + w + " " + h);
    svg.setAttribute("class", "spark");
    const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
    path.setAttribute("d", d.trim());
    path.setAttribute("fill", "none");
    path.setAttribute("stroke", "currentColor");
    path.setAttribute("stroke-width", "1.6");
    svg.appendChild(path);
    return svg;
  }

  function pgTwin(host) {
    host.appendChild(el("p", { class: "muted" }, "Find twin primes (p, p+2) starting at a chosen point. There are conjecturally infinitely many."));
    const inp = bigInput("start near, e.g. 1000", 1000);
    const out = el("div", { class: "live-out" });
    const go = () => {
      out.innerHTML = "";
      let n;
      try { n = BigInt(inp.value.trim()); } catch { out.appendChild(bad("Enter a whole number.")); return; }
      if (n > 100000000000n) { out.appendChild(bad("Keep it under 10¹¹.")); return; }
      const t = NUM.twinPrimes(n, 8);
      if (!t.length) { out.appendChild(bad("No twin primes found in the search window.")); return; }
      out.appendChild(el("div", { class: "verdict good" }, "✓ found " + t.length + " twin-prime pairs at/after " + n));
      out.appendChild(el("div", { class: "pairs" }, ...t.map((pr) => el("span", { class: "pairchip" }, "(" + pr[0] + ", " + pr[1] + ")"))));
    };
    inp.addEventListener("keydown", (e) => { if (e.key === "Enter") go(); });
    host.appendChild(el("div", { class: "row" }, inp, el("button", { class: "btn primary", onclick: go }, "▶ Find twins")));
    host.appendChild(out); go();
  }

  function pgErdosStraus(host) {
    host.appendChild(el("p", { class: "muted" }, "Enter n ≥ 2. The solver writes 4/n as a sum of three unit (Egyptian) fractions 1/a + 1/b + 1/c."));
    const inp = bigInput("n, e.g. 2027", 2027);
    const out = el("div", { class: "live-out" });
    const go = () => {
      out.innerHTML = "";
      const n = parseInt(inp.value.trim(), 10);
      if (!Number.isFinite(n) || n < 2) { out.appendChild(bad("Enter an integer ≥ 2.")); return; }
      if (n > 200000) { out.appendChild(bad("Keep n under 200,000 for a fast search.")); return; }
      const r = NUM.erdosStraus(n);
      if (!r) { out.appendChild(bad("No decomposition found in the search bound (not a counterexample — just the search cap).")); return; }
      out.appendChild(el("div", { class: "verdict good" }, "✓ 4/" + n + " = 1/" + r[0] + " + 1/" + r[1] + " + 1/" + r[2]));
      const check = 4 / n, got = 1 / r[0] + 1 / r[1] + 1 / r[2];
      out.appendChild(el("p", { class: "muted small" }, "Check: 4/" + n + " ≈ " + check.toPrecision(8) + ",  sum ≈ " + got.toPrecision(8)));
    };
    inp.addEventListener("keydown", (e) => { if (e.key === "Enter") go(); });
    host.appendChild(el("div", { class: "row" }, inp, el("button", { class: "btn primary", onclick: go }, "▶ Decompose")));
    host.appendChild(out); go();
  }

  function pgLegendre(host) {
    host.appendChild(el("p", { class: "muted" }, "Legendre conjectured a prime always sits between n² and (n+1)². Find one."));
    const inp = bigInput("n, e.g. 1000", 1000);
    const out = el("div", { class: "live-out" });
    const go = () => {
      out.innerHTML = "";
      let n;
      try { n = BigInt(inp.value.trim()); } catch { out.appendChild(bad("Enter a whole number.")); return; }
      if (n < 1n) { out.appendChild(bad("Use a positive integer.")); return; }
      if (n > 100000000n) { out.appendChild(bad("Keep n under 10⁸.")); return; }
      const r = NUM.legendre(n);
      if (!r.prime) { out.appendChild(bad("No prime found in (" + r.lo + ", " + r.hi + ") — this would refute Legendre!")); return; }
      out.appendChild(el("div", { class: "verdict good" }, "✓ " + r.lo + " < " + r.prime + " < " + r.hi + "  (prime)"));
    };
    inp.addEventListener("keydown", (e) => { if (e.key === "Enter") go(); });
    host.appendChild(el("div", { class: "row" }, inp, el("button", { class: "btn primary", onclick: go }, "▶ Find prime")));
    host.appendChild(out); go();
  }

  function pgMersenne(host) {
    host.appendChild(el("p", { class: "muted" }, "Test whether 2^p − 1 is a (Mersenne) prime for an exponent p. Only prime exponents have a chance."));
    const inp = bigInput("exponent p, e.g. 31", 31);
    const out = el("div", { class: "live-out" });
    const go = () => {
      out.innerHTML = "";
      let p;
      try { p = BigInt(inp.value.trim()); } catch { out.appendChild(bad("Enter a whole number.")); return; }
      if (p < 2n) { out.appendChild(bad("Use p ≥ 2.")); return; }
      if (p > 5000n) { out.appendChild(bad("Keep p under 5000 for a fast primality test.")); return; }
      const r = NUM.mersenne(p);
      if (r.isMersennePrime) out.appendChild(el("div", { class: "verdict good" }, "✓ 2^" + p + " − 1 is prime (" + r.digits + " digits)"));
      else if (!r.pPrime) out.appendChild(el("div", { class: "verdict warn" }, "◐ p = " + p + " is not prime, so 2^" + p + " − 1 is composite."));
      else out.appendChild(el("div", { class: "verdict bad" }, "✗ 2^" + p + " − 1 is composite (" + r.digits + " digits)."));
    };
    inp.addEventListener("keydown", (e) => { if (e.key === "Enter") go(); });
    host.appendChild(el("div", { class: "row" }, inp, el("button", { class: "btn primary", onclick: go }, "▶ Test")));
    host.appendChild(out); go();
  }

  function pgSat(host) {
    host.appendChild(el("p", { class: "muted" },
      "SAT — is a Boolean formula satisfiable? — is NP-complete: it sits at the heart of P vs NP. This tiny DPLL solver runs in your browser. ",
      "Enter clauses in DIMACS-ish form: one clause per line, space-separated signed variable numbers (negative = NOT)."));
    const ta = el("textarea", { class: "coq-area", spellcheck: "false", rows: "6" });
    ta.value = "1 -2\n2 3\n-1 -3\n1 3";
    const out = el("div", { class: "live-out" });
    const go = () => {
      out.innerHTML = "";
      const cnf = ta.value.split(/\n+/).map((l) => l.trim()).filter(Boolean)
        .map((l) => l.split(/\s+/).map(Number).filter((x) => x !== 0));
      if (!cnf.length) { out.appendChild(bad("Enter at least one clause.")); return; }
      try {
        const r = NUM.solveSAT(cnf);
        if (r.sat) {
          const asg = Object.keys(r.model).sort((a, b) => a - b).map((k) => "x" + k + "=" + (r.model[k] ? "T" : "F")).join("  ");
          out.appendChild(el("div", { class: "verdict good" }, "✓ SATISFIABLE  (" + r.steps + " search steps)"));
          out.appendChild(el("p", { class: "mono small" }, asg || "(any assignment works)"));
        } else {
          out.appendChild(el("div", { class: "verdict bad" }, "✗ UNSATISFIABLE  (" + r.steps + " search steps) — no assignment satisfies all clauses."));
        }
      } catch (e) { out.appendChild(bad("Error: " + e.message)); }
    };
    host.appendChild(ta);
    host.appendChild(el("div", { class: "row" }, el("button", { class: "btn primary", onclick: go }, "▶ Solve")));
    host.appendChild(out); go();
  }

  function pgCoq(host, pg) {
    host.appendChild(el("p", { class: "muted" }, pg.title || "Edit the proof and run it in Coq (loads jsCoq from a CDN on first run)."));
    const body = el("div", {});
    host.appendChild(body);
    const pre = el("pre", { class: "code" });
    pre.innerHTML = highlight(pg.code, "coq");
    body.appendChild(pre);
    const actions = el("div", { class: "code-actions" },
      el("button", { class: "btn ghost", onclick: () => copy(pg.code) }, "⧉ Copy"),
      el("button", { class: "btn primary", onclick: (e) => runCoq(pg.code, body, e.currentTarget) }, "▶ Run in Coq"),
      el("a", { class: "btn ghost", href: COQ.externalPlayground, target: "_blank", rel: "noopener" }, "↗ Coq playground"));
    body.appendChild(actions);
  }

  /* ---------------- utilities ---------------- */
  function bad(msg) { return el("div", { class: "verdict bad" }, msg); }
  function copy(text) {
    if (navigator.clipboard) navigator.clipboard.writeText(text).then(() => toast("Copied to clipboard"));
    else toast("Copy not supported in this browser");
  }
  let toastTimer = null;
  function toast(msg) {
    let t = $("#toast");
    if (!t) { t = el("div", { id: "toast" }); document.body.appendChild(t); }
    t.textContent = msg; t.classList.add("show");
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => t.classList.remove("show"), 1600);
  }

  /* ---------------- router ---------------- */
  function route() {
    const root = $("#app");
    const hash = location.hash || "#/";
    window.scrollTo(0, 0);
    if (hash.startsWith("#/p/")) renderDetail(root, decodeURIComponent(hash.slice(4)));
    else renderCatalog(root);
  }

  window.addEventListener("hashchange", route);
  window.addEventListener("DOMContentLoaded", route);
  if (document.readyState !== "loading") route();
})();
