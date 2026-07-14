/*
 * logic.js — a self-contained propositional-logic proof verifier.
 *
 * It tokenizes and parses a formula, then decides validity by building the
 * full truth table. This is a genuine, complete decision procedure for
 * propositional logic — it PROVES tautologies live, in the browser, with no
 * external dependencies. Exposed as window.MP_LOGIC.
 *
 * Accepted syntax (case-insensitive keywords, unicode welcome):
 *   negation      ~   !   ¬   not
 *   conjunction   &   &&  /\  ∧   and
 *   disjunction   |   ||  \/  ∨   or
 *   implication   ->  =>  →        implies
 *   biconditional <-> <=> ↔        iff
 *   constants     true/⊤/1   false/⊥/0
 *   variables     any identifier (A, B, p, q, foo, ...)
 *   grouping      ( ... )
 * You may also check an argument:   P, Q |- R   (turnstile |- or ⊢)
 */
(function () {
  "use strict";

  /* ---------------- tokenizer ---------------- */

  const TWO = { "->": "IMP", "=>": "IMP", "<->": "IFF", "<=>": "IFF", "&&": "AND", "||": "OR", "/\\": "AND", "\\/": "OR", "|-": "TURN" };
  const THREE = { "<->": "IFF", "<=>": "IFF" };

  function tokenize(src) {
    const toks = [];
    let i = 0;
    const s = src;
    while (i < s.length) {
      const c = s[i];
      if (/\s/.test(c)) { i++; continue; }

      // three-char operators
      const t3 = s.substr(i, 3);
      if (THREE[t3]) { toks.push({ t: THREE[t3] }); i += 3; continue; }

      // two-char operators
      const t2 = s.substr(i, 2);
      if (TWO[t2]) { toks.push({ t: TWO[t2] }); i += 2; continue; }

      // single char operators / unicode
      if (c === "(") { toks.push({ t: "LP" }); i++; continue; }
      if (c === ")") { toks.push({ t: "RP" }); i++; continue; }
      if (c === "~" || c === "!" || c === "¬") { toks.push({ t: "NOT" }); i++; continue; }
      if (c === "&" || c === "∧" || c === "·" || c === "^") { toks.push({ t: "AND" }); i++; continue; }
      if (c === "|" || c === "∨" || c === "+") { toks.push({ t: "OR" }); i++; continue; }
      if (c === "→" || c === "⊃") { toks.push({ t: "IMP" }); i++; continue; }
      if (c === "↔" || c === "≡") { toks.push({ t: "IFF" }); i++; continue; }
      if (c === "⊢") { toks.push({ t: "TURN" }); i++; continue; }
      if (c === "⊤") { toks.push({ t: "CONST", v: true }); i++; continue; }
      if (c === "⊥") { toks.push({ t: "CONST", v: false }); i++; continue; }
      if (c === ",") { toks.push({ t: "COMMA" }); i++; continue; }

      // identifiers / keywords
      if (/[A-Za-z0-9_]/.test(c)) {
        let j = i;
        while (j < s.length && /[A-Za-z0-9_]/.test(s[j])) j++;
        const word = s.slice(i, j);
        i = j;
        const lw = word.toLowerCase();
        if (lw === "not") toks.push({ t: "NOT" });
        else if (lw === "and") toks.push({ t: "AND" });
        else if (lw === "or") toks.push({ t: "OR" });
        else if (lw === "implies" || lw === "imp") toks.push({ t: "IMP" });
        else if (lw === "iff") toks.push({ t: "IFF" });
        else if (lw === "true" || word === "1" || lw === "t" && word === "T") toks.push({ t: "CONST", v: true });
        else if (lw === "false" || word === "0" || lw === "f" && word === "F") toks.push({ t: "CONST", v: false });
        else toks.push({ t: "VAR", v: word });
        continue;
      }
      throw new Error("Unexpected character: '" + c + "'");
    }
    return toks;
  }

  /* ---------------- parser (recursive descent, standard precedence) ----------------
     iff  (lowest)  <  imp  <  or  <  and  <  not  (highest)                        */

  function parse(toks) {
    let pos = 0;
    const peek = () => toks[pos];
    const next = () => toks[pos++];
    const expect = (t) => { const x = next(); if (!x || x.t !== t) throw new Error("Expected " + t); return x; };

    function parseIff() {
      let node = parseImp();
      while (peek() && peek().t === "IFF") { next(); node = { op: "IFF", l: node, r: parseImp() }; }
      return node;
    }
    function parseImp() {
      const left = parseOr();
      if (peek() && peek().t === "IMP") { next(); return { op: "IMP", l: left, r: parseImp() }; } // right-assoc
      return left;
    }
    function parseOr() {
      let node = parseAnd();
      while (peek() && peek().t === "OR") { next(); node = { op: "OR", l: node, r: parseAnd() }; }
      return node;
    }
    function parseAnd() {
      let node = parseNot();
      while (peek() && peek().t === "AND") { next(); node = { op: "AND", l: node, r: parseNot() }; }
      return node;
    }
    function parseNot() {
      if (peek() && peek().t === "NOT") { next(); return { op: "NOT", r: parseNot() }; }
      return parseAtom();
    }
    function parseAtom() {
      const tk = peek();
      if (!tk) throw new Error("Unexpected end of formula");
      if (tk.t === "LP") { next(); const e = parseIff(); expect("RP"); return e; }
      if (tk.t === "VAR") { next(); return { op: "VAR", name: tk.v }; }
      if (tk.t === "CONST") { next(); return { op: "CONST", val: tk.v }; }
      throw new Error("Unexpected token: " + tk.t);
    }

    const ast = parseIff();
    if (pos !== toks.length) throw new Error("Trailing input after formula");
    return ast;
  }

  /* ---------------- evaluation ---------------- */

  function collectVars(node, set) {
    if (!node) return set;
    if (node.op === "VAR") set.add(node.name);
    collectVars(node.l, set);
    collectVars(node.r, set);
    return set;
  }

  function evalNode(node, env) {
    switch (node.op) {
      case "VAR": return env[node.name];
      case "CONST": return node.val;
      case "NOT": return !evalNode(node.r, env);
      case "AND": return evalNode(node.l, env) && evalNode(node.r, env);
      case "OR": return evalNode(node.l, env) || evalNode(node.r, env);
      case "IMP": return !evalNode(node.l, env) || evalNode(node.r, env);
      case "IFF": return evalNode(node.l, env) === evalNode(node.r, env);
    }
    throw new Error("bad node");
  }

  /* ---------------- public API ---------------- */

  // Parse "P, Q |- R" or a single formula. Returns { ast, vars, premises }.
  function build(input) {
    const toks = tokenize(input);
    // split on TURN if present
    const turnIdx = toks.findIndex((t) => t.t === "TURN");
    if (turnIdx >= 0) {
      const before = toks.slice(0, turnIdx);
      const after = toks.slice(turnIdx + 1);
      // premises separated by commas
      const premises = [];
      let cur = [];
      for (const tk of before) {
        if (tk.t === "COMMA") { if (cur.length) premises.push(parse(cur)); cur = []; }
        else cur.push(tk);
      }
      if (cur.length) premises.push(parse(cur));
      const conclusion = parse(after);
      // Build (p1 & p2 & ...) -> conclusion
      let ant = null;
      for (const p of premises) ant = ant ? { op: "AND", l: ant, r: p } : p;
      const ast = ant ? { op: "IMP", l: ant, r: conclusion } : conclusion;
      return { ast, premises, conclusion, isArgument: true };
    }
    if (toks.some((t) => t.t === "COMMA")) throw new Error("Use `|-` (turnstile) to separate premises from the conclusion");
    return { ast: parse(toks), isArgument: false };
  }

  // Full analysis: verdict + truth table rows.
  function analyze(input) {
    const built = build(input);
    const vars = Array.from(collectVars(built.ast, new Set())).sort();
    const rows = [];
    const n = vars.length;
    const total = 1 << n;
    if (n > 12) throw new Error("Too many variables (" + n + "). Keep it to 12 or fewer.");
    let trues = 0;
    for (let mask = 0; mask < total; mask++) {
      const env = {};
      for (let b = 0; b < n; b++) env[vars[b]] = Boolean(mask & (1 << (n - 1 - b)));
      const val = evalNode(built.ast, env);
      if (val) trues++;
      rows.push({ env, val });
    }
    let verdict;
    if (n === 0) verdict = built.ast.op === "CONST" ? (built.ast.val ? "tautology" : "contradiction") : (evalNode(built.ast, {}) ? "tautology" : "contradiction");
    else if (trues === total) verdict = "tautology";
    else if (trues === 0) verdict = "contradiction";
    else verdict = "contingent";

    return { vars, rows, verdict, isArgument: built.isArgument, total, trues };
  }

  window.MP_LOGIC = { tokenize, parse, build, analyze, evalNode, collectVars };
})();
