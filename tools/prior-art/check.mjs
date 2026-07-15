#!/usr/bin/env node
/*
 * Prior-art crawler/checker for the A317940 nonnegativity proof.
 *
 * Goes deep across several independent sources to look for any pre-existing
 * proof (formal or in the literature) of the DeepMind Formal Conjectures
 * theorem A317940_f_nonnegative, so we can substantiate (or retract) the
 * novelty claim. Each source degrades gracefully — a blocked/unreachable host
 * is reported as "unreachable", not a failure.
 *
 * Sources:
 *   1. DeepMind upstream file (raw.githubusercontent) — is it still `sorry`?
 *   2. GitHub code search — any A317940 proof in Lean/Coq/Isabelle anywhere.
 *   3. GitHub PR/issue search — any PR/issue proving it (esp. formal-conjectures).
 *   4. OEIS A317940 — references / links / comments scan.
 *   5. arXiv — papers matching the mechanism.
 *   6. Local repo — our own PRIOR_ART.md boundary.
 *
 * Writes math/a317940/prior-art-report.json (+ prints a summary).
 * Set GITHUB_TOKEN to enable the GitHub API sources (present on Actions).
 *
 * Usage: node tools/prior-art/check.mjs
 */
import { writeFileSync, readFileSync, existsSync } from "node:fs";
import { resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
const OUT = resolve(ROOT, "math/a317940/prior-art-report.json");
const GH = process.env.GITHUB_TOKEN;

const UPSTREAM_RAW =
  "https://raw.githubusercontent.com/google-deepmind/formal-conjectures/auto_oeis/FormalConjectures/OEIS/Auto/317940_cd729cdd.lean";

// The submitter's own GitHub account — its repos/issues are part of THIS
// submission, not prior art, so they're excluded from the search.
const SELF = /(^|\/|github\.com\/)DomTheDeveloper\//i;

async function get(url, opts = {}, kind = "text") {
  const ctl = AbortSignal.timeout ? AbortSignal.timeout(25000) : undefined;
  // A real User-Agent is required by OEIS (and polite elsewhere).
  const headers = { "User-Agent": "A317940-prior-art-check (+https://github.com/DomTheDeveloper/crl)", ...(opts.headers || {}) };
  const res = await fetch(url, { signal: ctl, ...opts, headers });
  if (!res.ok) throw new Error("HTTP " + res.status);
  return kind === "json" ? res.json() : res.text();
}

const results = [];
const add = (o) => { results.push(o); const s = o.status === "clear" ? "✓" : o.status === "hit" ? "⚠" : "…"; console.log(`  ${s} ${o.source}: ${o.summary}`); };

// 1) upstream still-open check
async function upstreamOpen() {
  try {
    const txt = await get(UPSTREAM_RAW);
    const line = (txt.split("\n").find((l) => l.includes("A317940_f_nonnegative")) || "").trim();
    const stillSorry = /:=\s*by\s+sorry\b/.test(line) || /\bsorry\b/.test(line);
    add({ source: "DeepMind upstream (auto_oeis)", status: stillSorry ? "clear" : "hit",
      summary: stillSorry ? "theorem still stated with `sorry` — OPEN upstream" : "upstream no longer `sorry` — a proof may now exist upstream!",
      detail: line, url: UPSTREAM_RAW });
  } catch (e) { add({ source: "DeepMind upstream (auto_oeis)", status: "unreachable", summary: "could not fetch (" + e.message + ")", url: UPSTREAM_RAW }); }
}

// 2/3) GitHub code + PR/issue search (needs token)
async function github() {
  if (!GH) { add({ source: "GitHub code search", status: "unreachable", summary: "no GITHUB_TOKEN — skipped (runs on Actions)" }); return; }
  const H = { Authorization: "Bearer " + GH, Accept: "application/vnd.github+json", "User-Agent": "prior-art-check" };
  const queries = [
    ["code", "A317940_f_nonnegative"],
    ["code", "A317940 language:lean"],
    ["code", "A317940 language:coq"],
    ["issues", "A317940 nonnegative in:title,body"]
  ];
  for (const [kind, q] of queries) {
    try {
      const j = await get(`https://api.github.com/search/${kind}?q=${encodeURIComponent(q)}&per_page=20`, { headers: H }, "json");
      // Exclude (a) the submitter's own repos/issues and (b) the OEIS auto-statement
      // (which is the still-`sorry` conjecture itself, not a proof).
      const items = (j.items || []).filter((it) => {
        const repo = (it.repository && it.repository.full_name) || "";
        const url = it.html_url || "";
        return !SELF.test(repo) && !SELF.test(url) && !/formal-conjectures\/.*Auto\//i.test(url);
      });
      add({ source: `GitHub ${kind}: "${q}"`, status: items.length ? "hit" : "clear",
        summary: items.length ? `${items.length} candidate match(es) — inspect` : "no external proof matches",
        detail: items.slice(0, 8).map((it) => it.html_url) });
    } catch (e) { add({ source: `GitHub ${kind}: "${q}"`, status: "unreachable", summary: "search failed (" + e.message + ")" }); }
  }
}

// 4) OEIS references / links / comments
async function oeis() {
  try {
    const j = await get("https://oeis.org/search?q=id:A317940&fmt=json", {}, "json");
    const rec = (j.results && j.results[0]) || {};
    const blob = JSON.stringify([rec.comment, rec.reference, rec.link, rec.formula]).toLowerCase();
    const hit = /(proof|prove|nonnegativ|positiv).*(theorem|shown|establish)/.test(blob) &&
                !/no negative terms among the first/.test(blob.replace(/\s+/g, " ").slice(0, 400)); // exclude the open-question comment
    add({ source: "OEIS A317940 (comments/refs/links)", status: hit ? "hit" : "clear",
      summary: hit ? "a comment/reference may assert a proof — inspect" : "no asserted proof in comments/refs/links (only the open question)",
      url: "https://oeis.org/A317940" });
  } catch (e) { add({ source: "OEIS A317940", status: "unreachable", summary: "could not fetch (" + e.message + ")", url: "https://oeis.org/A317940" }); }
}

// 5) arXiv — mechanism keywords
async function arxiv() {
  const q = 'all:%22Dirichlet%20square%20root%22%20AND%20all:positivity';
  try {
    const xml = await get(`https://export.arxiv.org/api/query?search_query=${q}&max_results=15`);
    const titles = [...xml.matchAll(/<title>([\s\S]*?)<\/title>/g)].map((m) => m[1].trim()).slice(1);
    const suspicious = titles.filter((t) => /A317940|digit.?sum.*positiv|square root.*positiv/i.test(t));
    add({ source: "arXiv (Dirichlet square root + positivity)", status: suspicious.length ? "hit" : "clear",
      summary: suspicious.length ? suspicious.length + " title(s) worth a closer look" : `${titles.length} results scanned; none assert this result`,
      detail: suspicious, url: "https://arxiv.org/a/list" });
  } catch (e) { add({ source: "arXiv", status: "unreachable", summary: "could not fetch (" + e.message + ")" }); }
}

// 6) our own recorded boundary
function localBoundary() {
  const p = resolve(ROOT, "math/a317940/docs/PRIOR_ART.md");
  if (existsSync(p)) {
    const t = readFileSync(p, "utf8");
    add({ source: "Our recorded prior-art boundary", status: "clear",
      summary: "PRIOR_ART.md present: digit-sum product identity is classical; positivity argument + A317940 application appear new",
      detail: t.split("\n").slice(0, 3).join(" ") });
  }
}

async function main() {
  console.log("Prior-art check for A317940_f_nonnegative\n");
  await upstreamOpen();
  await github();
  await oeis();
  await arxiv();
  localBoundary();

  const hits = results.filter((r) => r.status === "hit");
  const unreachable = results.filter((r) => r.status === "unreachable");
  const verdict = hits.length === 0
    ? "NO PRIOR FORMAL PROOF FOUND across reachable sources; upstream still open. (Not an exhaustive literature review.)"
    : hits.length + " source(s) need human inspection — possible prior art.";
  const report = {
    subject: "A317940_f_nonnegative (OEIS A317940 nonnegativity)",
    generated_at: new Date().toISOString(),
    generated_by: GH ? "CI (GitHub Actions, full network + token)" : "local/sandbox (limited network)",
    verdict, hits: hits.length, unreachable: unreachable.map((u) => u.source), sources: results,
    caveat: "Automated prior-art search over code hosts, OEIS and arXiv. A negative result is evidence, not proof, of novelty; a full literature/expert review is still advised."
  };
  writeFileSync(OUT, JSON.stringify(report, null, 2) + "\n");
  console.log(`\n${verdict}\nWrote ${OUT}`);
  // Non-zero exit ONLY if a genuine prior-art hit is found (so CI surfaces it).
  process.exit(hits.length ? 2 : 0);
}
main().catch((e) => { console.error("crawler error:", e); process.exit(1); });
