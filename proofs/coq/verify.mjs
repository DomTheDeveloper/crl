#!/usr/bin/env node
/*
 * Verify every Coq proof in proofs/coq/*.v using the jsCoq (Coq-in-WASM) CLI.
 * Exits non-zero if any proof fails to compile, so it can gate CI.
 *
 * Requires: npm i jscoq@0.17.1   (provides node_modules/jscoq/dist-cli/cli.cjs)
 * Usage:    node proofs/coq/verify.mjs
 */
import { readdirSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const CLI = resolve(here, "../../node_modules/jscoq/dist-cli/cli.cjs");
const files = readdirSync(here).filter((f) => f.endsWith(".v")).sort();

let failures = 0;
console.log(`Verifying ${files.length} Coq proof(s) with jsCoq CLI\n`);
for (const f of files) {
  const path = join(here, f);
  const res = spawnSync(
    process.execPath,
    [CLI, "run", "--require-pkg", "coq-arith", "-l", path],
    { encoding: "utf8", timeout: 300000, maxBuffer: 1 << 26 }
  );
  const out = (res.stdout || "") + (res.stderr || "");
  const errs = out.split("\n").filter((l) => /^\[Error\]|^\[Exception\]/.test(l));
  if (errs.length === 0 && res.status === 0) {
    console.log(`  PASS  ${f}`);
  } else {
    failures++;
    console.log(`  FAIL  ${f}`);
    errs.slice(0, 4).forEach((e) => console.log(`        ${e}`));
    if (errs.length === 0) console.log(`        (exit ${res.status}) ${(res.error && res.error.message) || ""}`);
  }
}
console.log(`\n${failures === 0 ? "All Coq proofs verified ✓" : failures + " Coq proof(s) FAILED ✗"}`);
process.exit(failures === 0 ? 0 : 1);
