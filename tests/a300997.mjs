#!/usr/bin/env node
/*
 * Independent finite corroboration of OEIS A300997 (the mass-splitting CA
 * stabilization time). Reproduces the sequence and checks DeepMind AlphaProof's
 * lemma  a(n+1) - a(n) ∈ {1,2}  for n = 1..N. This is finite evidence, NOT a
 * proof — the proof is DeepMind's (math/materials/a300997/).
 */
import { readFileSync } from "node:fs";
import { resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import vm from "node:vm";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const sandbox = { window: {}, BigInt, Math, console };
vm.createContext(sandbox);
vm.runInContext(readFileSync(resolve(root, "math/assets/js/numtools.js"), "utf8"), sandbox, { filename: "numtools.js" });
const N = sandbox.window.MP_NUM;

const RANGE = 600;
const r = N.a300997_check(RANGE);
const head = r.values.slice(0, 16).join(",");
const expected = "0,1,3,4,6,8,10,11,13,15,17,19,21,23,24,26";

let fail = 0;
if (head !== expected) { fail++; console.log(`  FAIL a(1..16): got ${head}`); }
else console.log(`  ok   a(1..16) = ${head}`);
if (r.gapViolations.length !== 0) { fail++; console.log(`  FAIL gap lemma: ${r.gapViolations.length} violation(s)`, r.gapViolations.slice(0, 5)); }
else console.log(`  ok   gap lemma a(n+1)-a(n) ∈ {1,2} for n=1..${RANGE} (0 violations)`);

console.log(`\n${fail === 0 ? "A300997 finite corroboration passed ✓ (proof is DeepMind AlphaProof's)" : fail + " FAILURE(S) ✗"}`);
process.exit(fail === 0 ? 0 : 1);
