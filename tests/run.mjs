#!/usr/bin/env node
/*
 * Verify the pure-JS "solvers" that back the interactive site:
 *   - the propositional-logic engine (logic.js)
 *   - the number-theory explorers (numtools.js), including the exact A317940
 *     rational computation used for the nonnegativity conjecture.
 * Exits non-zero on any failure, to gate CI.
 */
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import vm from "node:vm";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const sandbox = { window: {}, WebAssembly, BigInt, Math, console };
vm.createContext(sandbox);
for (const f of ["math/assets/js/logic.js", "math/assets/js/numtools.js"]) {
  vm.runInContext(readFileSync(resolve(root, f), "utf8"), sandbox, { filename: f });
}
const L = sandbox.window.MP_LOGIC, N = sandbox.window.MP_NUM;

let fail = 0;
const eq = (name, got, want) => {
  const ok = JSON.stringify(got) === JSON.stringify(want);
  if (!ok) { fail++; console.log(`  FAIL ${name}: got ${JSON.stringify(got)} want ${JSON.stringify(want)}`); }
  else console.log(`  ok   ${name}`);
};

console.log("Propositional logic:");
eq("excluded middle", L.analyze("A | ~A").verdict, "tautology");
eq("de morgan", L.analyze("~(A & B) <-> (~A | ~B)").verdict, "tautology");
eq("peirce", L.analyze("((A -> B) -> A) -> A").verdict, "tautology");
eq("contraposition", L.analyze("(A -> B) <-> (~B -> ~A)").verdict, "tautology");
eq("modus ponens", L.analyze("A, A -> B |- B").verdict, "tautology");
eq("invalid arg", L.analyze("A -> B, B |- A").verdict, "contingent");
eq("contradiction", L.analyze("A & ~A").verdict, "contradiction");

console.log("Number theory:");
eq("prime 97", N.isPrime(97), true);
eq("composite 91", N.isPrime(91), false);
eq("goldbach 100", N.goldbach(100).map(String), ["3", "97"]);
eq("collatz 27 steps", N.collatz(27).steps, 111);
eq("twin near 10", N.twinPrimes(10, 2).map((p) => p.map(String)), [["11", "13"], ["17", "19"]]);
eq("mersenne 31 prime", N.mersenne(31).isMersennePrime, true);
eq("mersenne 11 composite", N.mersenne(11).isMersennePrime, false);
eq("sat", N.solveSAT([[1, -2], [2, 3], [-1, -3], [1, 3]]).sat, true);
eq("unsat", N.solveSAT([[1], [-1]]).sat, false);

console.log("A317940 (exact rational Dirichlet square root):");
const S = N.ratToString;
eq("f(4)=7/2", S(N.a317940_f(4)), "7/2");
eq("f(16)=427/8", S(N.a317940_f(16)), "427/8");
eq("f(1024)", S(N.a317940_f(1024)), "13613977/256");
eq("f(65536)", S(N.a317940_f(65536)), "28828278565699/32768");
// anchors: A317940(n) = |numerator(f(n))|
for (const [n, a] of [[1, 1], [2, 1], [3, 1], [4, 7]]) {
  const r = N.a317940_f(n); const num = (r.n < 0n ? -r.n : r.n).toString();
  eq(`A317940(${n})=${a}`, num, String(a));
}
// positivity sweep — the conjecture, checked to 20000
let neg = 0;
for (let n = 1; n <= 20000; n++) if (!N.ratPositive(N.a317940_f(n))) neg++;
eq("positivity 1..20000 (0 non-positive)", neg, 0);

console.log(`\n${fail === 0 ? "All solver checks passed ✓" : fail + " FAILURE(S) ✗"}`);
process.exit(fail === 0 ? 0 : 1);
