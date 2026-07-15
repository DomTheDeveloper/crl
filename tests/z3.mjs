#!/usr/bin/env node
/*
 * Verify the Z3 SMT solver (WebAssembly build, `z3-solver`) actually decides
 * satisfiability. Exits non-zero on any wrong answer, to gate CI.
 * Requires: npm i z3-solver
 */
import { init } from "z3-solver";

const { Context } = await init();
const Z = Context("main");
let fail = 0;
const eq = (name, got, want) => {
  const ok = got === want;
  if (!ok) { fail++; console.log(`  FAIL ${name}: got ${got} want ${want}`); }
  else console.log(`  ok   ${name}: ${got}`);
};

// 1) A satisfiable integer system.
{
  const x = Z.Int.const("x"), y = Z.Int.const("y");
  const s = new Z.Solver();
  s.add(x.gt(2), y.lt(10), x.add(2).mul(y).eq(7));
  eq("(x>2, y<10, (x+2)*y=7) is sat", await s.check(), "sat");
}
// 2) A contradiction is unsat.
{
  const p = Z.Bool.const("p");
  const s = new Z.Solver();
  s.add(p.and(p.not()));
  eq("(p and not p) is unsat", await s.check(), "unsat");
}
// 3) Pigeonhole-ish: no integer strictly between 0 and 1.
{
  const n = Z.Int.const("n");
  const s = new Z.Solver();
  s.add(n.gt(0), n.lt(1));
  eq("(0 < n < 1 over integers) is unsat", await s.check(), "unsat");
}
// 4) De Morgan as an SMT tautology: negation of (¬(a∧b) ↔ (¬a∨¬b)) is unsat.
{
  const a = Z.Bool.const("a"), b = Z.Bool.const("b");
  const lhs = a.and(b).not(), rhs = a.not().or(b.not());
  const s = new Z.Solver();
  s.add(lhs.eq(rhs).not());
  eq("De Morgan is valid (negation unsat)", await s.check(), "unsat");
}

console.log(`\n${fail === 0 ? "All Z3 checks passed ✓" : fail + " FAILURE(S) ✗"}`);
process.exit(fail === 0 ? 0 : 1);
