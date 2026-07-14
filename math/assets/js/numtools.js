/*
 * numtools.js — small, exact number-theory helpers powering the interactive
 * "give it a try" explorers for the OPEN problems. Everything runs client-side.
 * Exposed as window.MP_NUM.
 */
(function () {
  "use strict";

  // Deterministic Miller–Rabin, correct for all n < 3.3 * 10^24 with these bases.
  function isPrime(n) {
    n = BigInt(n);
    if (n < 2n) return false;
    for (const p of [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n]) {
      if (n % p === 0n) return n === p;
    }
    let d = n - 1n, r = 0n;
    while (d % 2n === 0n) { d /= 2n; r++; }
    const bases = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n];
    const powmod = (a, e, m) => {
      let res = 1n; a %= m;
      while (e > 0n) { if (e & 1n) res = (res * a) % m; a = (a * a) % m; e >>= 1n; }
      return res;
    };
    for (const a of bases) {
      let x = powmod(a % n, d, n);
      if (x === 1n || x === n - 1n) continue;
      let cont = false;
      for (let i = 0n; i < r - 1n; i++) {
        x = (x * x) % n;
        if (x === n - 1n) { cont = true; break; }
      }
      if (!cont) return false;
    }
    return true;
  }

  // Goldbach: return the prime pair (p, q) with p smallest, p + q = n, or null.
  function goldbach(n) {
    n = BigInt(n);
    if (n <= 2n || n % 2n !== 0n) return null;
    for (let p = 2n; p <= n / 2n; p++) {
      if (isPrime(p) && isPrime(n - p)) return [p, n - p];
    }
    return null;
  }

  // All Goldbach pairs (for the "how many ways" count), capped for display.
  function goldbachAll(n, cap) {
    n = BigInt(n);
    const out = [];
    if (n <= 2n || n % 2n !== 0n) return out;
    for (let p = 2n; p <= n / 2n; p++) {
      if (isPrime(p) && isPrime(n - p)) { out.push([p, n - p]); if (out.length >= (cap || 50)) break; }
    }
    return out;
  }

  // Collatz trajectory from n (as an array of BigInt), plus stats.
  function collatz(n, maxSteps) {
    n = BigInt(n);
    const seq = [n];
    let max = n, steps = 0n;
    const limit = maxSteps || 100000;
    while (n !== 1n && seq.length <= limit) {
      n = (n % 2n === 0n) ? n / 2n : 3n * n + 1n;
      if (n > max) max = n;
      seq.push(n);
      steps++;
    }
    return { seq, steps: Number(steps), peak: max, reachedOne: n === 1n };
  }

  // Find twin-prime pairs (p, p+2) at or after start, up to `count` of them.
  function twinPrimes(start, count) {
    start = BigInt(start);
    if (start < 3n) start = 3n;
    const out = [];
    let p = start;
    let guard = 0;
    while (out.length < (count || 5) && guard < 5_000_00) {
      if (isPrime(p) && isPrime(p + 2n)) out.push([p, p + 2n]);
      p++; guard++;
    }
    return out;
  }

  // Erdős–Straus: find (a,b,c) with 4/n = 1/a + 1/b + 1/c.
  function erdosStraus(n) {
    n = Number(n);
    if (n < 2) return null;
    // Search a, then solve 4/n - 1/a = (4a - n)/(n a) = 1/b + 1/c.
    for (let a = Math.ceil(n / 4) || 1; a <= n * n; a++) {
      const numA = 4 * a - n;          // numerator of (4/n - 1/a)
      if (numA <= 0) continue;
      const denA = n * a;              // 4/n - 1/a = numA/denA ; want = 1/b + 1/c
      // 1/b + 1/c = numA/denA. Try b from ceil(denA/numA).
      const bStart = Math.ceil(denA / numA);
      for (let b = Math.max(a, bStart); b <= 2 * denA / numA + 2 && b < 4_000_000; b++) {
        // 1/c = numA/denA - 1/b = (numA*b - denA)/(denA*b)
        const cNum = numA * b - denA;
        if (cNum <= 0) continue;
        const cDen = denA * b;
        if (cDen % cNum === 0) {
          const c = cDen / cNum;
          if (c >= b && Number.isInteger(c)) return [a, b, c];
        }
      }
    }
    return null;
  }

  // Legendre: smallest prime strictly between n^2 and (n+1)^2.
  function legendre(n) {
    n = BigInt(n);
    const lo = n * n, hi = (n + 1n) * (n + 1n);
    for (let p = lo + 1n; p < hi; p++) if (isPrime(p)) return { prime: p, lo, hi };
    return { prime: null, lo, hi };
  }

  // Is 2^p - 1 a Mersenne prime? (p must be prime for it to have a chance.)
  function mersenne(p) {
    p = BigInt(p);
    const m = (1n << p) - 1n;
    return { exponent: p, value: m, pPrime: isPrime(p), isMersennePrime: isPrime(p) && isPrime(m), digits: m.toString().length };
  }

  /* ---------------- tiny SAT solver (DPLL) for the P-vs-NP demo ----------------
     A CNF is an array of clauses; each clause is an array of signed integers,
     e.g. [[1, -2], [2, 3]] means (x1 ∨ ¬x2) ∧ (x2 ∨ x3).                        */
  function solveSAT(cnf) {
    const assign = {};
    let steps = 0;
    function dpll(clauses) {
      steps++;
      // unit propagation
      let changed = true;
      const local = clauses.map((c) => c.slice());
      const model = Object.assign({}, assign);
      while (changed) {
        changed = false;
        for (const clause of local) {
          const unresolved = clause.filter((lit) => model[Math.abs(lit)] === undefined);
          const satisfied = clause.some((lit) => model[Math.abs(lit)] === (lit > 0));
          if (satisfied) continue;
          if (unresolved.length === 0) return null;      // conflict
          if (unresolved.length === 1) {
            const lit = unresolved[0];
            model[Math.abs(lit)] = lit > 0;
            changed = true;
          }
        }
      }
      // check all satisfied
      const allSat = local.every((c) => c.some((lit) => model[Math.abs(lit)] === (lit > 0)));
      if (allSat) return model;
      // pick an unassigned variable
      let pick = null;
      for (const c of local) for (const lit of c) if (model[Math.abs(lit)] === undefined) { pick = Math.abs(lit); break; }
      if (pick === null) return allSat ? model : null;
      for (const val of [true, false]) {
        const saved = Object.assign({}, assign);
        Object.assign(assign, model);
        assign[pick] = val;
        const res = dpll(clauses);
        if (res) return res;
        for (const k of Object.keys(assign)) delete assign[k];
        Object.assign(assign, saved);
      }
      return null;
    }
    const res = dpll(cnf);
    return { sat: !!res, model: res, steps };
  }

  window.MP_NUM = {
    isPrime, goldbach, goldbachAll, collatz, twinPrimes,
    erdosStraus, legendre, mersenne, solveSAT
  };
})();
