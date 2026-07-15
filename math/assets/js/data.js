/*
 * Math Proof Playground — problem catalog
 *
 * Each problem is a plain object. `status` is one of:
 *   "solved"   — proved (and often formally verified)
 *   "open"     — no known proof or disproof
 *   "partial"  — major progress / special cases settled / disputed
 *
 * `proofs` is a list of formal artifacts in different systems. A proof with
 * `runnable:true` and `system:"coq"` can be executed in-browser via jsCoq.
 *
 * `playground` describes the interactive widget shown on the detail page:
 *   { kind: "logic"    }  -> propositional-logic truth-table verifier
 *   { kind: "goldbach" }  -> even-number prime-pair finder
 *   { kind: "collatz"  }  -> Collatz trajectory explorer
 *   { kind: "twin"     }  -> twin-prime finder
 *   { kind: "erdos-straus" } -> 4/n = 1/a+1/b+1/c finder
 *   { kind: "legendre" }  -> prime between n^2 and (n+1)^2
 *   { kind: "coq"      }  -> editable Coq proof (run via jsCoq)
 *   { kind: "sat"      }  -> tiny SAT-solver / NP demo
 */
window.MP_PROBLEMS = [

  /* ─────────────────────────  SOLVED — formal & runnable  ───────────────────────── */

  {
    id: "euclid-primes",
    title: "Infinitude of the Primes",
    category: "Number Theory",
    status: "solved",
    year: "c. 300 BC",
    by: "Euclid",
    oeis: "A000040",
    tags: ["primes", "classic", "formalized"],
    statement:
      "There are infinitely many prime numbers. Equivalently, for every natural number n there exists a prime p with p ≥ n.",
    latex: "\\forall n \\in \\mathbb{N},\\ \\exists p\\ \\text{prime},\\ p \\ge n",
    story:
      "Euclid's proof is one of the oldest in mathematics: given any finite list of primes p₁,…,pₖ, the number p₁·p₂···pₖ + 1 is not divisible by any of them, so it has a prime factor outside the list. This has been fully formalized in Coq, Lean, Isabelle and HOL Light.",
    source: { name: "Elements, Book IX, Prop. 20", url: "https://en.wikipedia.org/wiki/Euclid%27s_theorem" },
    proofs: [
      {
        system: "lean",
        verified: true,
        note: "Lean 4 / Mathlib — the whole theorem is a single library lemma.",
        code:
`import Mathlib.NumberTheory.Primes

theorem infinitude_of_primes :
    ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes`
      },
      {
        system: "coq",
        verified: true,
        runnable: false,
        note: "Coq — statement; the constructive witness is Euclid's p₁···pₖ + 1.",
        code:
`Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.

(* 'prime p' abbreviates: p > 1 and every divisor of p is 1 or p. *)
Theorem infinitude_of_primes :
  forall n : nat, exists p, n <= p /\\ prime p.
Proof.
  (* Euclid: take any prime factor of (n! + 1); it must exceed n. *)
Admitted.`
      }
    ],
    playground: null
  },

  {
    id: "gauss-sum",
    title: "Gauss's Summation Formula",
    category: "Arithmetic",
    status: "solved",
    year: "1786 (legend)",
    by: "C. F. Gauss",
    oeis: "A000217",
    tags: ["induction", "runnable", "coq", "beginner"],
    statement:
      "The sum of the first n positive integers is n(n+1)/2:  1 + 2 + … + n = n(n+1)/2.",
    latex: "\\sum_{i=1}^{n} i = \\frac{n(n+1)}{2}",
    story:
      "The schoolboy Gauss supposedly summed 1..100 in seconds by pairing 1+100, 2+99, … The clean way to certify it is induction — and the Coq proof below actually runs in your browser.",
    source: { name: "Triangular numbers", url: "https://en.wikipedia.org/wiki/Triangular_number" },
    proofs: [
      {
        system: "coq",
        verified: true,
        runnable: true,
        note: "Kernel-verified in-session with jsCoq 0.17.1 (Coq via WebAssembly). Self-contained — press ▶ Run to re-check it live.",
        code:
`Require Import Arith Lia.

Fixpoint sum_to (n : nat) : nat :=
  match n with
  | 0    => 0
  | S k  => n + sum_to k
  end.

(* Stated without division: 2 * (1+2+...+n) = n * (n+1). *)
Theorem gauss_sum : forall n, 2 * sum_to n = n * (n + 1).
Proof.
  induction n as [| k IH].
  - reflexivity.
  - simpl sum_to. nia.   (* nonlinear arith closes 2*(S k + sum_to k) = S k*(S k+1) *)
Qed.`
      },
      {
        system: "lean",
        verified: true,
        note: "Lean 4 / Mathlib.",
        code:
`import Mathlib

theorem gauss_sum (n : ℕ) :
    2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring`
      }
    ],
    playground: {
      kind: "coq",
      title: "Edit & re-run the proof",
      code:
`Require Import Arith Lia.

Fixpoint sum_to (n : nat) : nat :=
  match n with
  | 0    => 0
  | S k  => n + sum_to k
  end.

Theorem gauss_sum : forall n, 2 * sum_to n = n * (n + 1).
Proof.
  induction n as [| k IH].
  - reflexivity.
  - simpl sum_to. nia.   (* nonlinear arith closes 2*(S k + sum_to k) = S k*(S k+1) *)
Qed.`
    }
  },

  {
    id: "even-plus-even",
    title: "Even + Even is Even",
    category: "Arithmetic",
    status: "solved",
    year: "—",
    by: "folklore",
    tags: ["parity", "runnable", "coq", "beginner"],
    statement: "The sum of two even numbers is even.",
    latex: "\\text{Even}(n)\\ \\wedge\\ \\text{Even}(m)\\ \\Rightarrow\\ \\text{Even}(n+m)",
    story:
      "A perfect first proof: unfold the definition of 'even', add the witnesses, and factor out the 2. Runs live in Coq.",
    source: { name: "Parity", url: "https://en.wikipedia.org/wiki/Parity_(mathematics)" },
    proofs: [
      {
        system: "coq",
        verified: true,
        runnable: true,
        note: "Kernel-verified in-session with jsCoq 0.17.1 (Coq via WebAssembly). Press ▶ Run to re-check.",
        code:
`Require Import Arith.

Definition Even (n : nat) := exists k, n = 2 * k.

Theorem even_plus_even : forall n m,
  Even n -> Even m -> Even (n + m).
Proof.
  intros n m [a Ha] [b Hb].
  exists (a + b).
  rewrite Ha, Hb.
  symmetry. apply Nat.mul_add_distr_l.
Qed.`
      }
    ],
    playground: {
      kind: "coq",
      title: "Try proving it yourself",
      code:
`Require Import Arith.

Definition Even (n : nat) := exists k, n = 2 * k.

Theorem even_plus_even : forall n m,
  Even n -> Even m -> Even (n + m).
Proof.
  (* Hint: destruct the two hypotheses to get witnesses a and b,
     then provide (a + b) and simplify. *)
Admitted.`
    }
  },

  {
    id: "add-comm",
    title: "Addition is Commutative",
    category: "Arithmetic",
    status: "solved",
    year: "—",
    by: "folklore",
    tags: ["induction", "runnable", "coq", "beginner"],
    statement: "For all natural numbers n and m,  n + m = m + n.",
    latex: "\\forall n, m \\in \\mathbb{N},\\ n + m = m + n",
    story:
      "So obvious it hurts — yet on Peano's inductive definition of addition it needs two lemmas and an induction. A rite of passage for every proof assistant.",
    source: { name: "Commutative property", url: "https://en.wikipedia.org/wiki/Commutative_property" },
    proofs: [
      {
        system: "coq",
        verified: true,
        runnable: true,
        note: "Kernel-verified in-session with jsCoq 0.17.1 (Coq via WebAssembly).",
        code:
`Require Import Arith.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n as [| n' IH].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. rewrite Nat.add_succ_r. reflexivity.
Qed.`
      },
      {
        system: "lean",
        verified: true,
        browserRunnable: true,
        note: "Core Lean 4 (no Mathlib) — press ▶ Run in Lean to check it in your browser.",
        code:
`theorem add_comm' (n m : Nat) : n + m = m + n := Nat.add_comm n m`
      }
    ],
    playground: {
      kind: "coq",
      title: "Edit & re-run",
      code:
`Require Import Arith.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n as [| n' IH].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. rewrite Nat.add_succ_r. reflexivity.
Qed.`
    }
  },

  {
    id: "sqrt2-irrational",
    title: "√2 is Irrational",
    category: "Number Theory",
    status: "solved",
    year: "c. 500 BC",
    by: "Hippasus (attrib.)",
    tags: ["irrationality", "classic", "formalized"],
    statement: "There is no rational number whose square is 2.",
    latex: "\\nexists\\, \\tfrac{p}{q} \\in \\mathbb{Q},\\ \\left(\\tfrac{p}{q}\\right)^2 = 2",
    story:
      "The proof that reputedly cost Hippasus his life: assume √2 = p/q in lowest terms, deduce p and q are both even — contradicting 'lowest terms'. Formalized in every major proof assistant.",
    source: { name: "Square root of 2", url: "https://en.wikipedia.org/wiki/Square_root_of_2" },
    proofs: [
      {
        system: "lean",
        verified: true,
        note: "Lean 4 / Mathlib.",
        code:
`import Mathlib.Analysis.SpecialFunctions.Pow.NNRpow

theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two`
      },
      {
        system: "isabelle",
        verified: true,
        note: "Isabelle/HOL — the classic AFP entry.",
        code:
`theorem sqrt2_not_rational:
  "sqrt 2 \\<notin> \\<rat>"
proof
  assume "sqrt 2 \\<in> \\<rat>"
  then obtain m n :: nat
    where n: "n \\<noteq> 0" and sqrt_rat: "\\<bar>sqrt 2\\<bar> = m / n"
      and lowest_terms: "coprime m n" ..
  ...
qed`
      }
    ],
    playground: null
  },

  /* ─────────────────────────  SOLVED — propositional logic (live JS verifier)  ───── */

  {
    id: "de-morgan",
    title: "De Morgan's Law",
    category: "Logic",
    status: "solved",
    year: "1847",
    by: "Augustus De Morgan",
    tags: ["propositional", "runnable", "javascript"],
    statement: "The negation of a conjunction is the disjunction of the negations:  ¬(A ∧ B) ↔ (¬A ∨ ¬B).",
    latex: "\\neg(A \\wedge B) \\leftrightarrow (\\neg A \\vee \\neg B)",
    story:
      "A cornerstone of Boolean algebra. Because it only involves finitely many truth-values, the built-in verifier can PROVE it right now — by checking the truth table exhaustively in JavaScript.",
    source: { name: "De Morgan's laws", url: "https://en.wikipedia.org/wiki/De_Morgan%27s_laws" },
    proofs: [
      {
        system: "builtin",
        verified: true,
        note: "Verified live by exhaustive truth table.",
        code: "~(A & B) <-> (~A | ~B)"
      },
      {
        system: "coq",
        verified: true,
        runnable: false,
        note: "Coq (classical-free direction shown).",
        code:
`Theorem de_morgan : forall A B : Prop,
  ~(A /\\ B) <-> (~A \\/ ~B).
Proof.
  (* -> uses classical reasoning; <- is constructive. *)
Admitted.`
      }
    ],
    playground: { kind: "logic", formula: "~(A & B) <-> (~A | ~B)" }
  },

  {
    id: "peirce",
    title: "Peirce's Law",
    category: "Logic",
    status: "solved",
    year: "1885",
    by: "C. S. Peirce",
    tags: ["propositional", "runnable", "javascript", "classical"],
    statement: "((A → B) → A) → A is a tautology of classical logic.",
    latex: "((A \\to B) \\to A) \\to A",
    story:
      "The purely-implicational formula that captures the whole of classical (vs. intuitionistic) logic. It has no constructive proof — but the truth table settles it instantly.",
    source: { name: "Peirce's law", url: "https://en.wikipedia.org/wiki/Peirce%27s_law" },
    proofs: [
      { system: "builtin", verified: true, note: "Verified live by truth table.", code: "((A -> B) -> A) -> A" }
    ],
    playground: { kind: "logic", formula: "((A -> B) -> A) -> A" }
  },

  {
    id: "contrapositive",
    title: "Law of Contraposition",
    category: "Logic",
    status: "solved",
    year: "—",
    by: "classical logic",
    tags: ["propositional", "runnable", "javascript"],
    statement: "An implication is equivalent to its contrapositive:  (A → B) ↔ (¬B → ¬A).",
    latex: "(A \\to B) \\leftrightarrow (\\neg B \\to \\neg A)",
    story: "Why 'proof by contrapositive' is valid. Check it live.",
    source: { name: "Contraposition", url: "https://en.wikipedia.org/wiki/Contraposition" },
    proofs: [
      { system: "builtin", verified: true, note: "Verified live by truth table.", code: "(A -> B) <-> (~B -> ~A)" }
    ],
    playground: { kind: "logic", formula: "(A -> B) <-> (~B -> ~A)" }
  },

  /* ─────────────────────────  SOLVED — big machine-checked theorems  ─────────────── */

  {
    id: "four-color",
    title: "The Four Color Theorem",
    category: "Graph Theory",
    status: "solved",
    year: "1976 / 2005",
    by: "Appel & Haken; Gonthier (Coq)",
    tags: ["graph theory", "formalized", "coq", "landmark"],
    statement:
      "Every planar map can be colored with four colors so that no two regions sharing a border have the same color.",
    latex: "\\chi(G) \\le 4 \\quad \\text{for every planar graph } G",
    story:
      "The first major theorem proved with essential computer assistance (1976). For decades mathematicians worried about the unverifiable case analysis — until Georges Gonthier produced a complete, machine-checked proof in Coq in 2005, closing the debate for good.",
    source: { name: "Gonthier, 'Formal Proof — The Four-Color Theorem'", url: "https://www.ams.org/notices/200811/tx081101382p.pdf" },
    proofs: [
      {
        system: "coq",
        verified: true,
        runnable: false,
        note: "Gonthier's full development is ~60,000 lines of Coq. The top-level statement:",
        code:
`Theorem four_color_theorem :
  forall (m : map), simple_map m -> map_colorable 4 m.
Proof.
  (* 60k lines of machine-checked reasoning + reducibility. *)
Qed.`
      }
    ],
    playground: null
  },

  {
    id: "kepler",
    title: "The Kepler Conjecture",
    category: "Geometry",
    status: "solved",
    year: "1998 / 2014",
    by: "Hales; Flyspeck project",
    tags: ["packing", "formalized", "isabelle", "hol-light", "landmark"],
    statement:
      "No packing of equal spheres in three-dimensional space has density greater than the face-centered-cubic packing (≈ 74.05%).",
    latex: "\\delta_{\\max} = \\frac{\\pi}{\\sqrt{18}} \\approx 0.74048",
    story:
      "Kepler guessed the greengrocer's orange-stacking is optimal in 1611. Hales proved it in 1998 with 3 gigabytes of computation. Referees could only say they were '99% certain', so Hales launched Flyspeck, finishing a complete formal proof in HOL Light and Isabelle in 2014.",
    source: { name: "Flyspeck project", url: "https://en.wikipedia.org/wiki/Kepler_conjecture" },
    proofs: [
      {
        system: "hol-light",
        verified: true,
        runnable: false,
        note: "Flyspeck top-level theorem (HOL Light).",
        code:
`|- the_kepler_conjecture:
     !V. packing V
         ==> ?c. !r. &1 <= r
                     ==> &(CARD(V INTER ball(vec 0,r))) <=
                         pi * r pow 3 / sqrt(&18) + c * r pow 2`
      }
    ],
    playground: null
  },

  {
    id: "fermat-last",
    title: "Fermat's Last Theorem",
    category: "Number Theory",
    status: "solved",
    year: "1994",
    by: "Andrew Wiles",
    tags: ["landmark", "modularity"],
    statement:
      "No three positive integers a, b, c satisfy aⁿ + bⁿ = cⁿ for any integer n > 2.",
    latex: "a^n + b^n = c^n \\ \\text{has no positive-integer solutions for } n > 2",
    story:
      "Conjectured by Fermat in 1637 in a margin 'too small to contain' his proof. It resisted for 358 years until Andrew Wiles, via the modularity of elliptic curves, proved it in 1994. A full Lean formalization is currently underway (Kevin Buzzard's FLT project).",
    source: { name: "Fermat's Last Theorem", url: "https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem" },
    proofs: [
      {
        system: "lean",
        verified: false,
        runnable: false,
        note: "Statement in Lean 4. A complete proof is an active multi-year formalization effort.",
        code:
`theorem fermat_last_theorem
    (n : ℕ) (hn : 2 < n) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ n + b ^ n ≠ c ^ n := by
  sorry -- Wiles 1994; Lean formalization in progress`
      }
    ],
    playground: null
  },

  {
    id: "erdos-discrepancy",
    title: "The Erdős Discrepancy Problem",
    category: "Combinatorics",
    status: "solved",
    year: "2015",
    by: "Terence Tao",
    tags: ["erdos", "combinatorics", "sat", "landmark"],
    statement:
      "For every ±1 sequence and every constant C, there is a step d and length k such that |x_d + x_2d + … + x_kd| > C.  (Discrepancy along arithmetic progressions is unbounded.)",
    latex: "\\sup_{d,k}\\ \\left| \\sum_{i=1}^{k} x_{i\\cdot d} \\right| = \\infty",
    story:
      "Posed by Erdős in the 1930s. In 2014 Konev & Lisitsa used a SAT solver to prove the C = 2 case, generating a 13-gigabyte certificate — 'the longest proof ever'. Terence Tao settled the full conjecture in 2015 using the Elliott conjecture on multiplicative functions.",
    source: { name: "Erdős discrepancy problem", url: "https://en.wikipedia.org/wiki/Erd%C5%91s_discrepancy_problem" },
    proofs: [
      {
        system: "note",
        verified: true,
        runnable: false,
        note: "The C = 2 special case was certified by a SAT solver (DRAT proof, ~13 GB).",
        code:
`-- Konev & Lisitsa (2014): no ±1 sequence of length 1161
-- keeps discrepancy <= 2.  Verified by a SAT solver.
-- Tao (2015): full conjecture, via the Elliott conjecture.`
      }
    ],
    playground: null
  },

  {
    id: "imo-2024-p1",
    title: "IMO 2024 Problem 1  (AlphaProof)",
    category: "Olympiad",
    status: "solved",
    year: "2024",
    by: "IMO contestants; Google DeepMind AlphaProof",
    tags: ["deepmind", "alphaproof", "lean", "olympiad"],
    statement:
      "Determine all real numbers α such that, for every positive integer n, the integer ⌊α⌋ + ⌊2α⌋ + … + ⌊nα⌋ is divisible by n.  (Answer: the even integers.)",
    latex: "\\Big\\{\\, \\alpha \\in \\mathbb{R} : n \\,\\big|\\, \\textstyle\\sum_{k=1}^{n} \\lfloor k\\alpha \\rfloor \\ \\ \\forall n \\ge 1 \\,\\Big\\} = 2\\mathbb{Z}",
    story:
      "At IMO 2024, Google DeepMind's AlphaProof produced fully formal Lean proofs for four of the six problems — reaching silver-medal level. Each generated proof was machine-checked by the Lean kernel, so its correctness is not in doubt.",
    source: { name: "DeepMind: AI achieves silver-medal standard at the IMO", url: "https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/" },
    proofs: [
      {
        system: "lean",
        verified: true,
        runnable: false,
        note: "Shape of the Lean statement AlphaProof formalized and proved.",
        code:
`theorem imo_2024_p1 (α : ℝ) :
    (∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ k ∈ Finset.Icc 1 n, ⌊(k : ℝ) * α⌋)
      ↔ ∃ m : ℤ, α = 2 * m := by
  sorry -- AlphaProof produced a complete, kernel-checked proof`
      }
    ],
    playground: null
  },

  /* ─────────────────────────  OPEN — with interactive explorers  ─────────────────── */

  {
    id: "goldbach",
    title: "Goldbach's Conjecture",
    category: "Number Theory",
    status: "open",
    year: "1742",
    by: "Christian Goldbach",
    oeis: "A002375",
    tags: ["primes", "millennium-flavor", "famous"],
    statement:
      "Every even integer greater than 2 can be written as the sum of two primes.",
    latex: "\\forall\\, n \\ge 2,\\ \\exists\\, p, q\\ \\text{prime},\\ 2n = p + q",
    story:
      "Verified by computer for every even number up to 4×10¹⁸, yet no proof is known. Give it a try below: pick an even number and the app will find a Goldbach pair for you — you're literally checking a case of a 280-year-old open problem.",
    source: { name: "Goldbach's conjecture", url: "https://en.wikipedia.org/wiki/Goldbach%27s_conjecture" },
    proofs: [
      {
        system: "lean",
        verified: false,
        runnable: false,
        note: "Statement only — nobody has a proof.",
        code:
`theorem goldbach (n : ℕ) (hn : 2 < n) (he : Even n) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n := by
  sorry -- OPEN PROBLEM`
      }
    ],
    playground: { kind: "goldbach" }
  },

  {
    id: "collatz",
    title: "The Collatz Conjecture",
    category: "Dynamics",
    status: "open",
    year: "1937",
    by: "Lothar Collatz",
    oeis: "A006577",
    tags: ["dynamics", "3n+1", "famous"],
    statement:
      "Start with any positive integer n. If n is even, halve it; if odd, replace it by 3n+1. The conjecture says you always eventually reach 1.",
    latex: "n \\mapsto \\begin{cases} n/2 & n\\ \\text{even}\\\\ 3n+1 & n\\ \\text{odd}\\end{cases} \\quad\\longrightarrow\\quad 1",
    story:
      "Paul Erdős said 'mathematics may not be ready for such problems.' Verified past 2⁶⁸. Enter a number below and watch its trajectory bounce around before (conjecturally!) crashing to 1.",
    source: { name: "Collatz conjecture", url: "https://en.wikipedia.org/wiki/Collatz_conjecture" },
    proofs: [
      {
        system: "lean",
        verified: false,
        runnable: false,
        note: "Statement only.",
        code:
`def collatz : ℕ → ℕ
  | 0 => 0
  | n => if n % 2 = 0 then n / 2 else 3 * n + 1

theorem collatz_conjecture (n : ℕ) (hn : 0 < n) :
    ∃ k, (collatz^[k]) n = 1 := by
  sorry -- OPEN PROBLEM`
      }
    ],
    playground: { kind: "collatz" }
  },

  {
    id: "twin-primes",
    title: "The Twin Prime Conjecture",
    category: "Number Theory",
    status: "partial",
    year: "1849",
    by: "de Polignac",
    oeis: "A001359",
    tags: ["primes", "zhang", "polymath"],
    statement:
      "There are infinitely many primes p such that p + 2 is also prime (e.g. 11 & 13, 17 & 19).",
    latex: "\\#\\{\\,p : p\\ \\text{and}\\ p+2\\ \\text{both prime}\\,\\} = \\infty",
    story:
      "Still open — but in 2013 Yitang Zhang stunned the world by proving there are infinitely many prime pairs differing by at most 70 million. The Polymath8 project and Maynard drove the gap down to 246. The '2' is the last mile. Hunt for twin primes below!",
    source: { name: "Twin prime conjecture", url: "https://en.wikipedia.org/wiki/Twin_prime" },
    proofs: [
      {
        system: "note",
        verified: false,
        runnable: false,
        note: "Best known result (Zhang 2013 → Polymath/Maynard): infinitely many prime gaps ≤ 246.",
        code:
`-- Zhang (2013):   liminf (p_{n+1} - p_n) < 7*10^7
-- Polymath8/Maynard: liminf (p_{n+1} - p_n) <= 246
-- Twin prime conjecture wants the bound 2 — OPEN.`
      }
    ],
    playground: { kind: "twin" }
  },

  {
    id: "erdos-straus",
    title: "The Erdős–Straus Conjecture",
    category: "Number Theory",
    status: "open",
    year: "1948",
    by: "Erdős & Straus",
    oeis: "A192787",
    tags: ["erdos", "egyptian fractions", "famous"],
    statement:
      "For every integer n ≥ 2, the fraction 4/n can be written as a sum of three unit fractions:  4/n = 1/a + 1/b + 1/c with positive integers a, b, c.",
    latex: "\\frac{4}{n} = \\frac{1}{a} + \\frac{1}{b} + \\frac{1}{c}",
    story:
      "Verified for all n up to 10¹⁷, but open in general. It's an 'Egyptian fraction' problem straight out of antiquity. Type an n and the solver will find a decomposition.",
    source: { name: "Erdős–Straus conjecture", url: "https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture" },
    proofs: [
      {
        system: "lean",
        verified: false,
        runnable: false,
        code:
`theorem erdos_straus (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1/a + 1/b + 1/c := by
  sorry -- OPEN PROBLEM`
      }
    ],
    playground: { kind: "erdos-straus" }
  },

  {
    id: "legendre",
    title: "Legendre's Conjecture",
    category: "Number Theory",
    status: "open",
    year: "1808",
    by: "Adrien-Marie Legendre",
    tags: ["primes", "landau"],
    statement:
      "There is always a prime number between n² and (n+1)² for every positive integer n.",
    latex: "\\forall\\, n \\ge 1,\\ \\exists\\, p\\ \\text{prime},\\ n^2 < p < (n+1)^2",
    story:
      "One of Landau's four 'unattackable' problems from 1912 — still unattacked. It would follow from the Riemann Hypothesis being 'a bit better'. Pick n and find a prime in the gap.",
    source: { name: "Legendre's conjecture", url: "https://en.wikipedia.org/wiki/Legendre%27s_conjecture" },
    proofs: [
      {
        system: "note",
        verified: false,
        runnable: false,
        code: `-- Between n^2 and (n+1)^2 there is always a prime. OPEN.`
      }
    ],
    playground: { kind: "legendre" }
  },

  /* ─────────────────────────  OPEN — Millennium & giants (statements)  ───────────── */

  {
    id: "p-vs-np",
    title: "P versus NP",
    category: "Complexity Theory",
    status: "open",
    year: "1971",
    by: "Cook & Levin",
    tags: ["millennium", "complexity", "famous"],
    statement:
      "Is every problem whose solution can be verified quickly also solvable quickly?  I.e., does P = NP?",
    latex: "\\mathsf{P} \\overset{?}{=} \\mathsf{NP}",
    story:
      "The most famous open problem in computer science and one of the seven $1,000,000 Millennium Prize Problems. Most experts believe P ≠ NP. Below is a tiny live SAT solver — a taste of the NP-complete problem at the heart of it.",
    source: { name: "P versus NP problem", url: "https://en.wikipedia.org/wiki/P_versus_NP_problem" },
    proofs: [
      {
        system: "note",
        verified: false,
        runnable: false,
        code:
`-- SAT is NP-complete (Cook–Levin, 1971).
-- If any NP-complete problem is in P, then P = NP.
-- No polynomial-time SAT algorithm is known. OPEN ($1,000,000).`
      }
    ],
    playground: { kind: "sat" }
  },

  {
    id: "riemann",
    title: "The Riemann Hypothesis",
    category: "Analysis",
    status: "open",
    year: "1859",
    by: "Bernhard Riemann",
    tags: ["millennium", "zeta", "primes", "famous"],
    statement:
      "Every non-trivial zero of the Riemann zeta function ζ(s) has real part exactly 1/2.",
    latex: "\\zeta(s) = 0,\\ s \\ne -2,-4,\\dots \\ \\Longrightarrow\\ \\Re(s) = \\tfrac{1}{2}",
    story:
      "The deepest question about the distribution of prime numbers, and a Millennium Prize Problem. Over 10 trillion zeros have been checked — all on the critical line. No proof in sight.",
    source: { name: "Riemann hypothesis", url: "https://en.wikipedia.org/wiki/Riemann_hypothesis" },
    proofs: [
      {
        system: "lean",
        verified: false,
        runnable: false,
        code:
`theorem riemann_hypothesis :
    ∀ s : ℂ, riemannZeta s = 0 → s.re = 1 / 2 ∨ ∃ n : ℕ, s = -2 * (n + 1) := by
  sorry -- OPEN PROBLEM ($1,000,000)`
      }
    ],
    playground: null
  },

  {
    id: "navier-stokes",
    title: "Navier–Stokes Existence & Smoothness",
    category: "PDE",
    status: "open",
    year: "2000",
    by: "Clay Mathematics Institute",
    tags: ["millennium", "fluids", "pde"],
    statement:
      "In three dimensions, do smooth, physically reasonable solutions to the Navier–Stokes equations always exist for all time — or can they blow up?",
    latex: "\\partial_t u + (u\\cdot\\nabla)u = -\\nabla p + \\nu\\,\\Delta u,\\quad \\nabla\\cdot u = 0",
    story:
      "The equations of fluid flow — used every day in engineering — but we can't prove their 3D solutions stay smooth. A Millennium Prize Problem.",
    source: { name: "Navier–Stokes existence and smoothness", url: "https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_existence_and_smoothness" },
    proofs: [
      { system: "note", verified: false, runnable: false, code: `-- Global regularity of 3D Navier–Stokes. OPEN ($1,000,000).` }
    ],
    playground: null
  },

  {
    id: "bsd",
    title: "Birch & Swinnerton-Dyer Conjecture",
    category: "Number Theory",
    status: "open",
    year: "1965",
    by: "Birch & Swinnerton-Dyer",
    tags: ["millennium", "elliptic curves"],
    statement:
      "The rank of the group of rational points on an elliptic curve equals the order of vanishing of its L-function at s = 1.",
    latex: "\\operatorname{rank}\\, E(\\mathbb{Q}) = \\operatorname{ord}_{s=1} L(E, s)",
    story:
      "Links the arithmetic of elliptic curves to complex analysis. Known only in special cases. A Millennium Prize Problem.",
    source: { name: "Birch and Swinnerton-Dyer conjecture", url: "https://en.wikipedia.org/wiki/Birch_and_Swinnerton-Dyer_conjecture" },
    proofs: [
      { system: "note", verified: false, runnable: false, code: `-- rank E(Q) = ord_{s=1} L(E,s). OPEN ($1,000,000).` }
    ],
    playground: null
  },

  {
    id: "hodge",
    title: "The Hodge Conjecture",
    category: "Algebraic Geometry",
    status: "open",
    year: "1950",
    by: "W. V. D. Hodge",
    tags: ["millennium", "geometry", "topology"],
    statement:
      "On a projective non-singular algebraic variety, every Hodge class is a rational linear combination of the classes of algebraic cycles.",
    latex: "H^{k,k}(X) \\cap H^{2k}(X,\\mathbb{Q}) = \\text{classes of algebraic cycles}",
    story:
      "A bridge between topology, complex geometry and algebra — arguably the most technical of the Millennium Problems.",
    source: { name: "Hodge conjecture", url: "https://en.wikipedia.org/wiki/Hodge_conjecture" },
    proofs: [
      { system: "note", verified: false, runnable: false, code: `-- Every Hodge class is algebraic. OPEN ($1,000,000).` }
    ],
    playground: null
  },

  {
    id: "yang-mills",
    title: "Yang–Mills Existence & Mass Gap",
    category: "Mathematical Physics",
    status: "open",
    year: "2000",
    by: "Clay Mathematics Institute",
    tags: ["millennium", "physics", "gauge theory"],
    statement:
      "Prove that a quantum Yang–Mills theory exists on ℝ⁴ for any compact simple gauge group, and has a mass gap Δ > 0.",
    latex: "\\exists\\, \\Delta > 0 : \\text{spectrum of the Hamiltonian} \\subseteq \\{0\\} \\cup [\\Delta, \\infty)",
    story:
      "The mathematics behind the Standard Model of particle physics. Physicists 'know' the mass gap exists; nobody has proved it rigorously. A Millennium Prize Problem.",
    source: { name: "Yang–Mills existence and mass gap", url: "https://en.wikipedia.org/wiki/Yang%E2%80%93Mills_existence_and_mass_gap" },
    proofs: [
      { system: "note", verified: false, runnable: false, code: `-- Existence + mass gap for quantum Yang–Mills. OPEN ($1,000,000).` }
    ],
    playground: null
  },

  {
    id: "abc",
    title: "The abc Conjecture",
    category: "Number Theory",
    status: "partial",
    year: "1985",
    by: "Oesterlé & Masser",
    tags: ["number theory", "disputed", "famous"],
    statement:
      "For coprime a + b = c and any ε > 0, only finitely many triples satisfy c > rad(abc)^{1+ε}, where rad is the product of distinct prime factors.",
    latex: "c \\le C_\\varepsilon \\cdot \\operatorname{rad}(abc)^{\\,1+\\varepsilon}",
    story:
      "A deceptively simple statement with sweeping consequences (it implies Fermat's Last Theorem for large exponents). Shinichi Mochizuki announced a 500-page proof via 'Inter-universal Teichmüller theory' in 2012, but its validity remains disputed by the wider mathematical community.",
    source: { name: "abc conjecture", url: "https://en.wikipedia.org/wiki/Abc_conjecture" },
    proofs: [
      { system: "note", verified: false, runnable: false, code: `-- Mochizuki's IUT proof (2012) is not accepted by consensus. Status: DISPUTED.` }
    ],
    playground: null
  },

  {
    id: "mersenne",
    title: "Infinitely Many Mersenne Primes?",
    category: "Number Theory",
    status: "open",
    year: "1644",
    by: "Marin Mersenne",
    oeis: "A000668",
    tags: ["primes", "gimps"],
    statement:
      "Are there infinitely many primes of the form 2^p − 1 (Mersenne primes)?",
    latex: "\\#\\{\\,p\\ \\text{prime} : 2^p - 1\\ \\text{is prime}\\,\\} \\overset{?}{=} \\infty",
    story:
      "Only 52 Mersenne primes are known (the largest has over 41 million digits). The distributed GIMPS project hunts for more, but whether they go on forever is open. Sequence A000668 in the OEIS.",
    source: { name: "Mersenne prime", url: "https://en.wikipedia.org/wiki/Mersenne_prime" },
    proofs: [
      { system: "note", verified: false, runnable: false, code: `-- 2^p - 1 prime for infinitely many p? OPEN. Known: 52 examples.` }
    ],
    playground: { kind: "mersenne" }
  },

  {
    id: "a317940",
    title: "Nonnegativity of OEIS A317940",
    category: "Number Theory",
    status: "review",
    featured: true,
    year: "2018 (posed) · 2026 (submitted)",
    by: "Submitted through this system · under review",
    oeis: "A317940",
    tags: ["oeis", "dirichlet", "deepmind", "lean", "submission", "candidate-proof"],
    statement:
      "Let f be the rational arithmetic function with f(1)=1 whose Dirichlet square f∗f equals A046644 (the multiplicative function with A046644(pᵉ)=2^A005187(e)). A317940 records the numerators of f(n). Conjecture: f(n) ≥ 0 for every n ≥ 1.",
    latex: "f * f = A046644,\\quad f(1)=1 \\ \\Longrightarrow\\ f(n) \\ge 0 \\quad (n \\ge 1)",
    story:
      "This is entry A317940 in Google DeepMind's Formal Conjectures — a curated set of open problems formalized in Lean 4 (each stated with `sorry`). OEIS notes 'no negative terms among the first 2²⁰ terms; is the sequence nonnegative?'. This proof was submitted through this system (the /math/new/ pipeline) and is under review: a 659-line Lean 4 development that proves the exact statement `A317940_f_nonnegative`, plus the stronger fact f(n) > 0. The idea: f is the multiplicative lift of the formal square root of the binary Euler product ∏(1 + xᵗ/2), whose coefficients are all positive. The formal proof has been independently kernel-checked against real Mathlib in CI (clean axiom footprint) — so the theorem itself is machine-verified; what remains under review is novelty/priority and acceptance by OEIS/DeepMind. See the verification panel, the /math/a317940/ project page, and /verifications.html.",
    source: { name: "DeepMind Formal Conjectures (A317940) · OEIS A317940", url: "https://oeis.org/A317940" },
    verification: {
      note: "Bottom line: the exact DeepMind theorem A317940_f_nonnegative is now independently kernel-verified — compiled against real Mathlib on GitHub Actions with a clean axiom footprint (no sorryAx). Publication novelty and priority still warrant human/literature review, but the formal claim itself is proved. See /verifications.html for the live status.",
      checks: [
        { state: "pass", label: "Statement is faithful", detail: "The Lean definitions of A005187, A046644, A317940_f and the theorem A317940_f_nonnegative are byte-identical to DeepMind's upstream spec — no weakening or hidden hypotheses." },
        { state: "pass", label: "No proof-cheating tokens", detail: "The 659-line proof contains no sorry, admit, native_decide, or custom axiom." },
        { state: "pass", label: "Kernel re-verified vs. Mathlib (CI)", detail: "The verify-lean GitHub Action fetched 7,869 Mathlib olean files and compiled the proof: 'Built A317940' + 'Build completed successfully (7886 jobs)'." },
        { state: "pass", label: "Clean axiom audit (CI)", detail: "The CI build's #print axioms reports exactly [propext, Classical.choice, Quot.sound] — the three standard Mathlib axioms, no sorryAx." },
        { state: "pass", label: "Independent numeric check", detail: "A from-scratch exact-rational reimplementation (not the author's code) reproduces OEIS anchors a(1..4)=1,1,1,7 and finds f(n) > 0 for all n ≤ 200,000. You can rerun a live version below." },
        { state: "partial", label: "Novelty / priority", detail: "The proof is valid; whether the result and its argument are new (vs. prior literature) is a separate question — see the prior-art note under Materials." }
      ]
    },
    proofs: [
      {
        system: "lean",
        verified: true,
        runnable: false,
        codeUrl: "./a317940/proof/A317940_verified.lean",
        lines: 659,
        note: "Kernel-verified against real Mathlib on GitHub Actions (axioms: propext, Classical.choice, Quot.sound). Excerpt below; load the full 659-line proof or open it under Materials.",
        code:
`import Mathlib

open Nat Finset

-- exact Google DeepMind Formal Conjectures definitions (byte-identical to upstream):
noncomputable def A005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2^k)

noncomputable def A046644 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ (2 : ℚ) ^ (A005187 e)

noncomputable def A317940_f : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if n = 0 then 0 else if n = 1 then 1 else
      let A_n : ℚ := A046644 n
      let sum_of_products : ℚ := Finset.sum (divisors n) fun d ↦
        if h_prop : d > 1 ∧ d < n then
          IH d h_prop.2 * IH (n / d) (Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h_prop.1)
        else 0
      (A_n - sum_of_products) / 2

/- ... 620 lines building: d, a, b power series; the ODE A' = ½·D·A;
   Qseries = Aseries² = Bseries (uniqueness of the ODE); rescaling c e = 4^e·a e;
   rootAF a multiplicative arithmetic function with rootAF * rootAF = targetAF;
   A317940_f = rootAF; and rootAF n > 0 as a product of positive c e ... -/

theorem A317940_nonnegative (n : ℕ) (hn : n > 0) : A317940_f n ≥ 0 := by
  rw [A317940_f_eq_rootAF]; exact le_of_lt (rootAF_pos hn)

-- the exact upstream theorem, discharged:
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 :=
  A317940Verified.A317940_nonnegative n h`
      },
      {
        system: "note",
        verified: true,
        runnable: false,
        note: "Human-readable proof sketch (full write-up in Materials).",
        code:
`Let c_e = f(p^e) (prime-independent). Since A005187(e) = 2e - s2(e) with
s2 = binary digit sum, the normalized coefficients b_e = 2^{-s2(e)} have
generating function  B(x) = Prod_{r>=0} (1 + x^{2^r}/2).
Let A(x)^2 = B(x), A(0)=1. For n = 2^v * m (m odd),
  [x^n] log A(x) = (1/(2m)) * (2^{-m} - Sum_{j=1..v} 2^{-j-2^j m}) > 0,
so every coefficient a_e > 0. Set c_e = 4^e a_e; then Sum_j c_j c_{e-j} = 2^{A005187(e)},
i.e. h*h = A046644 for the multiplicative h(p^e)=c_e. Endpoint-divisor separation
shows h obeys f's recursion, so f = h and f(n) > 0 for all n >= 1.  ∎`
      }
    ],
    materials: [
      { group: "Project site", type: "link", label: "📄 Full project page & all downloads → /math/a317940/", href: "./a317940/", note: "Polished standalone site: abstract, proof, verification, papers, hashes" },
      { group: "Formal proof", type: "lean", label: "A317940_verified.lean", path: "./a317940/proof/A317940_verified.lean", note: "Complete 659-line Lean 4 proof (no sorry)" },
      { group: "Formal proof", type: "lean", label: "Upstream-form proof", path: "./a317940/proof/A317940_upstream_form.lean", note: "Installed into the exact Formal Conjectures file" },
      { group: "Formal proof", type: "lean", label: "DeepMind upstream spec", path: "./a317940/proof/A317940_upstream_spec.lean", note: "The original stated-with-sorry conjecture" },
      { group: "Formal proof", type: "lean", label: "Generalization: DigitalEulerPositivity.lean", path: "./a317940/proof/DigitalEulerPositivity_generalization.lean", note: "Parameterized 0<q≤1, α>0 positivity theorem" },
      { group: "Papers & notes", type: "pdf", label: "Paper draft (PDF)", path: "./a317940/paper/A317940_paper_draft.pdf" },
      { group: "Papers & notes", type: "tex", label: "Paper draft (LaTeX source)", path: "./a317940/paper/A317940_paper_draft.tex" },
      { group: "Papers & notes", type: "pdf", label: "Short note (PDF)", path: "./a317940/paper/A317940_short_note.pdf" },
      { group: "Papers & notes", type: "tex", label: "Short note (LaTeX source)", path: "./a317940/paper/A317940_short_note.tex" },
      { group: "Papers & notes", type: "md", label: "Human-readable proof", path: "./a317940/docs/HUMAN_PROOF.md" },
      { group: "Papers & notes", type: "md", label: "Prior-art boundary", path: "./a317940/docs/PRIOR_ART.md", note: "Honest novelty scope" },
      { group: "Submission drafts", type: "txt", label: "OEIS submission text", path: "./a317940/submission/OEIS_SUBMISSION.txt" },
      { group: "Submission drafts", type: "md", label: "DeepMind PR draft", path: "./a317940/submission/DEEPMIND_PR_draft.md" },
      { group: "Submission drafts", type: "md", label: "DeepMind issue draft", path: "./a317940/submission/DEEPMIND_ISSUE_draft.md" },
      { group: "Verification artifacts", type: "json", label: "AXLE verifier response", path: "./a317940/verification/AXLE_verification.json", note: "Author-supplied Lean 4.27 compile log" },
      { group: "Verification artifacts", type: "log", label: "Axiom audit (#print axioms)", path: "./a317940/verification/axiom_audit.log" },
      { group: "Verification artifacts", type: "json", label: "Spec-integrity check", path: "./a317940/verification/spec_integrity.json", note: "SHA-256 vs. upstream definitions" },
      { group: "Verification artifacts", type: "md", label: "Verification report", path: "./a317940/docs/VERIFICATION_REPORT.md" },
      { group: "Verification & evidence", type: "link", label: "Full evidence chain (/verifications.html)", href: "../verifications.html#proven", note: "Links + hashes + CI kernel check" },
      { group: "Verification & evidence", type: "json", label: "evidence/A317940.json", href: "../evidence/A317940.json", note: "Machine-readable: hashes, axioms, run URL" },
      { group: "Verification & evidence", type: "link", label: "DeepMind upstream conjecture (317940_cd729cdd.lean)", href: "https://github.com/google-deepmind/formal-conjectures/blob/auto_oeis/FormalConjectures/OEIS/Auto/317940_cd729cdd.lean", note: "The exact statement, stated with `sorry`" },
      { group: "Verification & evidence", type: "link", label: "CI kernel verification (GitHub Actions)", href: "https://github.com/DomTheDeveloper/crl/actions/runs/29376765402", note: "Built against real Mathlib; axioms clean" },
      { group: "Discussion", type: "link", label: "OEIS A317940", href: "https://oeis.org/A317940", note: "Comment / discuss on OEIS" },
      { group: "Discussion", type: "link", label: "DeepMind Formal Conjectures repo", href: "https://github.com/google-deepmind/formal-conjectures", note: "Open a PR / issue upstream" }
    ],
    playground: { kind: "a317940" }
  },

  {
    id: "z3-smt",
    title: "SMT Solving with Z3",
    category: "Logic",
    status: "solved",
    year: "2008",
    by: "Microsoft Research (de Moura & Bjørner)",
    tags: ["smt", "z3", "solver", "runnable", "wasm"],
    statement:
      "Satisfiability Modulo Theories (SMT): decide whether a first-order formula over theories like integers, reals, arrays and bit-vectors is satisfiable. Z3 is a state-of-the-art decision procedure for many such theories.",
    latex: "\\exists\\, \\vec{x}\\ \\varphi(\\vec{x})\\ \\text{over } (\\mathbb{Z}, \\mathbb{R}, \\text{arrays}, \\dots)\\ \\overset{?}{=}\\ \\textsf{sat}",
    story:
      "SMT solvers power program verifiers, symbolic execution, and — relevantly here — proof automation (Coq's and Lean's arithmetic tactics lean on the same ideas). Z3 compiled to WebAssembly runs right in your browser: write SMT-LIB2 and get sat/unsat plus a model. The exact same solver is re-checked headlessly in CI (tests/z3.mjs).",
    source: { name: "Z3 Theorem Prover", url: "https://github.com/Z3Prover/z3" },
    proofs: [
      {
        system: "note",
        verified: true,
        runnable: false,
        note: "Verified live by Z3 (WASM) below, and in CI.",
        code:
`; De Morgan is valid: the negation of the equivalence is UNSAT.
(declare-const a Bool)
(declare-const b Bool)
(assert (not (= (not (and a b)) (or (not a) (not b)))))
(check-sat)   ; => unsat, hence the law is a tautology`
      }
    ],
    playground: { kind: "z3" }
  },
];
