# Submit A317940 to DeepMind — final two clicks

Everything on our side is done and verified. The two remaining actions must
happen under your own GitHub account (the `google-deepmind` org is external —
Claude's session cannot open issues/PRs there). The branch is already pushed.

Status:
- [x] Proof complete & kernel-verified (Lean 4 + Mathlib; axioms: propext,
      Classical.choice, Quot.sound; no sorryAx).
- [x] CLA signed (you confirmed).
- [x] gh-pages public so the `formal_proof` link resolves.
- [x] Fork branch pushed: `DomTheDeveloper/formal-conjectures@a317940-solved`
      (adds the `@[category research solved, AMS 11, formal_proof …]` marker to
      `FormalConjectures/OEIS/Auto/317940_cd729cdd.lean`).
- [ ] **You: open the issue** (link below) — their process is issue-first.
- [ ] **You: open the PR** (link below).

---

## Step 1 — Open the issue (pre-filled, one click)

https://github.com/google-deepmind/formal-conjectures/issues/new?title=A317940+nonnegativity+%28A317940_f_nonnegative%29+has+a+formal+Lean+4+proof+%E2%80%94+mark+solved%3F&body=The+OEIS+A317940+conjecture+currently+staged+at%0A%60FormalConjectures%2FOEIS%2FAuto%2F317940_cd729cdd.lean%60+%28branch+%60auto_oeis%60%29+is+stated%0Awith+%60sorry%60%3A%0A%0A%60%60%60lean%0Atheorem+A317940_f_nonnegative+%28n+%3A+%E2%84%95%29+%28h+%3A+n+%3E+0%29+%3A+A317940_f+n+%E2%89%A5+0+%3A%3D+by+sorry%0A%60%60%60%0A%0AI+have+a+complete+Lean+4+proof+of+%2A%2Athe+exact+statement%2A%2A%2C+using+your+exact%0Adefinitions+of+%60A005187%60%2C+%60A046644%60%2C+and+%60A317940_f%60+%28byte-identical+after%0Acomment+stripping%29.+Per+the+%3E25%E2%80%9350+line+guidance%2C+the+659-line+proof+stays+in+my%0Arepository+and+would+be+linked+via+%60%40%5Bformal_proof+using+lean4+at+%22%E2%80%A6%22%5D%60.%0A%0A%2A%2AEvidence%2A%2A%0A-+Proof+%28Lean+4%2C+no+%60sorry%60%2F%60admit%60%2Fcustom+axiom%29%3A+%3Chttps%3A%2F%2Fdomthedeveloper.github.io%2Fcrl%2Fmath%2Fa317940%2Fproof%2FA317940_verified.lean%3E%0A-+Kernel-verified+against+Mathlib+in+CI%3B+%60%23print+axioms%60+%E2%86%92%0A++%60%5Bpropext%2C+Classical.choice%2C+Quot.sound%5D%60+%28no+%60sorryAx%60%29%3A%0A++%3Chttps%3A%2F%2Fgithub.com%2FDomTheDeveloper%2Fcrl%2Factions%2Fruns%2F29378868663%3E%0A-+Faithfulness%3A+your+upstream+file+sha256%0A++%604658ee6927738e3b54f54e64fed146124558797b161bc3ec280f8b64280ef020%60%3B+the%0A++definition+code+matches+byte-for-byte.%0A-+Prior-art+check+%28no+pre-existing+formal+proof+found%3B+conjecture+still+open%0A++upstream%29%3A+%3Chttps%3A%2F%2Fdomthedeveloper.github.io%2Fcrl%2Fmath%2Fa317940%2Fprior-art.html%3E%0A-+Human-readable+proof+%2F+paper%3A+%3Chttps%3A%2F%2Fdomthedeveloper.github.io%2Fcrl%2Fmath%2Fa317940%2F%3E%0A%0A%2A%2AQuestion+on+process.%2A%2A+A317940+lives+on+the+%60auto_oeis%60+branch+and+carries+no%0A%60%40%5Bcategory%5D%60+tags+yet+%28unlike+the+curated+files%29.+What%27s+your+preferred+path%3F%0A1.+Add+%60%40%5Bcategory+research+solved%2C+AMS+11%2C+formal_proof+using+lean4+at+%22%E2%80%A6%22%5D%60+to%0A+++the+theorem+in+the+auto+file%2C+or%0A2.+Curate+A317940+into+a+%60main%60+location+%28I%27m+happy+to+add+the+appropriate%0A+++category+tags+to+the+accompanying+value-check+statements+too%29.%0A%0AI%27ve+signed+the+CLA+and+can+open+a+PR+against+whichever+target+you+prefer.

## Step 2 — Open the PR (one click — branch is ready and clean)

The fork branch `a317940-solved` is now built **on top of the exact upstream
`auto_oeis` commit** (`67338a15…`), so the diff is precisely the two marker
lines and merges cleanly (the earlier "outdated" was from an older main-based
branch — fixed). Open the PR here:

  https://github.com/google-deepmind/formal-conjectures/compare/auto_oeis...DomTheDeveloper:a317940-solved?expand=1

- Base: `google-deepmind/formal-conjectures` : `auto_oeis`
- Head: `DomTheDeveloper/formal-conjectures` : `a317940-solved`
- Diff: `FormalConjectures/OEIS/Auto/317940_cd729cdd.lean`, +2 lines only.

Paste the title/body from `PR.md` and add `Resolves #<issue-number>` from Step 1.

**Fallback (identical result via the web editor):**
  https://github.com/google-deepmind/formal-conjectures/edit/auto_oeis/FormalConjectures/OEIS/Auto/317940_cd729cdd.lean
Insert, immediately above `theorem A317940_f_nonnegative`:

    @[category research solved, AMS 11,
      formal_proof using lean4 at "https://domthedeveloper.github.io/crl/math/a317940/proof/A317940_verified.lean"]
