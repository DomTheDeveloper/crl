# Submit WOWII Conjecture 322 to DeepMind — final two clicks

Everything on our side is done. The branch is pushed and the diff is a clean
open→solved change. The two remaining actions run under your GitHub account
(the `google-deepmind` org is external — Claude's session cannot open issues/PRs
there).

Status:
- [x] Complete Lean 4 proof (no sorry/admit/native_decide).
- [x] Statement byte-identical to the upstream theorem signature.
- [x] Diff vs upstream = only `@[category research open]`→`solved` and `sorry`→proof.
- [x] Fork branch pushed: `DomTheDeveloper/formal-conjectures@wowii322-solved`
      (based on the current upstream `main`, so the compare is clean).
- [x] CI workflow that builds it inside the real DeepMind repo:
      `.github/workflows/verify-wowii322.yml`.
- [ ] **You: open the issue** (link below) — their process is issue-first.
- [ ] **You: open the PR** (link below).

---

## Step 1 — Open the issue (pre-filled, one click)

https://github.com/google-deepmind/formal-conjectures/issues/new?title=WOWII+Conjecture+322+%28conjecture322%29+has+a+complete+Lean+4+proof+%E2%80%94+mark+solved%3F&body=%60WrittenOnTheWallII.GraphConjecture322.conjecture322%60+is+currently%0A%60%40%5Bcategory+research+open%2C+AMS+5%5D%60+with+%60%3A%3D+by+sorry%60.+I+have+a+complete+Lean+4+proof%0Aof+%2A%2Athe+exact+statement%2A%2A+%28byte-identical+signature%29%2C+using+only+the+library%27s+own%0Adefinitions+%28%60IsWellTotallyDominated%60%2C+%60IsTotalDominatingSet%60%2C+%60indepNeighborsCard%60%2C%0A%60indepNum%60%29.%0A%0AThe+proof+is+short+%28~64+lines%29%2C+so+it+fits+inline+%E2%80%94+no+external+%60formal_proof%60+link%0Aneeded.%0A%0A%2A%2AProof+idea.%2A%2A+The+hypothesis+%60indepNeighborsCard+G+v+%E2%89%A4+1%60+for+all+%60v%60+forces+every%0Aopen+neighborhood+to+be+a+clique%2C+i.e.+%60G%60+is+%60P%E2%82%83%60-free%3B+a+connected+%60P%E2%82%83%60-free+graph+is%0Acomplete.+In+a+complete+graph+on+%E2%89%A5+2+vertices+a+set+totally+dominates+iff+it+has+%E2%89%A5+2%0Avertices%2C+so+every+minimal+total+dominating+set+has+cardinality+exactly+2+and+%60G%60+is%0Awell+totally+dominated.+%28The+%60n+%E2%89%A5+5%60+bound+is+inherited%3B+%60n+%E2%89%A5+2%60+suffices.%29%0A%0A%2A%2AEvidence%2A%2A%0A-+The+proof+%28no+%60sorry%60%2F%60admit%60%2F%60native_decide%60%29%2C+and+a+diff+showing+only+the%0A++%60open%E2%86%92solved%60+tag+and+%60sorry%E2%86%92proof%60+change%3A%0A++%3Chttps%3A%2F%2Fdomthedeveloper.github.io%2Fcrl%2Fmath%2Fwowii322%2F%3E%0A-+Reproducible+kernel+check%3A+a+CI+workflow+that+checks+out+this+repo%2C+installs+the%0A++completed+proof%2C+and+runs+%60lake+build%60+%2B+%60%23print+axioms+conjecture322%60+against+real%0A++Mathlib+%E2%80%94+%60.github%2Fworkflows%2Fverify-wowii322.yml%60+in%0A++%3Chttps%3A%2F%2Fgithub.com%2FDomTheDeveloper%2Fcrl%3E.%0A%0AI%27ve+signed+the+CLA+and+have+a+PR+ready+%28branch+%60wowii322-solved%60+on+my+fork%29+%E2%80%94+happy+to%0Aopen+it+against+%60main%60.

## Step 2 — Open the PR (one click — branch is ready and clean)

https://github.com/google-deepmind/formal-conjectures/compare/main...DomTheDeveloper:wowii322-solved?expand=1

- Base: `google-deepmind/formal-conjectures : main`
- Head: `DomTheDeveloper/formal-conjectures : wowii322-solved`
- Diff: `FormalConjectures/WrittenOnTheWallII/GraphConjecture322.lean`, +64/−2.

Paste the title/body from `PR.md` and add `Resolves #<issue-number>` from Step 1.

**Fallback (identical result via the web editor):**
https://github.com/google-deepmind/formal-conjectures/edit/main/FormalConjectures/WrittenOnTheWallII/GraphConjecture322.lean
Replace the file contents with `GraphConjecture322.SOLVED.lean` from this folder.
