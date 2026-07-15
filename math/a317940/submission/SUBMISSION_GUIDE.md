# Submitting A317940 to Google DeepMind's Formal Conjectures — step by step

Everything here is prepared and format-checked against their actual
`CONTRIBUTING.md` and real solved examples (Erdős 31, 221, 268, …). Two steps
are yours by necessity and cannot be automated:

- **Signing the CLA** — a legal agreement tied to your identity.
- **Opening the issue / PR against `google-deepmind/formal-conjectures`** — it's
  an external org; the fork + PR happen under your GitHub account.

Files in this folder:
- `317940_cd729cdd.SOLVED.lean` — the exact statement file to submit (upstream
  file + the one `@[category research solved, … formal_proof …]` marker; proof
  stays external per their >25–50 line rule).
- `ISSUE.md` — the issue to open first.
- `PR.md` — the pull-request title + body.

---

## 0. Make the proof public (required)

Their `formal_proof` link must resolve for reviewers. This repo (`crl`) is
**private**, so its links won't work externally. Easiest, and matches their own
precedent (Erdős 268 links a gist):

1. Create a **public gist** at <https://gist.github.com/> containing the proof
   `math/a317940/proof/A317940_verified.lean` (name it `A317940_verified.lean`).
2. Copy its **raw/permalink URL** — this is your `PROOF_URL`.

Alternatively: push that one file to a public repo of yours, or make `crl`
public (which also makes the CI, prior-art, and project-site links resolve).

## 1. Sign the CLA

<https://cla.developers.google.com/> — individual (or your employer's, if
already signed). One-time.

## 2. Fill in the placeholders

In `ISSUE.md`, `PR.md`, and `317940_cd729cdd.SOLVED.lean`, replace:
- `PROOF_URL_PLACEHOLDER` → your public proof URL (step 0)
- `CI_RUN_URL_PLACEHOLDER` → the verify-lean run (only public if `crl` is public)
- `PRIOR_ART_URL_PLACEHOLDER`, `PROJECT_URL_PLACEHOLDER` → your public site URLs
  (or drop them if `crl`/Pages stay private — the proof link alone satisfies
  their mechanism; reviewers can re-run `#print axioms` themselves).

## 3. Open the issue

Their process is **issue first**. Paste `ISSUE.md` at
<https://github.com/google-deepmind/formal-conjectures/issues/new>. Note the
honest process question in it: A317940 sits on the `auto_oeis` branch with no
`@[category]` tags yet, so ask the maintainers whether they want the marker on
the auto file or A317940 curated into `main`. Wait for their steer.

## 4. Fork, edit, build

```bash
# after forking via the GitHub UI:
git clone https://github.com/<you>/formal-conjectures && cd formal-conjectures
git checkout -b a317940-solved <target-branch-from-issue>   # e.g. auto_oeis or main
# place the edited statement file at the path the maintainers indicate, e.g.:
cp <this-folder>/317940_cd729cdd.SOLVED.lean \
   FormalConjectures/OEIS/Auto/317940_cd729cdd.lean
lake exe cache get && lake build      # must succeed
# verify the formal_proof link opens in a browser (not broken)
git commit -am "Mark A317940 solved; link external Lean 4 proof" && git push -u origin a317940-solved
```

## 5. Open the PR

Paste `PR.md`, set base = the maintainers' chosen branch, and **link it to the
issue** (`Resolves #<n>`).

---

## Honest notes before you click submit

- **What "solved" means here:** their guide defines `research solved` as
  *"formally proved here or elsewhere."* Our proof **is** formally proved and
  kernel-verified, so this submission is legitimate and uses the exact mechanism
  they provide.
- **Novelty is a separate question.** Marking their conjecture solved only
  claims a proof exists — which it does. Whether the *argument* is novel vs. the
  literature is still the "under review" part on our own site; it does not block
  this submission, but be ready to answer reviewer questions about it (the
  prior-art check and `PRIOR_ART.md` are your material).
- **I could not, and did not, sign anything or contact their repo on your
  behalf.** These are drafts for you to review and submit.
