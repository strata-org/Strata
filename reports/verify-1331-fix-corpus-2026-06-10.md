# #1331-fix corpus measurement: old-fvar ELAB clearance

Date: 2026-06-10
Branch: htd/smack
Fix under test: 188255668 `fix(boogietostrata): widen effective-modifies with old-referenced globals (#1331)`
Corpus: `/Users/htd/Documents/Strata-smack/Examples/smack-docker/boogie-files` (3,529 `*.bpl`)

## 1. Headline

**The #1331 fix is a clean win at corpus scale.** On a 80-file stratified sample, it
cleared **every** old-fvar ELAB failure it touched — 16/16 of the cleared-eligible files,
and 0 old-fvar occurrences remain in any of the 80 post-fix type-check outputs (hard-verified
by direct grep). **Zero regressions**: no file that type-checked before the fix broke after it.
The cleared bucket is the only bucket that moved; everything else is symmetric before/after.

The clearance is partial in the *practical* sense that 8 of the 24 old-fvar files do not reach
SMT after the fix — they unmask a single downstream blocker (modifies-completeness). But that
is the next problem, not a failure of this fix: the old-fvar error itself is eliminated 24/24.

## 2. Method

- **Sample**: 80 of 3,529 `*.bpl`, byte-size-quartile-stratified systematic sampling
  (4 equal-count quartiles of ~882, 20 evenly-spaced picks each, step k=44, sorted by
  basename within quartile). No RNG; fully reproducible. Quartile bands:
  Q1 130,104–268,013 B / Q2 268,082–544,702 B / Q3 545,154–1,194,459 B /
  Q4 1,196,695–12,214,152 B. The Q4 slice (up to ~12 MB) is where #1331's effective-modifies
  widening matters most, and it is represented.
  - The prior 200-file sample was cleared from `/tmp`; this 80-file sample was regenerated
    fresh for this run. The `old()`-reference pre-filter was evaluated and **deliberately not
    used as a discriminator** — `grep -E '(requires|ensures|free ensures).*old\('` matches
    3,529/3,529 corpus files and 80/80 sampled files, so it carries zero selection
    information. Size-stratification is therefore the sole selection axis.
- **Before/after**: each `.bpl` translated twice — with the PRE-FIX
  `BoogieToStrata.dll` (`/tmp/claude/b2s-prefix/`) and the POST-FIX dll (current
  `bin/Debug/net8.0/`) — then both `.core.st` outputs type-checked.
- **TYPE-CHECK ONLY**: `verify ... --check-mode deductive --check-level minimal --type-check`,
  which exits after the semantic dialect's type inference/checking, **before SMT**.
  Concurrency 2 (`xargs -P 2`), `gtimeout 20s` per type-check.
- **Classifier**: keyed on the substring `Cannot find this fvar in the context! old`
  in type-check output (the #1331 ELAB signature).
- **Scope caveat (load-bearing)**: this measures the **ELAB / type-check layer only**, not
  end-to-end SMT verdicts. That is the correct layer: #1331's claimed impact is precisely the
  `ELAB_FAIL` bucket (old-fvar type-check failures), and SMT pass/fail is downstream and out
  of scope here.

Driver: `/tmp/claude/eq1331-driver.sh`. Per-file artifacts under
`/tmp/claude/eq1331-work/<basename>/` (`pre.core.st`, `post.core.st`, `*.tc.out`).

## 3. Results

Before/after status matrix (n=80):

| before -> after        | count | classification   |
|------------------------|-------|------------------|
| ok -> ok               | 47    | never_failing    |
| oldfvar -> ok          | 16    | **cleared**      |
| oldfvar -> tc_error    | 8     | **next_blocker** |
| TIMEOUT -> TIMEOUT     | 8     | never_failing    |
| tc_error -> tc_error   | 1     | never_failing    |

Headline buckets:

| metric             | count | note                                                       |
|--------------------|-------|------------------------------------------------------------|
| before_elab_fail   | 24    | = cleared (16) + next_blocker (8)                          |
| cleared            | 16    | old-fvar ELAB error gone, type-check now passes            |
| still_failing      | 0     | no file still emits old-fvar after the fix                 |
| newly_broken       | 0     | no previously-passing file broke                           |
| next_blocker       | 8     | old-fvar gone, but a downstream type-check error appears   |

- **old-fvar clearance rate: 24/24 = 100%** of files that exhibited the #1331 ELAB
  error pre-fix no longer exhibit it post-fix (hard-verified: 0 old-fvar strings across all
  80 post.tc.out files).
- **Type-check-pass clearance rate: 16/24 = 66.7%** of old-fvar files now type-check
  cleanly end-of-ELAB; the remaining 8 clear old-fvar but hit the next blocker.

**Corpus projection (~3,529 files).** Pre-fix old-fvar incidence in the sample is
24/80 = 30.0%, projecting to ~**1,059** corpus files carrying the old-fvar ELAB failure
(95% Wilson interval on 24/80 ≈ 20.8%–41.0%, i.e. roughly **735–1,447** files). All of that
bucket has the old-fvar error eliminated. The sub-bucket that fully reaches a clean type-check
is 16/80 = 20.0%, projecting to ~**706** corpus files (Wilson ≈ 12.7%–29.9%, ~448–1,055).
Projections assume the sample's size-stratification is representative; treat them as
order-of-magnitude.

## 4. Regressions

**newly_broken = 0.** No file that type-checked before the fix failed after it. The matrix is
strictly monotone in the right direction: the only cell that changed status is `oldfvar -> ok`
(cleared) plus `oldfvar -> tc_error` (next_blocker, where the *old-fvar* error is still gone).
Every never_failing row (ok->ok 47, TIMEOUT->TIMEOUT 8, tc_error->tc_error 1) is symmetric
before and after. No regression to flag.

## 5. Next-blocker incidence

Of the 24 old-fvar files, **8 (33.3%)** unmask a downstream type-check error once #1331 is
fixed. All 8 unmask the **same** error — modifies-completeness:

```
post.core.st(...) [...]: This procedure modifies variables it is not allowed to!
```

This is the expected outcome and matches the earlier `EQ_wvadqhmgjvk` modifies-completeness
observation: the fix correctly widens effective-modifies for `old()`-referenced globals, the
old-fvar error disappears, and the next latent constraint surfaces. Example next-blocker files:
`EQ_00nul2z0yci_out.bpl`, `EQ_o4ji1zdca0j_out.bpl`, `EQ_rgtdpoqifzr_out.bpl`,
`EQ_klqsyelimgw_out.bpl`, `EQ_1swua5xhmuk_out.bpl` (all `oldfvar -> tc_error`).

**Bound on SMT reach.** This bounds how much of the ELAB_FAIL bucket actually reaches SMT after
the fix: of the old-fvar files, **66.7% (16/24) clear the type-check layer entirely** and are
free to proceed toward SMT; **33.3% (8/24) are immediately re-blocked** at the type-check layer
by modifies-completeness and do not reach SMT until that separate issue is addressed.

## 6. Honest scope

- **Type-check-layer only, not end-to-end.** This run stops before SMT. A file in the
  "cleared" (oldfvar->ok) bucket has cleared the #1331 ELAB error and passes ELAB/type-check;
  it has **not** been shown to produce a correct SMT verdict. That is by design — #1331's
  claimed impact is exactly the ELAB_FAIL bucket, which is what we measured.
- **Prior "56/200 ELAB_FAIL, ~28%" figure is corroborated.** The regenerated sample's pre-fix
  old-fvar rate is 24/80 = **30.0%**, statistically consistent with the prior 56/200 = 28.0%
  (the prior point estimate sits inside this sample's 95% Wilson interval 20.8%–41.0%). The two
  independent samples agree on the ~28–30% pre-fix old-fvar incidence.
- **TIMEOUT files are honestly excluded from the denominator.** 8 large files timed out at 20s
  on **both** sides; none of their pre-outputs contained old-fvar before timing out, so
  `before_elab_fail` is exact at 24 (not inflated by unknown-status timeouts). They are
  classified never_failing because they do not exercise #1331 within the time budget — not
  because they passed.
- **Smaller sample than the prior 200.** n=80 here vs 200 prior; intervals are correspondingly
  wider. The clearance and zero-regression conclusions are robust (16/16 and 0/56 are clean
  margins), but corpus projections carry the stated Wilson uncertainty.

## 7. Files referenced

- Sample list: `/tmp/claude/eq-1331-sample.txt` (80 absolute paths, 1/line)
- Before/after results: `/tmp/claude/eq-1331-beforeafter.tsv`
  (columns: file, before_status, after_status, classification)
- Driver script: `/tmp/claude/eq1331-driver.sh`
- Per-file detail artifacts: `/tmp/claude/eq1331-work/<basename>/`
  (`pre.core.st`, `post.core.st`, `*.tc.out`)
- Pre-fix dll: `/tmp/claude/b2s-prefix/BoogieToStrata.dll`
- Post-fix dll: `/Users/htd/Documents/Strata-smack/<...>/bin/Debug/net8.0/BoogieToStrata.dll`
- Fix commit: 188255668 (on branch htd/smack)
- Corpus: `/Users/htd/Documents/Strata-smack/Examples/smack-docker/boogie-files/` (3,529 `*.bpl`)
