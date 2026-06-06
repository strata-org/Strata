# EQ_*_out autonomous-closeout final synthesis (2026-06-05)

This is the final roll-up of the multi-phase autonomous run that exercised the
EQ_*_out corpus through Strata's verifier on htd/smack, drove two upstream-style
fixes (the SO/`balancedNondetIte` change at 494cf1147 + 346f55083, and the
side-branch decimal e-15 fix at 6f5e74fa6), and stratified the
remaining failure modes. All file paths below are absolute. Dates are 2026-06-05.

---

## 1. Headline

- **One real fix landed end-to-end with a measurable verdict shift.** The
  decimal e-15 emission fix (side-branch htd/decimal-e15-fix, commit
  6f5e74fa6) shifted 4/10 e-bearing baselines from non-PASS to PASS and
  cleaned residual `e-` parse-error noise from a 5th, with **zero
  regressions**. Issue draft pinned to origin/main2 HEAD dda37e4f3
  is staged at /Users/htd/Documents/Strata-smack/strata-decimal-e15-emission-bug.md
  and is filable as-is.
- **The SO fix is a crash-suppressor, not a verdict-restorer for SO files.**
  494cf1147 + 346f55083 turn the rc=134 SIGABRT into a silent 120 s
  TIMEOUT on all 7 known SO reproducers under the realistic
  `bodyOrContract / inline-fuel 100 / minimal` flag set. End-to-end correctness
  is not demonstrated for these files; the crash is gone but no SMT verdict is
  reached. The fix is still upstream-worthy (no SO regressions across the 94-file
  matrix), but the SO files themselves are now TIMEOUT-bound rather than
  PASS-reaching.
- **The contract-mode "PASS" majority is mostly an artifact.** The
  vacuous-PASS rate at n=22 stratified across families is **81.2 % strict
  (Wilson 95 % CI [57 %, 93 %])**, rising to 87.5 % once one Δ=0
  compound-vacuous case is included. Most of Aaron's contract-mode green
  is translation-time UF-shadowing, not soundness signal. The Tier-1
  Java-SMACK 28-file sweep gives the corpus its first non-vacuous PASS
  rate floor — **25 % real-PASS, 0 % vacuous-PASS** — and surfaces a
  new structural failure mode (`old`-of-non-modifies-fvar elab-fail, 6/28).

---

## 2. Probe 1 verdict — does the SO fix close end-to-end?

**No.** The SO fix is a true crash-suppressor on these 7 files but does not
restore a definite verdict under realistic flags within 120 s.

Flags (all 7): `--check-mode deductive --check-level minimal --call-policy bodyOrContract --inline-fuel 100`.
Wall timeout 120 s via gtimeout.

| File | TX rc | TX time | VER rc | VER time | stdout B | stderr B | Verdict |
|---|---|---|---|---|---|---|---|
| EQ_2zvm5xvfu22_out | 0 | 20 s | 124 | 122 s | 0 | 0 | TIMEOUT |
| EQ_wnksggs1hpx_out | 0 | 16 s | 124 | 120 s | 0 | 0 | TIMEOUT |
| EQ_cvrikypthwe_out | 0 | 21 s | 124 | 121 s | 0 | 0 | TIMEOUT |
| EQ_2aa5bx1uwko_out | 0 | 21 s | 124 | 121 s | 0 | 0 | TIMEOUT |
| EQ_wfgmxv3m3tx_out | 0 | 18 s | 124 | 120 s | 0 | 0 | TIMEOUT |
| EQ_sertrlracdg_out | 0 | 21 s | 124 | 121 s | 0 | 0 | TIMEOUT |
| EQ_0xaksnfuqqv_out | 0 | 21 s | 124 | 121 s | 0 | 0 | TIMEOUT |

Aggregate: 0/7 PASS, 0/7 PARTIAL, 0/7 FAIL, **7/7 TIMEOUT, 0/7 CRASH**. All 7
produced zero-byte stdout and zero-byte stderr — verifier is silently working
through the pipeline when the wall fires. No SMT verdict line, no progress line.

The fix (balancedNondetIte in Core.lean lines 185-189, validated against the
2.86 M-block depth driver in Probe 4) is doing its job: rc=134 SIGABRT is
absent everywhere on the 94-program matrix (68 PASS / 11 PARTIAL / 0 FAIL,
bit-identical to pre-fix where pre-fix returned a verdict). What it does *not*
do for SO reproducers is make them fast enough under inline-fuel-100 to hit a
verdict in 2 minutes. Whether the 120 s budget is dominated by
bodyOrContract inlining cost or by SMT cost is an unanswered question — a
follow-up under `--profile` or `--no-solve` (or a 600 s budget on one or two
files) would discriminate. That follow-up is logged as the "Next action" on
the SO BACKLOG entry.

Artifacts: /tmp/claude/probe1/run_one.sh, .meta/.core.st/.verify.{log,err}/
.translate.log per file.

---

## 3. Probe 2 / E-15 verdict — did the decimal fix work?

**Yes, strongly.** Side-branch htd/decimal-e15-fix at commit 6f5e74fa6
(/Users/htd/Documents/Strata-decimal-e15-fix) drops the [-5, 5] exponent
bounds and the `s!"{m}e{e}"` scientific-notation fallback in
Strata/DDM/Util/Decimal.lean. `lake build strata` completes 540/540 jobs.

| # | File | Before | Before-elapsed | After | After-elapsed | Shift |
|---|---|---|---|---|---|---|
| 1 | EQ_032wuerhmvw | TIMEOUT (silent) | 60 s | TIMEOUT (silent) | 60 s | unchanged |
| 2 | EQ_0agwqtm2bcg | TIMEOUT (silent) | 60 s | TIMEOUT (silent) | 60 s | unchanged |
| 3 | EQ_0c53ogei0g4 | TIMEOUT (`e-8` evidence) | 60 s | TIMEOUT (clean) | 60 s | improved (noise gone) |
| 4 | EQ_0exak45poxy | PARTIAL (261/261 fail w/ `e-15`) | 51 s | **PASS** (All 261) | 8 s | PARTIAL → PASS |
| 5 | EQ_0fmj2meb0oj | TIMEOUT (`e-14` evidence) | 60 s | **PASS** (All 609) | 56 s | TIMEOUT-e → PASS |
| 6 | EQ_0gsuem3slyl | FAIL (typecheck, unrelated) | 1 s | FAIL (typecheck) | 1 s | unchanged (predicted) |
| 7 | EQ_0q0oga15aij | TIMEOUT (`e-14` evidence) | 60 s | **PASS** (All 524) | 41 s | TIMEOUT-e → PASS |
| 8 | EQ_0rvvwfsfv2r | TIMEOUT (silent) | 60 s | TIMEOUT (silent) | 60 s | unchanged |
| 9 | EQ_0stx52y505t | TIMEOUT (silent) | 60 s | TIMEOUT (silent) | 60 s | unchanged |
| 10 | EQ_0z42qdmejd0 | TIMEOUT (`e20` evidence) | 60 s | **PASS** (All 598) | 23 s | TIMEOUT-e → PASS |

**4 of 10 verdict-shifts to PASS, 1 of 10 noise-cleanup, 0 of 10 regressions.**
All 5 files with e-evidence in baseline shifted toward green. The 4 silent
TIMEOUTs (032w, 0agw, 0rvv, 0stx) had no e-evidence either side — fix isn't
their problem and no shift attribution is claimed. EQ_0gsuem3slyl was
predicted not to shift (translator typecheck error, unrelated) and didn't.

Issue draft pinned to **origin/main2 HEAD dda37e4f3a9ae4ec4534d531d5ca1e6ef73d40fd**
is at /Users/htd/Documents/Strata-smack/strata-decimal-e15-emission-bug.md.
Note that the smack-branch path Strata/DDM/Util/Decimal.lean differs from the
main2 path StrataDDM/StrataDDM/Util/Decimal.lean (post-extraction in PR #1221);
the issue draft pins lines correctly to main2 (bounds at L27/L29, fallback at L50).
Minimal Boogie reproducer is at /tmp/claude/e15-repro/repro.bpl (9 lines).
Pre-fix on smack: rc=3, 1 SMT Solver Crash, SMT-LIB line 4 carries bare
`3141592653589793e-15` symbol. Post-fix: rc=0, all 1 goal passed, SMT-LIB emits
`3.141592653589793` (valid decimal).

---

## 4. Probe 3 verdict — vacuous-PASS rate

**81.2 % strict, 87.5 % including the 1 confirmed Δ=0 compound-vacuous case.**
The v2 §1.4/§2 projection of 60-100 % vacuous-PASS is confirmed at n=22 with
95 % CI floor of 57 %.

Method: 22 deep-dived files spanning v1 batch 1 + batch 2 + v2-named, run twice
each under `--check-mode deductive --check-level minimal --inline-fuel 100
--solver-timeout 50` with policy ∈ {contract, bodyOrContract}. Total wall: ~110 s
for 44 jobs (P=8). All translations done fresh against current htd/smack.

Aggregate by verdict-flip class:

- **Total contract-PASSes:** 16 / 22
- **Vacuous (contract-PASS → bodyOrContract non-PASS):** 13 — strict rate 13/16 = **81.2 %**
- **Δ=0 body-eval no-op (compound-vacuous):** 1 (jxsw3zuslgt) — adjusted rate 14/16 = **87.5 %**
- **Both PASS with substantive body expansion:** 2 (vtepk5bv3ld Δ=+1236, ylzs20xcwwt Δ=+414) — possibly real, possibly precision-tax-vacuous (v1 §ike-1122 mechanism)
- **Contract non-PASS (informative regardless of policy):** 3
- **FAIL-elab (uninformative):** 3

**Family skew is sharp:**
- Java-SMACK: 6/6 contract-PASSes vacuous (100 %); all flip to TIMEOUT under bodyOrContract.
- CLEVER+REVE+dart+bess synthetic: 6/7 vacuous (the lone exception jxsw3zuslgt is also compound-vacuous).
- Substantive both-PASS: 2 REVE files only.

This **reframes the corpus methodology**: contract-mode "PASS" verdicts are
*not* soundness signals on their own. Aaron's existing v2 narrative was right
in direction; the n=22 result puts a confidence interval on it.

Artifacts: /tmp/claude/probe3_files.txt, /tmp/claude/probe3_results.txt,
/tmp/claude/probe3_logs/runs/*.log, /tmp/claude/probe3_translate.sh,
/tmp/claude/probe3_verify.sh.

---

## 5. Tier-1 outcomes

### 5.1 A3 — pinned-solver-options witness extraction (5 new files + 2 v2-prior)

**Verdict: v2's narrow claim holds and generalizes within a file.** 6/7 files
yield z3-default sat witnesses on every ensures_0 path tested; 1/7
(EQ_vtepk5bv3ld) is no longer PARTIAL on this run (all 1516 goals PASS at full
bodyOrContract+inline-fuel-100). Per-file: REVE.addhorn (3/3 sat, bv32 zero
witnesses), tsafe.normAngle pair 0exak/s541 (5/5 each, but contaminated by
the orthogonal e-15 emission bug — see §3), bess.pythag (9/9 sat, Real-typed
Skolem-witnessed `_return` divergence), CLEVER.getSign2 bhx (10/10 sat,
re-confirmed). Path-uniformity within a file is real: all paths within a
Neq.SameV procedure flip together. The "solver-options artifact" is per-file,
not per-path.

### 5.2 A6 — [INLINE-CALL] vs [CFG-CALL] counter mismatch

**Verdict: explained-and-benign — close.** The 1131 vs 1552 gap reported in
Probe-4 is two counters measuring different axes. `[INLINE-CALL]`
(StatementEval.lean:826) fires once per `inlineCallBody` invocation regardless
of body shape. `[CFG-CALL]` (StatementEval.lean:777-780) fires once per
recursive entry of `evalCalleeCFG` — so each top-level `.cfg`-body callee
produces (rounds_to_drain + 1) events. Each `condGoto` fork at line 758 adds
an extra round; 76 `[CFG-CONDGOTO]` events were observed, consistent with
(rounds_per_walk × walks) = 1552. `.structured`-body callees contribute
nothing to `[CFG-CALL]`. No gating divergence, no leak, no perf opportunity.

### 5.3 Java-SMACK 28-file sweep

**Verdict: corpus is not a uniform hard-failure cohort.** Aggregate at n=28:

| verdict | count | rate |
|---|---:|---:|
| PASS (real-proof) | 7 | 25.0 % |
| PASS-? (vacuous) | 0 | 0.0 % |
| PARTIAL | 1 | 3.6 % |
| TIMEOUT (verify) | 11 | 39.3 % |
| TIMEOUT* (post-fix slowdown ≥4 MB) | 3 | 10.7 % |
| elab-fail (`old`-of-fvar) | 6 | 21.4 % |
| SO / FAIL / true-translation-fail | 0 | 0.0 % |

PASS rate 25 %, PASS+PARTIAL 28.6 %. **0 stack-overflow regressions across
the sample** (the SO fix in 277c468cb holds). Two new failure modes named:
(a) **`old`-of-non-modifies-fvar elab-fail** — `Cannot find this fvar in the
context! old <var>`, distinct from #1162 and the older CFG-body SKIP, smallest
clean repro EQ_w5qckr4iugx_out.bpl at 237 KB; (b) **fix_core_st.py
super-linear-regex slowdown** on ≥4 MB Boogie inputs, tooling-side.

This **invalidates v2 §1.3's "every Java-SMACK file with a known verdict is
a hard failure" claim** — that was an artifact of pre-SO-fix data. v2 §1.3
should be rewritten with the n=28 size-stratified profile.

Artifacts: /tmp/claude/final_results.csv, /tmp/claude/sweep.log,
/tmp/claude/rerun.log.

---

## 6. What's now closed

The following backlog items are settled by this autonomous run and the
docs-update commit 6daa32e1b on htd/smack:

- **EQ-pipeline blocker triage** — RESOLVED-PROVISIONAL. Two upstream-style
  fixes (SO crash-suppressor 494cf1147 + 346f55083; e-15 emitter side-branch
  6f5e74fa6) are validated; vacuous-PASS rate quantified at 81 %; corpus
  methodology updated.
- **SMT2 e-15 emission bug** — promoted from OPEN to FILED-DRAFT-READY with
  side-branch SHA + 10-file validation table (4 PASS + 1 noise-cleanup + 0
  regressions).
- **[INLINE-CALL] vs [CFG-CALL] counter-axis mystery** — closed as
  explained-and-benign (Tier-1 A6).
- **SO BACKLOG entry** — refreshed with structured upstream-filing template
  citing 494cf1147, all 7 reproducers, Probe-4 localization at
  Core.lean:185-189, 94-program matrix validation (68 PASS / 11 PARTIAL / 0 FAIL).
- **Pinned-solver-options witness audit** — closed at n=7 with the caveat that
  v2's "all 6 untested files share ike's encoding shape" claim is false for
  the tsafe.normAngle pair (different defect, separate fix landed).
- **Body-eval cost regression entry** — partially resolved by Probe-1
  Java-SMACK TIMEOUT confirmation (the cost is real on those 7 SO files;
  exact phase distribution still TBD via a `--profile` follow-up).

---

## 7. What's newly open

The autonomous run surfaced these anomalies that did not exist as backlog
items before:

1. **`old`-of-non-modifies-fvar elab-fail (6/28 in Tier-1 sweep).** Verifier
   emits `❌ Type checking error … Cannot find this fvar in the context! old <var>`
   on the first ensures clause and aborts (rc=3). Distinct from #1162
   (`__nondet`) and from CFG-body SKIP. Affected size range 237 KB → 2.7 MB.
   Smallest clean repro: /tmp/claude/sweep/EQ_w5qckr4iugx_out_fixed.core.st.
   Worth a separate ticket once Strata's `--smack` `InferModifies` path is
   audited.
2. **fix_core_st.py super-linear-regex slowdown on ≥4 MB Boogie inputs**
   (3/28). Translation succeeds but post-processing wedges; on the 4.3 MB
   input, fix takes ~205 s, the resulting 21 MB `.core.st` then verify-TIMEOUTs
   at 90 s. Tooling-side, not verifier-side. Worth filing if Strata-Smack is
   a customer-facing path.
3. **Probe-1 follow-up: where does the 120 s go for SO files?** All 7 SO
   reproducers TIMEOUT silently with zero-byte stdout/stderr at full-flag
   verify. Need a `--profile` or `--no-solve` run on one or two files to
   discriminate "stuck in transform" from "stuck in solver" — currently
   logged on the SO BACKLOG entry as the "Next action".
4. **`❓ unknown` bucketing.** EQ_m4ey1eyuxpx_out (Tier-1 #9) hit 21 783 PASS +
   1 unknown — currently lumped with PARTIAL but arguably a separate
   Z3-undecidable bucket. Spec-side decision pending.
5. **vtepk5bv3ld and ylzs20xcwwt substantive both-PASS verdicts.** Possibly
   real PASSes, possibly precision-tax-vacuous (v1 §ike-1122 mechanism). Per-goal
   SMT inspection would discriminate; not done here.

---

## 8. Filing readiness table

| Issue | Status | Branch / Commit | Repro | Validation | Filable? |
|---|---|---|---|---|---|
| SMT2 e-15 emission bug | DRAFT-READY (.md only) | side: htd/decimal-e15-fix @ 6f5e74fa6 | /tmp/claude/e15-repro/repro.bpl | 10-file: 4 PASS + 1 noise-clean + 0 regress | YES — pinned to main2 dda37e4f3 |
| SO crash (`balancedNondetIte`) | RESOLVED, upstream-template ready | smack: 494cf1147 + 346f55083 | 7 reproducers in BACKLOG | 94-program matrix bit-identical | YES — once body-eval cost characterized |
| `old`-of-non-modifies-fvar elab-fail | NEW, repro isolated | n/a (smack, current HEAD) | EQ_w5qckr4iugx_out.bpl (237 KB) | 6/28 in sweep | NEEDS root-cause (likely InferModifies) |
| fix_core_st.py super-linear regex | NEW, tooling-side | n/a | EQ_al4gmsai0vw_out (4.3 MB) | 3/28 in sweep | YES — narrow tooling fix |
| Pinned-solver-options witness drift | RESOLVED in narrow-claim sense | n/a | a3/{ike,bhx,mtonvj,0exak,s541} VC dir | 6/7 generalize, 1/7 contaminated | NO — empirical only, no code fix |
| `❓ unknown` bucketing decision | OPEN-spec | n/a | m4ey1eyuxpx | 1 obligation in 28-file sweep | NEEDS spec call |

The SO upstream issue is filable today on its own merits (no SO regressions;
clean root cause at Core.lean:185-189; 94-program validation). Filing it
*before* characterizing where the residual 120 s goes for SO files would
under-sell the work — the body-eval cost story belongs in the same ticket.
Recommendation: bundle Probe-1 follow-up into the SO upstream filing once
the `--profile` discrimination is in hand.

---

## 9. Recommended next steps

In order of ROI:

1. **File the e-15 issue today.** Effort: ~10 min (the .md is staged at
   /Users/htd/Documents/Strata-smack/strata-decimal-e15-emission-bug.md,
   pinned to origin/main2 dda37e4f3; minimal repro is 9 lines; side-branch
   commit 6f5e74fa6 is push-ready). ROI: high — 4 verdict-shifts already
   demonstrated, zero regressions, narrow scope (Decimal.lean bounds + fallback),
   and the fix is a 3-line change. This is the cleanest "small fix, broad
   shift" deliverable in the run. After filing, push htd/decimal-e15-fix and
   open a PR against main2 with the 10-file validation table inline.

2. **Run the Probe-1 follow-up to discriminate SO file 120 s budget.**
   Effort: ~30 min (run one or two of the 7 SO reproducers under
   `--profile` or `--no-solve` with a 600 s budget; classify time spent in
   transform vs VC-gen vs SMT). ROI: medium-high — unblocks the SO upstream
   filing, which is currently 80 % drafted but missing the body-eval cost
   characterization. Files of interest:
   /tmp/claude/probe1/EQ_2zvm5xvfu22_out.* (smallest, 20 s translate). Once
   classified, the SO upstream issue can be filed with both the crash-fix
   and a quantified post-fix latency story.

3. **Audit the `old`-of-non-modifies-fvar elab-fail at n=6.** Effort: ~1 h
   (read the smallest repro EQ_w5qckr4iugx_out.bpl at 237 KB; trace
   InferModifies; check whether `--smack` is emitting `ensures` clauses
   referencing variables not in `modifies` and whether the elaborator
   should be extending the typing context for those, or whether
   BoogieToStrata should be filtering them out). ROI: medium — 21 % of the
   Tier-1 Java-SMACK sample is gated on this. Likely fix locale: BoogieToStrata
   InferModifies pass or Strata's ensures-elab.

The remaining items (`❓ unknown` bucketing spec call, vtepk/ylzs precision-tax
inspection, fix_core_st.py regex audit) are lower-ROI and can wait for the
next session.

---

*End of autonomous-closeout synthesis. All claims above are either empirically
verified by the artifacts cited (Probe 1, Probe 2 baseline + post-fix, Probe 3
44-job matrix, Tier-1 A3 / A6 / 28-file sweep) or structurally inferred from
the verifier source at the line-numbers cited and labeled as such. Where v2
§1.3 / §1.4 claims have shifted (Java-SMACK no-PASS framing; tsafe.normAngle
encoding-shape generalization), the new data takes precedence and the BACKLOG
+ INDEX commits at 6daa32e1b reflect that.*
