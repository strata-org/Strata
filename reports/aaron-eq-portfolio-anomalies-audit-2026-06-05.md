# EQ Portfolio: Unified Anomalies Catalog

*Audience: lead developer who already read the v2 synthesis. This is what's actually left, ranked.*

---

## 1. Headline

**Settled (act-on / file-or-archive):**
- Multi-`Env` is sound. 30/72 verdict-differ, but every divergence reduces to a pre-existing latent defect or a precision-restoring change. The branch ships.
- Four root causes filed or fix-ready: stack-overflow in body-eval (RESOLVED, htd/smack@494cf1147); `old(<unmodified-global>)` elab defect (FILED, #1331); SMT2 scientific-notation emission `e-15` (DIAGNOSED to single line, `Strata/DDM/Util/Decimal.lean:50`); `multiple_Eq_SameV` harness mis-construction (FOR AARON).
- Vacuous-PASS via shared UF, on the `_uf_otherfile_*` namespace, mechanically confirmed via SMT-LIB inspection.
- The `--check-level minimal` baseline is verdict-equivalent to `full` on the 3 PARTIALs probed; cost regression cluster (5 files) clears at 60s under minimal.

**Still open and load-bearing:**
- The SO "fix" converts SIGABRT → TIMEOUT-no-verdict on the affected files; whether any reach a verdict under any flag combination is unmeasured.
- The 72-file sample is not representative — synthetic-benchmark family is over-weighted **2.5×** vs corpus, Java-SMACK is under-weighted **0.63×**. Every "X% of corpus" projection in v1/v2 is mis-attributed.
- The 6 other Neq.SameV PARTIAL files inherit the `INT_MIN`/`INT_MAX` axiom-gap diagnosis from probe-extrapolation on 2 files only; structurally inferred, not directly run.
- v2 §7's SO predictor ("fork-at-two-target-goto") is process-of-elimination on 15 static features; the actual fix that landed was at a different layer (foldl-tree depth in `inlineCallBody`), so the predictor is now lineage-detached from the fix and unverified.
- ~333/3,529 corpus files hit the `e-15` SMT-emission bug; impact is high-leverage but un-measured corpus-wide.

**One-line recommendation:** Don't close the EQ-portfolio backlog item on the SO fix alone. Three probes (~3 hours total — items #1, #5, #6 in §6 below) convert the headline projections from "extrapolated" to "measured" and would let the lead developer either ship-and-archive or escalate concretely.

---

## 2. Resolved Since v2 (Brief Recap)

| item | status | evidence |
|---|---|---|
| Stack-overflow under `bodyOrContract` | RESOLVED on htd/smack@494cf1147 (balancedNondetIte) | 3 Java-SMACK files (EQ_2zvm5xvfu22, EQ_2aa5bx1uwko, EQ_00b1txorhee) now produce PASS-? at rc=0 instead of SIGABRT; elapsed 189–579s |
| `old(<unmodified-global>)` elab defect | FILED upstream as #1331 (2026-06-05) | Verified to reproduce on origin/main2@4e4ceb9d1 with 5-line MWE; fix path identified in `Tools/BoogieToStrata/Source/StrataGenerator.cs:1798-1813` |
| SMT2 `e-15` emission bug | DIAGNOSED to single line | `Strata/DDM/Util/Decimal.lean:50` — `else s!"{m}e{e}"` fallback when `\|exponent\| > 5`; affects ~333 corpus files (9.4%) per literal-exponent histogram |
| Java-SMACK 0/0 hard-fail framing | INVALIDATED | Three sampled files (n=3 of 36) now reach PASS-?; v2 §1.3's "Java-SMACK has zero known PASSes" claim needs refresh post-SO-fix |
| Cost regression on bodyOrContract | RESOLVED via `--check-level minimal` | 5/5 cost-regression files clear at 60s under minimal+bodyOrContract+fuel100; including `mtonvj3sujq` which v1 flagged as eval-side blow-up — was full-driven, not eval pathology |
| Neq.SameV "with witnesses" claim | DOWNGRADED | Witness extraction probe on 2 of 7 files (bhx22kvwuqp, pyafkjy4xny): under z3-default, 4 of 6 paths flip to sat-with-concrete-counterexample on path 1316; pinned `--check-level full` solver options suppress otherwise-decidable instances |

---

## 3. Open Anomalies — Empirically Grounded

These are anomalies where the evidence is direct (not extrapolated). Each row is a real measurement on real files.

| anomaly | evidence | scope | open question | VoI | probe cost |
|---|---|---|---|---|---|
| **A1. SO "fix" converts SIGABRT → TIMEOUT-no-verdict** | All 7 SO reproducers now exit rc=124 under default flags. Java-SMACK probe used 120s/proc and split-procs to reach PASS-?. Single-binary `strata verify` at 60s on a non-split file is unmeasured. | 7 reproducers; corpus-wide unknown | Under `minimal --call-policy bodyOrContract --inline-fuel 100` at 120s, do any of the 7 reach a *verdict* (PASS / FAIL:N / PARTIAL), or do they all TIMEOUT? | **HIGHEST.** A "fix" that converts crash → silent timeout is barely a fix; settles whether the fix is end-to-end or surface-level | ~30 min |
| **A2. SMT2 `e-15` emitter bug, corpus-wide impact unmeasured** | Single offending line at `Strata/DDM/Util/Decimal.lean:50`. Histogram across 3,529 corpus files: 1,288 occurrences of `e-8`, 1,049 of `e-15`, 916 of `e-14`, 896 of `e-16`. 333 files (9.4%) have at least one literal with `\|exp\| > 5`. | ~333 files corpus-wide | Of those 333 files, how many produce a wrong verdict (PARTIAL / FAIL where PASS would be correct) under either call-policy? Does the fix turn them green or just stop the silent free-symbol injection? | **HIGH.** Single-line fix, double-digit-percent corpus impact, soundness-relevant (silent goal-retyping) | <1 hr to fix + sweep |
| **A3. Pinned solver options suppress decidable counterexamples** | Witness probe on EQ_bhx22kvwuqp + EQ_pyafkjy4xny: 4 of 6 paths flip from `unknown/unknown` (pinned options) to `sat/sat` with concrete witness (z3 default) on validity check. Witness shape: `_in_param=0x00000000`, `INT_MIN`/`INT_MAX` allowed non-canonical bv32. | 2 of 7 Neq.SameV PARTIALs measured; other 5 inferred (same encoding) | On the other 5 Neq.SameV PARTIAL files (jk0xftyhwbe, lamphgicbh5, plus the 3 batch-2 reproducers from §1.4), does the same option-stripping flip path verdicts? Should Strata add INT_MIN/INT_MAX value-pinning axioms instead of relying on z3 mbqi heuristics? | **HIGH.** Reframes "PARTIAL because solver timed out" as "PARTIAL because the SMT encoding is incomplete." UX implication: bodyOrContract could surface real witnesses instead of `❓` shrugs | ~1 hr |
| **A4. Sample stratification mis-attributes 100% of v1/v2 corpus projections** | Family classification on 3,529 corpus files: synthetic-benchmark = 707 (20.0%), Java-SMACK = 2,811 (79.7%), other = 11. Sample is 50/50. Line-count axis: small-bucket is 33% of sample, **3.9% of corpus** (8.6× over). | All v1/v2 corpus-extrapolated rates | Are sample within-family rates corpus-stable? (Yes for SO at 100% Java-SMACK; uncertain for everything else.) Re-sweep with corpus-weighted family/size split — what does the headline divergence rate become? | **HIGH for corpus-scale claims.** Within-family rates survive intact; whole-corpus extrapolations under-estimate Java-SMACK clusters by ~60% and over-estimate synthetic clusters by ~150% | ~3 hr (full re-sweep) |
| **A5. 2.86M deferred obligations on an 8.2K source body** | Probe-4 instrumentation on EQ_2aa5bx1uwko: `blocks=2,857,392 deferred=2,857,392 finished=40` — i.e., ~71,000 obligations per CFG completion on a single 8.2-KB EQ-reachable body. | 1 file directly measured | Is 71k-per-completion universal for Java-SMACK shape, or is this file an outlier? Is the multiplier deferred-list duplication, fork-fanout multiplication, or accumulator non-clearing? | **MEDIUM.** Soundness-relevant if outlier (suggests a leak); benign if uniform (suggests cost-dominant pathology) | ~30 min on 5 control files |
| **A6. inlineCallBody vs evalCalleeCFG mismatch** | Probe-4: 1,131 inline-call expansions vs 1,552 CFG call-frames on the same run — 421 callee-CFG forks proceed without an inline-body expansion. | 1 file directly measured | Is `[INLINE-CALL]` gated by a condition that `[CFG-CALL]` isn't? Or is one path divergent across the two call-handling arms? | **MEDIUM.** The two counters should be coupled; they aren't. Worth a probe even after the SO fix lands | ~1 hr (read inlineCallBody) |
| **A7. `[ITE-FORK]` count = 0 despite 2.86M deferred** | Probe-4: zero structured-ITE fires on a run that produces 1,552 `[CFG-CALL]` and 76 `[CFG-CONDGOTO]`. | 1 file directly measured | Is structured-ITE dead code on Java-SMACK shape (CFG-lowered too aggressively for it to fire), or is it gated incorrectly? | **LOW-MEDIUM.** Structurally noteworthy; only mildly surprising given Boogie shape | ~30 min |
| **A8. PARTIAL is `❓ unknown`, not `❌`, with no witness extraction** | CLI prints no model, no Counterexample, no input values; witness-extraction code path exists but is gated on `.sat`, not `.unknown`. v2 §5 confirmed verbatim. | All 7 Neq.SameV PARTIALs | Should body-eval surface witnesses when reachable in eval (e.g., `f(2,0)` for `addhorn.Neq.SameV`)? Connects to A3 — fixing pinned-options suppression converts most of these to `❌`-with-witness. | **MEDIUM.** UX-level; the more fundamental question is A3 | covered by A3 |
| **A9. Cost regression cluster: `mtonvj3sujq` at 94.2s eval-only** | A/B on EQ_0exak45poxy: full=60s TIMEOUT, minimal=23.1s + 2020 passed/1 failed. But mtonvj3sujq's `--no-solve` eval-time alone is 94.2s, exceeding 60s budget. | 1 of 5 cost-regression files | Does mtonvj3sujq scale with `--inline-fuel`, or is the eval-side cost intrinsic (separate from the SMT-side `--check-level` axis)? Is this representative or a long-tail outlier? | **MEDIUM.** If outlier, archive; if representative, it inverts the v2 §8.5 framing for largest files | ~30 min |
| **A10. Branch ref staleness in upstream filings** | Batch-2 report pinned to htd/smack@5648bdf62; current HEAD is 4 commits ahead. None touch Verifier/Options, but any re-run for filing should re-pin. | N/A (process) | Are the upstream filings (#1331, future SO/e-15) re-pinned to a stable commit on origin/main? | **LOW** but cheap | <5 min |

---

## 4. Open Anomalies — Structurally Inferred

These are claims v1 or v2 made that are *load-bearing for any scaling decision* but rest on extrapolation rather than direct measurement. Ranked by how much rests on each.

| inferred claim | source | n directly measured | n claimed | what would falsify it |
|---|---|---|---|---|
| **I1. SO predictor: "fork-at-two-target-goto on EQ-reachable bodies ≥~8 KB with symbolic-equality preconditions"** | v2 §7 process-of-elimination | 15 static features on 15 files; **0** runtime branch-spawn measurements | All Java-SMACK SO behavior | Branch-spawn counter shows the 7 SO files have no per-fork rate increase relative to controls; or controls show identical rates without crashing. The actual fix landed at foldl-tree depth in `inlineCallBody`, not branch-spawn — so the predictor is unverified post-fix. |
| **I2. 30% verdict divergence on 200-file sweep** | v2 §8.4, calibrated on 22 known-verdict | 22 of 72 (or 50/72 if you trust batch-2's stride sample) | All 200 in projected re-sweep | Re-running the existing 72 (not just the 22 deep-dived) at minimal+bodyOrContract+fuel100 produces a measured rate, replacing the projection |
| **I3. 60-100% of contract-PASS files are vacuous** | v2 §1.4 / §2.5 — confirmed mechanically on **1** file (EQ_jxsw3zuslgt) via SMT-LIB inspection | 1 file | All 72/72 contract PASSes | Run the 22 deep-dived files under bodyOrContract; count contract-PASS files that flip to PARTIAL/different verdicts. The shared-UF *mechanism* is universal (all `_uf_otherfile_*` declarations are corpus-uniform) so the lower bound is plausibly 100%; what's unmeasured is whether bodyOrContract surfaces it for files Aaron designed to be "actually equivalent" |
| **I4. e-15 corpus impact: ~333 files convert from `unknown` → green** | Histogram on 3,529 corpus files | 0 files run post-fix (fix not applied yet) | 333 | Apply the one-line fix locally; re-run 5–10 of the 333 affected files; count verdict shifts |
| **I5. Goal-fanout is uniformly 5× per ensures × per stub × per side** | v2 §6 measured on EQ_ike2wen0cz0 only | 1 file | All 6 PASS-with-shape-divergence files | Re-run goal-counting on the other 5 (267→1122-ratio cluster) and confirm 5× holds. Cheap; falls out of A4's re-sweep for free |
| **I6. The 7 Neq.SameV PARTIALs all share INT_MIN/INT_MAX axiom gap** | A3 probe ran 2 of 7 (bhx22kvwuqp, pyafkjy4xny); inferred for 0exak45poxy, s541ce4abnj, vtepk5bv3ld, mtonvj3sujq | 2 of 7 | All 7 | Run option-stripping probe on the other 5; expected 4-of-6 path flip on each |
| **I7. PARTIAL/SO-cluster sizes corpus-wide** (Java-SMACK 100% SO inferred → ~547 files) | Within-family rate × corpus weight | 8 of 36 sample known-fail; 0 unknown-verdict measured | 547 corpus | Run the 28 unknown-verdict Java-SMACK files of the original 72 under minimal+bodyOrContract+fuel100; confirm 100% within-family rate (or correct it) |
| **I8. 6 Neq.SameV files inherit precision-restoring property of vtepk5bv3ld** | BACKLOG.md uses vtepk5bv3ld as forward-witness fixture | 1 file | The 7-cluster | Revert eval to pre-multi-Env on each of the other 6; confirm at least one stack-overflows or times out where post-multi-Env passes |

---

## 5. Decisions Deferred (with Rationale)

| not investigating | why deferred |
|---|---|
| 9 files in `Examples/smack-docker/boogie-files/broken/` | Pre-existing skip; nothing in current sweep depends on them. Aaron-side question, not Strata. |
| Multi-Env impact on non-EQ corpora (the SMACK 94-suite vs 0% impact) | Bimodal datapoint flagged in v1 Q6, never followed up. Defer until a third corpus is needed for a separate decision; current EQ work doesn't gate on it. |
| `sv_locks_*` PASS-? variance (6 files, 10×-replay histogram) | Pre-documented as "probe variance"; falls under SMACK-suite, not EQ. Worth its own backlog entry, not blocking EQ closure. |
| TIMEOUT shape generalization (18 large-bucket TIMEOUTs at minimal+120s) | Predicted ~60/30/10 split (slow-but-bounded / unbounded / SO). Edge-case finds only; lower VoI than the cheap probes below. ~1 hr if anyone wants to settle it. |
| Goal-shrink mechanism (4 small-file PASS−2 to −12 cases) | Confirmed benign; mechanism (isTrue short-circuit at exception-merge) understood. Document, don't probe. |
| Eq.SameV count drop 4→1 across batches (sampling vs reclassification) | Batch-2 elab failures may have hidden some Eq.SameV cases pre-stratification. Falls out of A4's re-sweep if anyone re-runs; not worth a standalone probe. |
| Recon-vs-reality 5-orders-of-magnitude gap on 2.86M obligation count | Documented as a model-vs-reality gap; closing it requires building a better cost model, which is not on the critical path for any EQ decision. |
| `bugFinding` mode probe on the 7 PARTIALs | Single ike2wen0cz0 trial under bugFinding produced same `❓ unknown`; v2 §8.5's #2 action would systematize but yields modest information vs A3's option-stripping probe. Roll into A3 if time permits. |

---

## 6. Recommended Next Investigations

Top 5, ranked by ROI. Total realistic budget for the top 3: ~3 hours.

### #1. SO-fix end-to-end validation (~30 min)

**Probe shape:** Run all 7 SO reproducers (per BACKLOG.md:54-58) under `--check-level minimal --call-policy bodyOrContract --inline-fuel 100` at 120s/proc. Tabulate verdicts.

**Expected outcome:**
- Best case: 5+/7 reach PASS / PARTIAL / FAIL:N → SO fix is a real fix; close that backlog item.
- Worst case: 0/7 reach a verdict → fix is a crash-suppressor only; SMT-side pathology remains; file as separate "body-eval scaling beyond SO" issue.

**Why first:** Highest VoI per minute. Settles whether the headline "SO RESOLVED" claim actually answers the user-facing question.

### #2. e-15 fix-and-verify (~1 hr)

**Probe shape:** Apply the one-line fix at `Strata/DDM/Util/Decimal.lean:50` (replace scientific-notation fallback with `(/ m 10^|e|)` form). Re-run 10 of the 333 affected files; histogram verdict-shifts.

**Expected outcome:** 90%+ of affected files convert from `unknown` → green (PASS) for free. Soundness wedge for a one-line patch. File upstream PR.

**Why second:** Sharpest, smallest-diff Strata fix in this entire batch. The diagnosis is concrete to a single line; only verification + filing remains.

### #3. Vacuous-PASS rate measurement (~1 hr)

**Probe shape:** v2 §8.5's #1 action — run the 22 deep-dived files at minimal+bodyOrContract+fuel100. Count contract-PASS files that flip to PARTIAL/different.

**Expected outcome:** Replaces v2's "60-100% projected vacuous" with a measured rate. Single number Aaron most needs to interpret his benchmark.

**Why third:** Answers the (d) goal of the original sweep ("methodology recommendation for Aaron") with measurement instead of projection.

### #4. Java-SMACK 28-file unknown-verdict sweep (~1 hr)

**Probe shape:** The 28 unknown-verdict Java-SMACK files of the original 72, under minimal+bodyOrContract+fuel100 at 120s/proc.

**Expected outcome:** Confirms or corrects v2 §1.4's "Java-SMACK has 0 PASSes." Post-SO-fix probe (3/3 → PASS-?) suggests this needs a refresh. Likely outcome: most reach PASS-? or PARTIAL.

**Why fourth:** Inflection point for whether Aaron's benchmark methodology has a 50% dead corpus. Not gating on multi-Env merge; gating on Aaron-facing recommendation.

### #5. Branch-spawn instrumentation (~half-day)

**Probe shape:** Add `dbg_trace` branch-spawn counter at `evalCFGStep` (similar instrumentation to probes 3/4). Run on the 7 SO files + 5 control PASS files (e.g., `dhag5onbafh`, `n33r2qrii5y`, `yg4xkpggkg2`).

**Expected outcome:** Either (a) confirms v2 §7's "fork-at-two-target-goto" predictor, validating the upstream fix; or (b) refutes it, in which case the predictor in any future bug filing needs revision.

**Why last:** Bigger budget; higher information per dollar than #1–4 only if you're filing a follow-up upstream bug that depends on the predictor being correct. Skip if SO fix's actual mechanism (foldl-tree depth, not branch-spawn) is enough for upstream.

---

## 7. What's Ready to File Upstream

| item | status | gating |
|---|---|---|
| #1331 — `old(<unmodified-global>)` rejected | FILED 2026-06-05 against origin/main2@4e4ceb9d1 with 5-line MWE and surgical fix at `StrataGenerator.cs:1798-1813` | Track review/merge |
| SO body-eval crash | DIAGNOSED + FIXED on htd/smack@494cf1147 (balancedNondetIte) | Wait for body-eval merge before filing upstream; once landed, file as "body-eval recursion-depth on SMACK output shape" with the predictor v2 §7 caveat |
| SMT2 `e-15` emission | DIAGNOSED to single line `Strata/DDM/Util/Decimal.lean:50` | One-line fix + 10-file verification (probe #2 above) → file standalone PR; not gated on body-eval |
| Pinned solver options suppress decidable counterexamples (A3) | DIAGNOSED on 2 files, structurally inferred for 5 | Run probe #6 (option-stripping on remaining 5) before filing; depends on whether the fix is "remove pinning" (UX win, possibly performance regression) or "add INT_MIN/INT_MAX axioms" (encoding fix). Choice requires a discussion, not just a measurement. |
| `multiple_Eq_SameV` harness mis-construction | FOR AARON | Aaron-side, not Strata; document and forward |
| 2.86M obligation count outlier (A5) | DIAGNOSED on 1 file | Run probe #5-equivalent (5 control files) to confirm outlier-vs-uniform before filing |
| `inlineCallBody` vs `evalCalleeCFG` mismatch (A6) | OBSERVED on 1 file | Code-read on `inlineCallBody` to find the gating condition; file as "two coupled counters diverge by 421 invocations" once the condition is identified |

**Net upstream queue if all probes run:** 4 PRs/issues to file (#1331 already filed; SO post-merge; e-15 fix; A3 once option-stripping confirms on the remaining 5).

---

## 8. Closing Note on the BACKLOG Entry

The current BACKLOG.md "next action" — *"Optional third sweep on 7 cost-regression files at varied timeouts"* — is now stale. v2 §3 already cleared 5/5 cost-regression files at 60s under minimal+bodyOrContract+fuel100. The "optional third sweep" was the right next step at v1; it isn't now.

**Concrete revision:** Replace BACKLOG.md:42 with the 3-probe bundle (items #1, #2, #3 above, ~3 hours). After those, either (a) all three close cleanly → mark EQ-portfolio item DONE and file SO upstream + e-15 PR + Aaron methodology note; or (b) one or more surface a structural issue → unblock the rest of the backlog with concrete evidence rather than projections. Items #5 (branch-spawn) and the deferred-list outliers (A5, A6) become independent backlog entries either way.

The headline question for the lead developer is no longer *"is multi-Env sound?"* — that's settled. It's *"do we have enough measured evidence to close, or are we still projecting?"* On the current state of evidence, the honest answer is "still projecting on three load-bearing claims." Three hours of probing converts all three to measured.
