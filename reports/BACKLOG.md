# Backlog

Open feature work on `htd/smack` not tied to a specific bug report. Each entry: status + design pointer + next action.

**Document convention.** This file tracks **open** work only. When an item
lands, its detail moves out of this file: **features and fixes** go to the
catalog / bug ledger in
[`Examples/smack-docker/BRANCH_FEATURES.md`](../Examples/smack-docker/BRANCH_FEATURES.md)
(§4 features, §9 bug ledger); **observational findings** (sweeps, probes,
triage write-ups) go to [`reports/INDEX.md`](INDEX.md). Resolved items are not
retained here, even as pointers — consult those two indexes for landed work.
(Resolved items previously staged here were migrated on 2026-06-09: Multi-`Env`
→ BRANCH_FEATURES §4.6; balancedNondetIte SO → §4.5 + §9.5 #23; e-15 → §9.4 #24;
EQ portfolio sweep + A6 counter-axis → INDEX "Aaron's EQ portfolio sweep".)

## Benchmarks

### Aaron-side: harness mis-construction in `multiple_Eq_SameV` benchmarks

**Status:** OPEN — needs Aaron to confirm or fix.

**Summary.** The `EQ_*_out.bpl` files for `benchmarks.CLEVER.multiple.Eq.SameV` (4 of 36 batch-1 files) call `_lib` directly with the original input rather than going through `_client`. The two `_lib` bodies compute `mod 5` and `mod 6` respectively — non-equivalent on arbitrary inputs. Equivalence holds only at the client level (the client preprocesses input as `l1 * 30`, after which both libs return 0). The harness as constructed asks the wrong question; contract mode passes vacuously by abstracting both libs to the same UF; body-eval correctly reports PARTIAL on the obligation as written.

**Why it matters.** Future EQ-portfolio sweeps will report PARTIAL on these `multiple_Eq_SameV` files. That's the truthful verdict on the harness as written; the underlying programs may or may not actually be equivalent. Without harness-generator clarification, we can't tell which `Eq` benchmarks are correctly-harnessed (genuinely lib-equivalent) vs. mis-harnessed (only client-equivalent).

**Next action.** Ask Aaron whether the EQ-harness generator should call `_client` instead of `_lib` for `Eq` benchmarks. If yes: regenerate. If no: document the methodology so future PARTIAL counts are interpretable.

### Java-SMACK verdict profile — open follow-ups

**Status:** OPEN follow-ups from a RESOLVED-OBSERVATIONAL sweep (n=28, 2026-06-05). Sweep finding (PASS 25% real-proof, TIMEOUT 50% size-monotone, elab-fail 21% all `old`-of-fvar, 0 SO regressions) is closed; detail in `reports/eq-autonomous-closeout-2026-06-05.md`.

**Open next actions.** (a) Triage whether the 6/28 `Cannot find this fvar in the context! old <var>` elab-fails (constructor/getter `_ensures_0` clauses naming heap vars; smallest repro `EQ_w5qckr4iugx_out.bpl`) are the same root cause as #1331 or a distinct ticket — if the #1331 fix closes them transitively, no new ticket. (b) Optionally file a smack-docker pipeline ticket on `fix_core_st.py` super-linear-regex slowdown (3/28, all ≥4 MB inputs; ~205s on a 4.3 MB input).

### Strata-side: pinned z3 model-parameter options suppress decidable counterexamples

**Status:** OPEN (latent) — RESOLVED-OBSERVATIONAL investigation (Tier 1 A3, 2026-06-05); a fix/knob is not yet implemented. Detail in `reports/eq-autonomous-closeout-2026-06-05.md`.

**Summary.** Strata's `verify` pins z3 model parameters; under those pins, 6/7 PARTIAL EQ files return `❓ unknown` on obligations that flip to `sat`-with-concrete-witness under default-options z3 4.16. The suppression is per-file path-uniform (3/3, 9/9, 6/6, 5/5 within a Neq.SameV procedure all flip together), so it's a verify-config artifact, not a per-path solver hiccup. (2 of the 6 — the tsafe `normAngle` pair — only flip cleanly after the e-15 fix; that confound is now resolved.)

**Next action.** Drop the model-parameter pins from the z3 invocation default, or expose a `--solver-options` knob so they can be unpinned without recompiling. Witness-extraction reality-check is independently confirmable post-e15-fix. Artifacts: `/tmp/claude-503/a3/`.

### Strata-side: typecheck failure on `old(<unmodified-global>)` in free-ensures (3 reproducers) — **FILED**

**Status:** FILED upstream as [#1331](https://github.com/strata-org/Strata/issues/1331) on 2026-06-05. Verified to reproduce on `origin/main2@4e4ceb9d1` with a 5-line minimal Boogie input. Independent of call-policy.

**Diagnosis update.** The original "cross-prefix" framing was a red herring — the bug fires whenever `g ∉ modifies` for any global referenced under `old`, regardless of namespace prefix. Verified by the minimal repro using same-prefix globals. Boogie permits `old(g)` for any in-scope `g`; Strata's `mkOld` bindings are minted only for inout params (`Strata/Languages/Core/ProcedureType.lean:100-105`), so the read-only globals BoogieToStrata emits for non-modifies globals lack `old`-resolvable fvars.

**Fix path (proposed in the issue).** Translator-side: in `Tools/BoogieToStrata/Source/StrataGenerator.cs:1798-1813`, pre-pass walking `proc.Requires` and `proc.Ensures` collecting any global appearing under `OldExpr` and unioning those into `modifiesNames` before the inout/read-only partition. Sound widening; preserves Strata's clean inout-only model.

**EQ-portfolio reproducers** (all 3 trip the same root cause): `EQ_koudjso4dzv_out.bpl`, `EQ_wvadqhmgjvk_out.bpl`, `EQ_cjromzqjo0n_out.bpl`.

**Next action.** Track #1331 review/merge. Local issue-draft kept at `boogietostrata-old-rejects-unmodified-global.md` for reference.

### Body-eval cost regression on bodyOrContract (partially resolved by e-15 fix; remainder deferred)

**Status:** PARTIALLY-RESOLVED (2026-06-05) — 4 of the 7 files in this set were attributable to the SMT2 e-15 emission bug, not to body-eval cost. After the side-branch fix (`6f5e74fa6`):
- `0exak45poxy`: TIMEOUT → PASS All 261 goals
- `s541ce4abnj`: TIMEOUT → was PARTIAL pre-fix, now expected to follow 0exak (same shape)
- `0fmj2meb0oj`, `0q0oga15aij`, `0z42qdmejd0`: TIMEOUT (with e-noise) → PASS
- `vtepk5bv3ld`: was PARTIAL on v1 batch, **PASS All 1516 goals** on Tier-1 A3 re-run; not actually cost-regressing
- `mtonvj3sujq`, `oqt2xfezy0x`: still PARTIAL/TIMEOUT (true body-eval cost)

**Summary.** Original framing of "7 batch-2 files where contract finishes <60s but bodyOrContract hits 60s timeout" conflated three independent causes: (a) e-15 SMT2 emission contamination [now fixed on side branch], (b) flaky PARTIAL classification on `vtepk5bv3ld` [no longer PARTIAL], and (c) genuine body-eval cost regression on a handful of medium files (`mtonvj3sujq`, `oqt2xfezy0x`). Only category (c) is a real body-eval performance issue.

**Next action.** Re-run the residual ~2-3 files (after merging the e-15 fix into htd/smack) at timeouts of 120s and 300s to determine whether they're slow-but-bounded (raise CI budget) or actually unbounded (file as a body-eval performance bug). Don't file until characterized.

## Investigations

(The resolved "Qualitative analysis of the 15 PASS-? unreachable cases"
investigation moved to [`reports/INDEX.md`](INDEX.md) on 2026-06-09 — see the
`v6-pass-question-mark-classification.md` row. Its open follow-up, the
CFG-eval loop-handling fix, remains below.)

### CFG-eval loop-handling: havoc loop-modified-set on exit-branch entry

**Status:** OPEN — design pointer in classification report; no code.

**Design.** [`v6-pass-question-mark-classification.md`](v6-pass-question-mark-classification.md) §"Recommended fixes, ranked": option (1) is the minimum fix; options (2) and (3) are progressive enhancements.

**Summary.** When CFG-eval reaches a `condGoto` that exits a loop (i.e. the false-branch leaves the loop's strongly-connected component), replace the loop-modified-set with fresh symbolic variables in `env_f` before evaluating downstream blocks. Today the modified set retains pre-loop concrete values, which makes the exit-branch path conditions trivially UNSAT whenever the loop guard is initially true.

**Why it matters.** Closes the "PASS-? hides safe verdicts" gap (9 would-be-PASS programs) and surfaces the "PASS-? hides FAIL" gap (6 would-be-FAIL SV-COMP programs) as actual PARTIAL/FAIL verdicts. The matrix's deductive column would flip from 68 PASS / 15 PASS-? / 11 PARTIAL to roughly 77 PASS / 0 PASS-? / 17 PARTIAL — assuming the would-be-PASS group reaches PASS and the would-be-FAIL group surfaces as PARTIAL with concrete failing VCs. (The just-landed multi-env work `5648bdf62` does not contribute to this projection — verified by full-matrix re-run on `htd/smack` HEAD: byte-identical 68/15/11 verdicts to the pre-multi-env baseline. `nondet_branch` is a top-level CFG case unaffected by the multi-env contract change.)

**Next action.** Identify the loop-modified-set per CFG cycle in `Strata/Languages/Core/ProcedureEval.lean`'s `evalCFGStep` (use the back-edge information already present in the CFG analyzer); on exit-branch construction, fold a `havoc` of the modified set into `env_f` before adding the path-condition assumption. Validate against the 15 PASS-? programs from the classification report.

**Relationship to CFG loop-elim (#29) — likely the same fix.** This havoc-on-exit-branch patch and the #29 OOM both stem from one root: `evalCFGBlocks` has no loop-aware abstraction, so it unrolls the back-edge using concrete pre-loop induction-variable values. #29 is the memory symptom (unrolling blows up); the 15 PASS-? cases are the soundness symptom (the concrete-valued exit branch collapses to `assume false`, discharging the assertion vacuously). A **CFG-level loop-elim pass** that cuts the back-edge AND havocs the loop-modified set *subsumes this patch*: replacing the modified set with fresh symbolic values at exit is exactly what loop-elim's havoc does. Crucially, the 15 PASS-? programs are mostly invariant-less `while(1)`/bare loops — `LoopElim` requires an invariant (`LoopElim.lean:41`), so a CFG loop-elim pass must handle the no-invariant case with a plain havoc-the-modified-set fallback (assume nothing). With that fallback: the 9 would-be-PASS programs reach real PASS (exit no longer vacuous), and the 6 would-be-FAIL programs fail honestly against havoc'd state — the projected 68/15/11 → ~77/0/17 matrix shift. So **implementing CFG loop-elim would very likely flip these PASS-? results**; this standalone patch is the narrower alternative that fixes only the soundness symptom, not the OOM. The CFG-level-loop-elim effect study (in *Ready to execute*) should measure the PASS-? programs explicitly, not just the invariant-bearing #29 reproducer.

### CFG-eval memory profile on loop-with-invariant programs — ROOT CAUSE FOUND: build a CFG-level loop-elim pass

**Status:** OPEN — root cause confirmed (irreducible-CFG census workflow `wqlj6z95v`, 2026-06-09); recommended fix is a new CFG-level loop-elimination pass. Tracked as BRANCH_FEATURES.md §9.5 #29.

**Design pointer.** [`reports/irreducible-cfg-census-2026-06-09.md`](irreducible-cfg-census-2026-06-09.md). Background: `Strata/Languages/Core/ProcedureEval.lean:106-149` (evalCFGStep + evalCFGBlocks worklist), `Strata/Transform/LoopElim.lean:125-203` (the structured-form acyclic cut), `:249` (the `.cfg`-body passthrough that's the gap).

**Root cause (confirmed).** `evalCFGBlocks` (`ProcedureEval.lean:133-149`) is a **fuel-only worklist with no visited-set / fixpoint / back-edge awareness**, and `evalCFGStep` (`:106-130`) forks *both* successors on a symbolic `condGoto`. So it literally **unrolls** reducible loop back-edges (the decrease block's `.goto lentry` at `StructuredToUnstructured.lean:132`) until fuel runs out — heap grows one `Env` per pseudo-iteration. The structured path doesn't OOM because `LoopElim` runs its acyclic havoc-and-cut on `.loop` Stmts; the CFG path never does (`LoopElim.lean:249` passes `.cfg` bodies through unchanged). NOT an irreducibility problem — the census found **0 irreducible CFGs across all 3,767 procedures** in the three corpora; every loop is a clean single-header reducible natural loop.

**Recommended fix — CFG-level loop-elim pre-pass (priority HIGH).** A `Program → Program` `PipelinePhase` on `.cfg` bodies, run before symbolicEval/evalCFGBody, mirroring `loopElimPipelinePhase`'s role for structured bodies. Per procedure: (1) compute dominators + identify natural-loop regions from dominator back-edges (the census analyzer already prototypes this; all-reducible so no irreducible fallback needed); (2) recover the loop contract from the header `condGoto`'s `specLoopInvariant`/`specDecreases` transfer metadata — **already present**, attached at `StructuredToUnstructured.lean:146-151`, no re-inference; (3) splice the loop region with the same acyclic havoc+assume-invariant sequence `LoopElim` emits (`LoopElim.lean:125-203`), removing the `.goto lentry` back-edge. Result: `evalCFGBlocks` sees a DAG, terminates bounded, #29 OOM eliminated *structurally* (not papered over with `maxHeartbeats`/memory bounds), and CFG verdicts converge with structured-form. **Scope boundary: verification path ONLY — must NOT touch the CBMC/GOTO path, which wants the real cyclic CFG for unwinding.** Gate the pass to fire only when a CFG carries loop-contract metadata.

**Superseded mitigations.** The earlier stop-gaps (maxHeartbeats / separate Lake target / partial-loop-bound / env-list collapse) are now superseded by the structural fix above; the test-harness split (Part1-4) remains a reasonable OOM-avoidance for the test surface in the interim.

**Next action.** Scope the CFG-level loop-elim pass as a `Strata/Transform/` addition (new file, e.g. `CFGLoopElim.lean`, modeled on `LoopElim.lean`) + a `PipelinePhase` wiring in `Verifier.lean`'s `corePipelinePhases`. Estimated 1-2 days. Workflow `wpqfi3man` (evalCFGBody OOM TDD) may produce a complementary direct-fix candidate; reconcile when it lands.

(The resolved "Irreducible control flow census" investigation — 0 irreducible
CFGs across all 3,767 procedures; confirmed the #29 root cause — moved to
[`reports/INDEX.md`](INDEX.md) on 2026-06-09. Its actionable output, the
CFG-level loop-elim pass, is tracked in the *CFG-eval memory profile #29* entry
above.)

### EQ-200 corpus: pre-solver elaboration TIMEOUT cluster (anomaly A7)

**Status:** OPEN — diagnostic phase; tracked in `reports/eq-200-anomaly-analysis-2026-06-06.md` A7.

**Summary.** 4 Q1-small TIMEOUTs (227-266 KB) emit zero stdout in the 20s mem-capped wall window; axiom/assert/quantifier density is 1.5-4× the PASS-peer median. Pre-solver elaboration hangs (front-end cost), not solver-side TIMEOUTs. Distinct mechanism from #1331-latent ELAB_FAILs (which fail fast). Sibling to BRANCH_FEATURES #17 (deeply-nested-expr `elabExpr` rewrite) — same elaboration cost class, different trigger shape.

**Validator pass.** Re-run the 4 Q1 small TIMEOUTs at 60s, 120s, and 180s wall budgets to confirm the front-end-cost hypothesis (if a verdict is reached at 120s but not 60s, the cost is bounded; if 180s also TIMEOUTs with no progress, the cost is unbounded and matches #17's class).

**Next action.** Run the 60-180s validator pass on the 4 reproducers identified in A7; classify each as bounded-but-slow vs unbounded; if unbounded, bundle into the #17 elabExpr rewrite scope.

**Sibling cleanup.** Anomaly A8 (3 OTHER files clustering at 11-13s elapsed, distinct from ELAB tail at 1-4s and TIMEOUT wall at 20-22s — suggested Boogie-side OOM/abort signature) is a low-priority tracking ticket only, not a defect.

## Translator

### Refuse-to-convert for `.typeDecl` / `.funcDecl` Stmts in `stmtsToCFG`

**Status:** OPEN — soundness gap, no code yet.

**Design pointer.** [`reports/cfgform-9-mismatch-analysis-2026-06-08.md`](cfgform-9-mismatch-analysis-2026-06-08.md) §F2; tracked as BRANCH_FEATURES.md §9.3 #26.

**Summary.** `Strata/Transform/StructuredToUnstructured.lean:72-77` matches `.funcDecl _ _ :: rest` and `.typeDecl _ _ :: rest` and recurses with the declaration silently thrown away (source comment: *"Not yet supported, so just continue with `rest`."*). Subsequent statements still reference the declared types/functions, but they are no longer in scope after the rewrite, so the type-checker rejects the post-rewrite program. This produces a program with strictly different verdict from the original — a soundness violation. Surfaced by 5 CFGForm blocks: `TypeDeclStmt` (`typeDeclStmt1`, `typeDeclStmt3`, `typeDeclStmt4`, `shadowTopLevelType`) and `FunctionPreconditions_Part3/funcDeclPgm`.

**Recommended fix (option 1 in classification report).** Add a precondition check in `stmtsToCFG` that fails with a clear error message *"inline `.typeDecl` / `.funcDecl` not supported in CFG conversion"* rather than silently dropping. Aligns with the structured-to-unstructured proof's `simpleShape` predicate which already excludes these cases. **Alternative (more work):** hoist statement-level type/func declarations to top-level scope before rewrite.

**Next action.** Land the refuse-to-convert variant first (small, immediately closes the soundness gap); the hoisting alternative can come later if there's user demand.

### Type-checker: extend `mkOld` bindings beyond inout params (closes #1331)

**Status:** OPEN — alternative to translator-side widen-modifies, more invasive but more semantically faithful.

**Design pointer.** [`reports/inferModifies-investigation-2026-06-09.md`](inferModifies-investigation-2026-06-09.md) (rules out `InferModifies` as a fix); upstream issue [#1331](https://github.com/strata-org/Strata/issues/1331).

**Summary.** `Strata/Languages/Core/ProcedureType.lean:100-105` currently mints `mkOld` bindings only for inout params. Boogie permits `old(g)` for any in-scope global; the read-only globals BoogieToStrata emits for non-modifies globals lack `old`-resolvable fvars, so the typechecker emits `Cannot find this fvar in the context! old <X>`. Two fix paths: (a) **translator-side** (BACKLOG #1331 entry) widens `modifiesNames` by walking `proc.Requires` / `proc.Ensures` for `OldExpr`-references; (b) **typechecker-side** extends `mkOld` to mint bindings for all input params (or all globals in scope), regardless of inout/modifies. Path (b) is more faithful to Boogie semantics (any in-scope global can take `old`); path (a) is the proposed minimal fix in #1331.

**Why list path (b) too.** If StrataGenerator changes are blocked on PR review or if Boogie's any-old-global semantics is judged the canonical model, path (b) is the cleaner home for the fix. Also relevant: 56 ELAB_FAILs + ~17 latent in TIMEOUT in the mem-capped EQ-200 sweep all share this root cause — the volume justifies a long-term fix, not just a translator hack.

**Next action.** Wait on #1331 review; if path (a) lands upstream, this entry closes. If path (a) is rejected, propose path (b) as a Strata-Core PR.

## Operational

### Operational: push 437d38683 (F1+F4 `flushCmds` fix) to origin/htd/smack

**Status:** DONE (2026-06-09) — pushed. `git merge-base --is-ancestor 437d38683 origin/htd/smack` now returns true; `origin/htd/smack` is at `8908eb668` (the F1+F4 fix plus the three docs commits, fast-forward `8c588fb89..8908eb668`). origin and local are in sync (0 ahead).

**Residual.** The fix is still `htd/smack`-only relative to `main`/`main2`; landing upstream remains gated on the underlying PRs (see §9 *Path to upstream* in BRANCH_FEATURES). Kept here only as the record of the push.

## Ready to execute

Pre-authored workflow scripts, reviewed and staged but not yet launched. Each
is self-contained; launch with `Workflow({scriptPath: "<path>"})`.

**⚠️ Memory caution (applies to every entry below).** These workflows build
Strata, run the SMT verifier (`#eval verify` / `strata verify`), and in some
cases cbmc — each a large-memory-footprint process (a single `strata` run has
been observed at 28.5 GB RSS on a 48 GB box; the CFGForm test surface OOM-killed
a Lean process at 13 sequential SMT calls). When running these, **bound
parallelism and per-process memory**: cap `lake` / `xargs -P` worker counts
(≤4 build workers, ≤8 xargs on this box), apply `set_option maxHeartbeats` per
`#eval`, single-thread Z3, run each isolated-worktree TDD agent's build
sequentially rather than fanning out many concurrent heavy builds, and prefer
splitting a large test target over running it monolithically. Do **not** launch
two of these workflows concurrently, and avoid running them alongside other
heavy builds — their combined peak RSS can thrash or swap-kill the machine. See
the persistent `smt-test-memory-pressure` memory note for the full knob list and
the EQ-200 incident that motivated it.

### Call-elim-on-CBM prototype

**Status:** READY TO EXECUTE — script written and reviewed, not started.

**Script:** `/Users/htd/.claude/jobs/d3648beb/tmp/wf-callelim-on-cbm.js`

**What it does.** Prototypes the call-elim-on-CBM fix for the Strata-CBMC
`[.no-body.<callee>]` blocker (BRANCH_FEATURES.md §9.1 #8): lower SMACK-intrinsic
calls (`__VERIFIER_assume` → `ASSUME(arg != 0)`, `assert_.iN` /
`__VERIFIER_assert` → `ASSERT(arg != 0)`) to GOTO ASSUME/ASSERT instructions at
the FUNCTION_CALL emission site (`CoreCFGToGOTOPipeline.lean:161-193`) instead of
emitting calls to bodyless stub declarations that CBMC rejects. Six phases:
isolated worktree → reproduce the `[.no-body]` failing test → design the lowering
(intrinsic-detection strategy + assume/assert polarity) → TDD-implement
(fail-first, minimal patch, no-regression on E2E_CoreToGOTO + a non-intrinsic
callee still emits FUNCTION_CALL) → measure CBM verdict delta on 5-8 small SMACK
programs with a CBN soundness cross-check → synthesize. Leaves the worktree in
place for patch review. Honest about the likely outcome (the `[.no-body]` error
clears but a *different* next blocker may surface — still progress).

**Why it's the right approach.** Call-elim is exactly what the deductive path
does (and why Ded gets 68 PASS while CBM gets 0); the CBM path preserves the
calls to bodyless intrinsics instead. See the conversation analysis: empty bodies
are inserted because the procedures are genuinely bodyless SMACK intrinsics, and
the CBM pipeline skips abstract procedures at `CoreCFGToGOTOPipeline.lean:533`.

### Block-coalescing applicability census

**Status:** READY TO EXECUTE — script written and reviewed, not started.

**Script:** `/Users/htd/.claude/jobs/d3648beb/tmp/wf-block-coalescing-applicability.js`

**What it does.** Censuses whether a basic-block coalescing pass (merge chains of
unconditional single-pred/single-succ branches into one block) has applicable
opportunities across the three corpora (SMACK pilot, equalizer, StrataTest). Six
phases: pin the coalesce criterion against the IR's actual unconditional-branch
form (the `condGoto true L L` equal-target pattern + inter-block `.goto` links) →
build a coalesceable-chain analyzer (reuses the CFG parser + dominator machinery
from the reducibility analyzer) → census EQ + SMACK → source-analyze whether
`stmtsToCFG` output is coalesceable (the load-bearing StrataTest question: which
structured constructs lower to coalesceable chains) → skeptic verification
(equal-target edge counting, hand-traced spot-checks, practical-value challenge)
→ synthesize. Answers all three of the user's questions with block-removable
counts + a value assessment (optimization vs cosmetic, per consumer).

**Shared machinery.** The analyzer reuses the dominator/CFG-analysis code from
the irreducible-CFG census (`reports/irreducible-cfg-census-2026-06-09.md`); the
synthesis explicitly considers whether a coalescing pass could share
infrastructure with the proposed CFG-level loop-elim pass (above).

### evalCFGBody OOM root-cause + TDD fix (PAUSED mid-run — resume)

**Status:** PAUSED — launched as workflow `wpqfi3man` (run ID `wf_c84e1cfd-ad1`), stopped via `TaskStop` on 2026-06-09 while still early (Reproduce phase, setting up the `htd/unstructured-procedure` worktree). Resume, don't relaunch — completed `agent()` calls return cached results.

**Script:** `/Users/htd/.claude/projects/-Users-htd-Documents-Strata-smack/d3648beb-ea46-4635-9a8d-6b7b138d0f3d/workflows/scripts/evalcfgbody-oom-investigation-wf_c84e1cfd-ad1.js`

**Resume with:**
```
Workflow({
  scriptPath: "/Users/htd/.claude/projects/-Users-htd-Documents-Strata-smack/d3648beb-ea46-4635-9a8d-6b7b138d0f3d/workflows/scripts/evalcfgbody-oom-investigation-wf_c84e1cfd-ad1.js",
  resumeFromRunId: "wf_c84e1cfd-ad1"
})
```
(Same session only — the resume journal lives under this session's workflow directory.)

**What it does.** Five phases: reproduce the OOM on both htd/smack and htd/unstructured-procedure → diagnose from three angles (profiling, code-read, structured-vs-CFG) → propose fix candidates → TDD-verify each in isolated worktrees → synthesize.

**Overlap caveat.** The diagnose + propose phases largely duplicate the already-completed irreducible-CFG census (`wqlj6z95v`), which confirmed the #29 root cause (fuel-only worklist unrolls reducible loops) and recommended the CFG-level loop-elim pass. The net-new value is the **TDD-Verify phase** — actually testing candidate fixes in worktrees, which the census did not do. Consider resuming only for that phase, or skip it and scope the CFG-level loop-elim pass directly (tracked under *Investigations → CFG-eval memory profile* above). Reconcile any fix candidate it produces with that recommendation.

### Translator-side fix for `old(<unmodified-global>)` typecheck failure (#1331)

**Status:** READY TO EXECUTE — plan below; no script (this is a direct code change, not a workflow). Upstream issue [#1331](https://github.com/strata-org/Strata/issues/1331) is filed; this is the translator-side fix path it proposes. Closes 56 ELAB_FAILs + ~17 latent-in-TIMEOUT on the mem-capped EQ-200 sweep (the largest single ELAB unblock available). See also the typechecker-side alternative under *Translator → extend `mkOld`* above; this translator-side path is the smaller, less invasive fix and is preferred first.

**Root cause (re-confirmed against current source).** `WriteProcedureHeader` (`Tools/BoogieToStrata/Source/StrataGenerator.cs:1890-1894`) partitions globals into `inout` (in `proc.Modifies`) vs read-only (everything else). Strata's `mkOld` mints `old`-resolvable fvars only for `inout` params (`Strata/Languages/Core/ProcedureType.lean:100-105`), so a global referenced via `old(g)` in a `requires`/`ensures` but **not** in `proc.Modifies` is emitted read-only and has no `old`-fvar → `Cannot find this fvar in the context! old <g>`. Confirmed (inferModifies-investigation-2026-06-09) that `InferModifies = true` does **not** help: ModSetCollector only adds globals the body *writes*, and these globals are only *read* (in a contract `old`), so the modifies set stays empty correctly.

**Fix: widen the effective-modifies set with `old`-referenced globals.** Before partitioning, walk the procedure's `Requires` and `Ensures` conditions collecting every global that appears under an `OldExpr`, and union those names into `modifiesNames`. Sound widening (a global declared `inout` but not actually written is a no-op havoc-and-restore at the Strata level); preserves Strata's clean inout-only `old` model.

**Critical subtlety — two partition sites must stay consistent.** Widening is NOT a local edit to `WriteProcedureHeader`. There are two sites that partition globals in the same inout-then-readonly order:
1. **Declaration** — `WriteProcedureHeader` (`StrataGenerator.cs:1890-1894`): proc P's own param list.
2. **Call site** — `VisitCallCmd` (`StrataGenerator.cs:1030-1047`): every caller of P emits args in the inout-then-readonly order matching P's params.

If P gains `g` as `inout` at the declaration but a caller still passes `g` read-only, the call-site arg order won't match P's param order — a translation bug worse than the original. So the fix must compute a **per-procedure effective-modifies set** (`proc.Modifies ∪ old-referenced-globals(proc)`) once, key it by procedure name, and consult the same map at *both* sites.

**Implementation plan.**
1. **Add an `OldGlobalCollector : ReadOnlyVisitor`** (mirror the existing `FieldTypeCollector` at `StrataGenerator.cs:17-28`): override `VisitOldExpr` to recurse into the `old(...)` body collecting `IdentifierExpr` names that are in `_globalVariables`; expose the collected `HashSet<string>`. (Note: nested `old` is illegal in Boogie, so a single-level walk suffices, but collect all `IdentifierExpr` under the `OldExpr` subtree to catch `old(g[i])`, `old(f(g))`, etc.)
2. **Add a per-procedure cache** `Dictionary<string, HashSet<string>> _effectiveModifies` on `StrataGenerator`. Compute lazily or in a pre-pass over `_program.Procedures`: for each proc, run `OldGlobalCollector` over all `Requires`/`Ensures` conditions, union with `proc.Modifies.Select(m => m.Name)`.
3. **Replace `modifiesNames` at both sites** with a lookup into `_effectiveModifies[proc.Name]`:
   - `WriteProcedureHeader:1892` — use `_effectiveModifies[proc.Name]` instead of `proc.Modifies` only.
   - `VisitCallCmd:1032` — use `_effectiveModifies[callee.Name]` instead of `callee.Modifies` only. (The callee's effective set, so the call site matches the callee's widened declaration.)
4. **Edge case — `--smack` synthetic specs.** `VisitProcedure` injects synthetic `requires`/`ensures` on `__VERIFIER_assume`/`assert_` (`StrataGenerator.cs:1948-1996`); those reference params, not `old(global)`, so they won't widen anything — but verify the collector runs after injection or is robust to it.

**TDD plan.**
- *Failing test first:* the 3 EQ-portfolio reproducers (`EQ_koudjso4dzv_out.bpl`, `EQ_wvadqhmgjvk_out.bpl`, `EQ_cjromzqjo0n_out.bpl`) and the 5-line minimal Boogie repro from #1331 — confirm `strata verify` emits `Cannot find this fvar in the context! old <g>` before the change.
- *After:* re-translate + verify; the `old`-fvar error is gone (verdict reaches PASS/PARTIAL/TIMEOUT, not ELAB_FAIL).
- *No-regression:* `dotnet test Tools/BoogieToStrata/IntegrationTests/` stays green; a proc with `old(g)` where `g` IS in modifies still emits `g` as a single `inout` (no double-listing); call sites of a widened proc still type-check.
- *Scale validation:* re-run the mem-capped EQ-200 sweep; expect the 56 ELAB_FAIL bucket to shrink substantially (toward 0 for the #1331 sub-class) and shift into PASS/PARTIAL/TIMEOUT.

**Branch locality.** The `--smack` BoogieToStrata path is htd/smack-only, but the underlying `mkOld`-inout-only restriction is on main+main2+htd/smack (`ProcedureType.lean`). This translator-side fix lands on htd/smack; the typechecker-side alternative (path b) would be the main-targeting fix if StrataGenerator changes are blocked on review.

**Estimated effort.** Half-day (one collector class + one cache + two call-site swaps + tests).

### CFG-level loop-elimination effect study

**Status:** READY TO EXECUTE — script written and reviewed, not started.

**Script:** `/Users/htd/.claude/jobs/d3648beb/tmp/wf-cfg-loopelim-effect.js`

**Confirmed precondition (checked 2026-06-09).** Loop elimination for CFG bodies is **not implemented**: `Strata/Transform/LoopElim.lean:240-251` runs the real acyclic havoc-and-assume-invariant rewrite only on `.structured` bodies; the `.cfg _` arm at `:249` is a no-op passthrough (`-- CFG bodies have no structured loops; pass through unchanged.`). `evalCFGBlocks` (`ProcedureEval.lean:106-149`) is a fuel-only worklist with no loop-elim, which is why it unrolls reducible loop back-edges until fuel runs out (the #29 OOM root cause). So this study is about the *effect of a would-be pass*, not measuring an existing one.

**What it does.** Six phases: baseline (re-confirm CFG loop-elim is unimplemented + the loop contract IS on the header `condGoto` transfer metadata + pull the census's 313 loop-bearing reducible procedures) → design (two framings: **A** a net-new CFG-native pass recovering the contract from transfer metadata and splicing `LoopElim`'s recipe; **B** reorder the pipeline so `loopElimPipelinePhase` runs *before* the structured→CFG lowering, possibly sidestepping a CFG-native pass entirely) → prototype the cheaper viable framing in an isolated worktree (phase-reorder ~5 LoC if B works, else a minimal `CFGLoopElim`, else hand-simulated acyclic `.core.st`) → measure the effect on a test set (does it close the #29 OOM on `loopGuardPrecondPgm`? do CFG-form verdicts converge with structured-form? RSS delta?) → skeptic verification (soundness of the eliminated form — right havoc set, preserved measure, after-verdict matches structured) → synthesize.

**Relationship to other entries.** Directly answers the open *Investigations → CFG-eval memory profile #29* question (whether the recommended CFG-level loop-elim pass actually closes the OOM, before committing 1-2 days to build it) and overlaps the paused `wpqfi3man` workflow's Propose/TDD-Verify phases — reconcile findings. Framing B (pipeline reorder) is a cheap hypothesis worth testing first; if it works, #29 closes for far less than the 1-2 day net-new-pass estimate. **Also subsumes the *CFG-eval loop-handling: havoc loop-modified-set on exit-branch* item** — loop-elim's havoc of the modified set is exactly that fix, so the study must include the 15 PASS-? programs (invariant-less `while(1)` loops needing the no-invariant havoc fallback) alongside the invariant-bearing #29 reproducer, and report whether elimination flips the projected 68/15/11 → ~77/0/17 matrix.

**Memory.** Runs the #29 OOM reproducer's verify — see the section-header memory caution. The script bounds every verify with `gtimeout 60` + `maxHeartbeats`, single-threads Z3, builds sequentially, and only fans out light analysis agents in parallel (never concurrent heavy SMT builds).
