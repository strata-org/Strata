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

**Corpus measurement (workflow `w26mmijqh`, 2026-06-10; report `reports/verify-1331-fix-corpus-2026-06-10.md`).** The fix (`188255668`) was verified at corpus scale, not just on the 3 reproducers. Regenerated an 80-file stratified sample (the prior 200-sample was cleared from `/tmp`; 3,529 source `.bpl` survive), translated each through pre-fix vs post-fix BoogieToStrata, type-checked both:
- **old-fvar error cleared: 24/24 = 100%** (zero `Cannot find this fvar … old` across all 80 post-fix type-check outputs). **0 regressions** (matrix strictly monotone).
- Pre-fix old-fvar incidence **30% (24/80)** — corroborates the prior 56/200 ≈ 28%. Projects to ~1,059 corpus files (95% CI ~735–1,447) with the error eliminated.
- **But only 67% (16/24) reach the type-check finish line.** The other **33% (8/24)** clear #1331 then hit a *different*, pre-existing type-check error — all the same one: modifies-completeness ("This procedure modifies variables it is not allowed to!"). So the fix's reach is real but bounded: ~⅔ of the ELAB_FAIL bucket proceeds toward SMT; ~⅓ is immediately re-blocked.
- Scope: type-check/ELAB layer only (the correct layer — #1331's impact is precisely the ELAB_FAIL bucket), NOT end-to-end SMT verdicts.

**End-to-end SMT re-sweep — DONE (2026-06-10; report `reports/eq-resweep-end-to-end-2026-06-10.md`).** The "separate, heavier follow-up" was run: the 16 cleared (`oldfvar→ok`) files were pushed past type-check into SMT on the freshly-rebuilt binary, verified per-procedure (`--split-procs`, the pilot-equivalent measure) across all **1,253 procedures**:
- **0 / 1,253 #1331 old-fvar regressions** — the widened effective-modifies set holds all the way through VC-gen and SMT, not just at type-check.
- **927 real-proof PASS (74.0%); 1,166 non-failing (93.1%)** counting the 239 vacuous (PASS_0/PASS-?). Only **14 hard errors (1.1%)** + **73 timeouts (5.8%)**.
- **0 soundness holes** — all 14 errors fail loudly (rc=3, zero spurious `goals passed`).
- **Two NEW EQ-corpus defects surfaced** (both orthogonal to #1331, tracked in BRANCH_FEATURES §9): (1) strata errno-63 temp-file-name-too-long on 265–278-char mangled Java proc names; (2) a Java float-array-heap SMT type-mismatch crash. See the two new entries below.
- **Methodology catch:** a first whole-program pass gave a false "0 PASS / 15 TIMEOUT" — an artifact of running SMT over 36–172 procs at once; `--split-procs` is the fair measure (a "timed-out" proc verifies in ~1s split). Durable artifacts (the prior `/tmp` runs were wiped 3×): `Examples/smack-docker/eq-resweep/` (`run.sh` resumable driver, `proc-out/*.out`, `proc-results.tsv`, `analysis/failure-taxonomy.txt`).

**Next action.** Track #1331 review/merge. Local issue-draft kept at `boogietostrata-old-rejects-unmodified-global.md` for reference. **Two follow-ups surfaced by the measurements:** (a) the modifies-completeness blocker (next entry) gates 33% of the type-check-cleared files; (b) the two new EQ end-to-end defects (BRANCH_FEATURES §9.5 #30 and #31) gate clean SMT verdicts on long-named / float-heap Java procs.

### Strata/translator-side: modifies-clause completeness for callee-modified globals — NEW

**Status:** OPEN — surfaced 2026-06-10 by the #1331 corpus measurement; unmasked once #1331 stops short-circuiting type-check. Not yet diagnosed in depth or filed.

**Summary.** 33% (8/24) of files cleared by the #1331 fix then fail type-check with "This procedure modifies variables it is not allowed to!" — a global is modified (often transitively, through a callee) but absent from the procedure's `modifies` clause, so BoogieToStrata emits it read-only and the Strata modifies-check rejects the body. First seen on `EQ_wvadqhmgjvk_out` (`reffile__heap` modified via a callee, not in modifies). Same root *family* as #1331 (modifies-clause incompleteness from SMACK output) but for *modified* globals, not just `old`-read ones — so the #1331 `old`-widening doesn't cover it.

**Likely fix direction.** Extend the effective-modifies widening (the #1331 `EffectiveModifies` machinery in `StrataGenerator.cs`) to also union the *transitive modifies* of called procedures — i.e. if proc P calls Q and Q modifies g, then g ∈ effective-modifies(P). This is the standard modifies-closure computation. Needs care: it's a fixpoint over the call graph, and must stay consistent at both partition sites (`WriteProcedureHeader` + `VisitCallCmd`) exactly as the #1331 fix does.

**Next action.** Diagnose the 8 files (confirm all are callee-transitive-modifies, not direct-modify-omissions); decide whether SMACK should have emitted the modifies (upstream) or BoogieToStrata should compute the closure (translator-side, like #1331). Estimate: ~1 day if it's the call-graph-closure extension of the existing `EffectiveModifies` pass.

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

### CFG-eval memory profile on loop-with-invariant programs — IMPLEMENTED (#29 closed locally)

**Status:** IMPLEMENTED (2026-06-10, local — uncommitted). The CFG-native loop-elim pass recommended by this investigation is built: `Strata/Transform/CFGLoopElim.lean` + `cfgLoopElimPipelinePhase` wired into `transformPipelinePhases` after `loopElimPipelinePhase` (verification path only). **The #29 measurement that died on transient 503s three times (`w2bl3s9l1`/`wikpaagrw`/`w7gh4f4nk`) is now COMPLETE** — run locally (no agent, no 503 exposure): `verifyCFG loopGuardPrecondPgm` flips **non-terminating (240 s timeout, 12.5 GB RSS) → 9 s / 847 MB, all VCs ✅**, with VC2 (maintenance) present and passing. Wrong-invariant soundness gate passes (VC1 FAILs in both forms). Zero regressions (8 still-failing CFGForm leaves are loop-free pre-existing #26/#27/#28). Report: `reports/cfg-loopelim-implementation-2026-06-10.md`. **Residual:** measure VC3/VC4 not yet wired into the CFG recipe (3/313 procs); corpus-scale TIMEOUT-unblock sweep (plan Task 5) deferred. Tracked as BRANCH_FEATURES.md §9.5 #29.

**Original status (for reference):** OPEN — root cause confirmed (irreducible-CFG census workflow `wqlj6z95v`, 2026-06-09); recommended fix is a new CFG-level loop-elimination pass.

**Design pointer.** [`reports/irreducible-cfg-census-2026-06-09.md`](irreducible-cfg-census-2026-06-09.md). Background: `Strata/Languages/Core/ProcedureEval.lean:106-149` (evalCFGStep + evalCFGBlocks worklist), `Strata/Transform/LoopElim.lean:125-203` (the structured-form acyclic cut), `:249` (the `.cfg`-body passthrough that's the gap).

**Root cause (confirmed).** `evalCFGBlocks` (`ProcedureEval.lean:133-149`) is a **fuel-only worklist with no visited-set / fixpoint / back-edge awareness**, and `evalCFGStep` (`:106-130`) forks *both* successors on a symbolic `condGoto`. So it literally **unrolls** reducible loop back-edges (the decrease block's `.goto lentry` at `StructuredToUnstructured.lean:132`) until fuel runs out — heap grows one `Env` per pseudo-iteration. The structured path doesn't OOM because `LoopElim` runs its acyclic havoc-and-cut on `.loop` Stmts; the CFG path never does (`LoopElim.lean:249` passes `.cfg` bodies through unchanged). NOT an irreducibility problem — the census found **0 irreducible CFGs across all 3,767 procedures** in the three corpora; every loop is a clean single-header reducible natural loop.

**Recommended fix — net-new CFG-native loop-elim pre-pass `cfgLoopElimPipelinePhase` (priority HIGH).** A `Program → Program` `PipelinePhase` on `.cfg` bodies, slotted after `loopElimPipelinePhase` in `transformPipelinePhases` (`Verifier.lean:893`), gated to fire only when a `.cfg` body has a back-edge. Per procedure: compute dominators, identify the natural-loop region, and replace it with the **full** structured-recipe acyclic cut, removing the back-edge so `evalCFGBlocks` sees a DAG and terminates bounded. **Scope boundary: verification path ONLY — must NOT touch the CBMC/GOTO path** (`corePipelinePhases` is not called by the CBMC GOTO entry).

**Refined by the effect study (workflow `w7gh4f4nk`, 2026-06-09; report `reports/cfg-loopelim-effect-2026-06-09.md`). Three load-bearing corrections to the original sketch:**
1. **Framing A (net-new CFG pass) confirmed; Framing B ruled out.** The 310-of-313 loop-bearing procs are born as `.cfg` directly from the SMACK/DDM translator (`translateCFGProcedure`, `Translate.lean:1808/1826`) and **never pass through `stmtsToCFG`** — so reordering `loopElim` before lowering (B1) touches nothing that OOMs, and reconstructing a structured `.loop` from `.cfg` (B2) is a full de-lowering, harder than the direct CFG cut. Build A.
2. **SOUNDNESS DEFECT in the naive cut — must NOT ship as prototyped.** The simple cut (`havoc M; assume ¬G; goto kNext`) is sound for *termination* but **drops the invariant-maintenance VC** (`arbitrary_iter_maintain_invariant`, VC2). A wrong-invariant program would spuriously PASS. The pass MUST emit the full recipe: pre-body `havoc(M) + assume(G ∧ I)`, body, post-body `assert(I)` (= VC2), then exit `havoc(M) + assume(¬G ∧ I)`. Verified against Loops.lean gauss golden (`:220-260`).
3. **Default to `assume true` for contract-less loops.** Only 3 of 313 loop-bearing procs carry `specLoopInvariant`/`specDecreases` metadata; the other 310 are contract-less SMACK CFGs. The pass must default the invariant to `true` to fix them (sound: `havoc M; assume true` is the standard no-invariant loop abstraction).

**Acceptance gate.** Re-run the Measure phase on htd/smack under a guarded harness (`gtimeout 60` + `maxHeartbeats`, single-thread Z3) and gate acceptance on **verdict-set equality with the structured form** on Loops.lean countUp/gauss/nested — NOT merely `cfgHasBackEdge` toggling. The #29 OOM closure is structurally plausible (prototype produces a DAG) but was **never measured end-to-end** — the Measure phase died on a transient 503 all three attempts (`w2bl3s9l1`, `wikpaagrw`, `w7gh4f4nk`), so the reproducer `loopGuardPrecondPgm` was never actually run post-elimination.

**Superseded mitigations.** The earlier stop-gaps (maxHeartbeats / separate Lake target / partial-loop-bound / env-list collapse) are superseded by the structural fix; the test-harness split (Part1-4) remains a reasonable OOM-avoidance for the test surface in the interim.

**Next action.** Execute the compile-ready implementation plan at [`reports/plan-cfg-loopelim-pass-2026-06-10.md`](plan-cfg-loopelim-pass-2026-06-10.md) — 5 tasks (dominator/region analysis → full-recipe acyclic synthesis → pipeline wiring → build+measure → regression+soundness), with the VC2-preserving recipe and `assume-true` default baked in. Hands-on Lean code task, ~2-3 days; the build/measure steps need a machine clear of other heavy Strata builds (the #29 measurement has died on transient 503s three times and must actually complete). The `wpqfi3man` evalCFGBody workflow was **dropped** (2026-06-10) as redundant — the census + effect study settled root cause and fix; its only net-new value (the loopGuardPrecondPgm measurement) is folded into the plan's Task 4 acceptance gate.

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

### Block-coalescing applicability census — DONE (verdict: don't build standalone)

**Status:** DONE (2026-06-09, workflow `w0sdli249`). Full detail: [`reports/block-coalescing-applicability-2026-06-09.md`](block-coalescing-applicability-2026-06-09.md).

**Findings.** Coalesceable-block density is wildly corpus-dependent: **EQ 38.4%** (79,464/206,860 blocks; 100% of procs; mostly length-2 `anonN` jump-chains) vs **SMACK 0.33%** (170/52,248; only 19.8% of procs) — 118× sparser, because SMACK's alternating-diamond CFGs split "unconditional source" and "single-pred target" onto different edges (verified: 384 uncond + 384 single-pred blocks, 0 edges with both). `stmtsToCFG` output *is* coalesceable (straight-line runs, block trampolines, ite-join tails, loop-body tails; ~20–80% per proc) and **never erases loop-contract metadata** — the feared `condGoto true L L` trap doesn't occur.

**Verdict: do NOT build it standalone.** (1) SMT query count is **invariant** under coalescing (obligation count = assert/cover count, preserved by `B.cmds ++ C.cmds`) — not a perf optimization. (2) Its only verify-path benefit (fewer false alarms from the per-block pc reset) is explicitly scheduled to be subsumed by the dominator-based pc-propagation TODO at `ObligationExtraction.lean:106`. (3) It pays off only on EQ (equivalence-checking), not the SMACK C-pipeline. CBMC/GOTO path must NOT coalesce (wants the real CFG).

**If pursued for readability/proof-corpus size:** fold into the **same dominator/natural-loop machinery the CFG-level loop-elim pass needs** (the predecessor-count map is a strict subset of loop-elim's dominator dataflow), run as a post-loop-elim cleanup phase (loop-elim splices acyclic blocks that create fresh single-pred chains; coalescing collapses them). Both are verification-path-only `Program → Program` pre-passes. Bundled it's nearly free; standalone the ROI doesn't justify a second framework. Tracked as a sub-task of the CFG-level loop-elim pass (*Investigations → CFG-eval memory profile #29*).

### evalCFGBody OOM root-cause + TDD fix (workflow `wpqfi3man`) — DROPPED

**Status:** DROPPED (2026-06-10) as redundant. The irreducible-CFG census (`wqlj6z95v`) confirmed the #29 root cause and the CFG-loop-elim effect study (`w7gh4f4nk`) settled the fix design (Framing A, full VC2-preserving recipe, assume-true default). This workflow's diagnose/propose phases duplicate both; its only net-new value — the `loopGuardPrecondPgm` OOM measurement — is now folded into Task 4 of `reports/plan-cfg-loopelim-pass-2026-06-10.md`. (That measurement died on transient 503s three times across `w2bl3s9l1`/`wikpaagrw`/`w7gh4f4nk`; the plan's guarded harness must finally complete it.) The paused run `wf_c84e1cfd-ad1` is left in place but should not be resumed.

### Translator-side fix for `old(<unmodified-global>)` typecheck failure (#1331) — IMPLEMENTED

**Status:** IMPLEMENTED on htd/smack at `188255668` (2026-06-09, local — not yet pushed). The `OldGlobalCollector`/`EffectiveModifies` widening landed in `StrataGenerator.cs` with the `OldUnmodifiedGlobal` regression fixture (`.bpl` + `.expect`). Verified: minimal repro flips `Cannot find this fvar ... old h` → `✅ pass`; all 3 EQ reproducers clear the old-fvar ELAB error (0 occurrences post-fix); integration suite 91 pass / 7 pre-existing fail (no regressions). **Corpus + end-to-end verification DONE (2026-06-10):** (i) type-check layer — 80-file stratified sample, old-fvar cleared 24/24 = 100%, 0 regressions, 67% reach a clean type-check (`reports/verify-1331-fix-corpus-2026-06-10.md`); (ii) end-to-end SMT — the 16 cleared files, all 1,253 procedures verified `--split-procs`: 927 real-proof PASS (74.0%), 1,166 non-failing (93.1%), **0 #1331 regressions through SMT**, 0 soundness holes (`reports/eq-resweep-end-to-end-2026-06-10.md`). **Residual follow-ups:** (a) `EQ_wvadqhmgjvk_out`-class modifies-clause-completeness issue — distinct ticket, see next BACKLOG entry; (b) the EQ-200 ELAB-bucket quantification is **subsumed** by the corpus measurement above (the old-fvar bucket projects to ~1,059 corpus files, all cleared at the ELAB layer); (c) **two new EQ end-to-end defects** surfaced (errno-63 long-name temp file, float-heap SMT type mismatch) — BRANCH_FEATURES §9.5 #30/#31. The plan that follows is retained for reference.

**Original plan (for reference):** READY TO EXECUTE — plan below; no script (this is a direct code change, not a workflow). Upstream issue [#1331](https://github.com/strata-org/Strata/issues/1331) is filed; this is the translator-side fix path it proposes. Closes 56 ELAB_FAILs + ~17 latent-in-TIMEOUT on the mem-capped EQ-200 sweep (the largest single ELAB unblock available). See also the typechecker-side alternative under *Translator → extend `mkOld`* above; this translator-side path is the smaller, less invasive fix and is preferred first.

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
