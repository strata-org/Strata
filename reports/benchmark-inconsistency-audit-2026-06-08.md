# Benchmark Inconsistency Audit — Synthesis

Date: 2026-06-08
Branches considered: main (1d2b555fb), main2 (688e125134), htd/smack (8c588fb89)
Corpora: EQ-200 sweep (200 SMACK-translated CLEVER-style equivalence programs), 94-program SMACK pilot (Examples/smack-docker/), 12-file SMACK Docker pilot, hand-rolled CFG fixtures (12 files).

---

## 1. Headline

- **24 distinct findings observed across hunter rounds; 8 are present on `main` (or `main`+`main2`+`htd/smack` shared code), 14 are observable only on `htd/smack`, and 2 are out-of-tree (driver-wrapper / SMACK-corpus).**
- **8 findings retain S0_soundness after skeptic re-classification (down from 12 hunter-claimed); 5 of those 8 collapse to a single root cause: the default `--check-level minimal` silently emits PASS on vacuously-discharged obligations.**
- **The most severe issue affecting `main` is the silent vacuous-PASS surface: under default flags, the verifier reports `PASS` on 6 SV-COMP programs the oracle marks unsafe (sv_locks_14_2 + 5 siblings). Defect lives in `Strata/Languages/Core/Options.lean` (default `.minimal`) and `Strata/Languages/Core/Verifier.lean` (vacuity collapse) — verified by `git merge-base --is-ancestor` on `891e36287` and direct file inspection on all three branches.**
- **One genuinely fresh, high-confidence S1 bug on `main`: SMT-emitter heap-vs-element type confusion in `mkReturnSubst` at `Strata/Languages/Core/StatementEval.lean:86`, introducing commit `01b11a540` is ancestor of all three branches. Surfaces as Z3 parse errors on 8/200 EQ files; loud crash, not silent.**
- **The `277c468cb` deferred-dedup pipeline-hang fix referenced in `MEMORY.md` is stale — the SHA does not exist on any current branch; the equivalent fix is at `8f019818f` on `htd/smack` (verified by reading `Strata/Languages/Core/ProcedureEval.lean:119-129`). `main` cannot exhibit the bug at all because `main`'s `Languages/Core/StatementEval.lean` has zero `condGoto` references.**

---

## 2. Setup

**Scope.** Verdict-divergence audit across cross-backend, cross-config, cross-run, and cross-branch axes for the Strata verifier. Inputs:

- 200-program EQ portfolio (`/tmp/claude-503/eq200-*` TSVs and stdout/stderr dirs, 2026-06-06 sweep at 60s + mem-cap re-run at 20s).
- 94-program SMACK pilot (`Examples/smack-docker/README.md`, `BRANCH_FEATURES.md`, `CROSS_VALIDATION.md`).
- 64–65 program portfolio call-policy comparison (`wt-test/comparison-bugFinding-call-policies-v4.md`).
- 12 hand-rolled CFG fixtures (`/tmp/claude-503/cfg_edge_tests/`).
- Git history & file-level diffs across `main`, `main2`, `htd/smack`.

**Method.** Five parallel hunter passes (cross-backend, cross-config, cross-run, vacuous-PASS, ELAB-FAIL re-audit, SMT-emitter type-confusion, stack/hang/SIGTERM hunter, verdict-vs-truth) + branch-locate ancestry checks + four skeptic passes (soundness, branch-locality, completeness, severity).

**Out of scope.** Cross-solver (z3 vs cvc5), random-seed sensitivity, run-to-run determinism, IEEE FP semantics beyond e-15 — see §6 Coverage gaps.

---

## 3. Priority Table

Sorted by severity (S0 first, then S1, S2, S3, S4). `branch_locality` columns: M=main, M2=main2, S=htd/smack. Y=present, N=absent, ?=unknown.

| # | severity | name | evidence summary | M / M2 / S | n_files | recommended action |
|---|----------|------|------------------|-----------|---------|--------------------|
| 1 | S0 | check-level=minimal silently emits PASS on vacuous goals (6 oracle-unsafe SV-COMP programs) | `Examples/smack-docker/README.md:250-254`; `Options.lean` default `.minimal` on all three branches | Y / Y / Y | 6+ | Change `Options.lean` default to `.minimalVerbose` or have minimal mode refuse PASS when path-condition collapses to UNSAT |
| 2 | S0 | sv_locks_14_2 (and 5 siblings) PASS-? hides a real failure (subsumes #1) | `README.md:438`, `:556`; `Verifier.lean:785` "pass (path unreachable)" on main | Y / Y / Y | 6 | Same as #1 — single root cause |
| 3 | S0 | call-policy=contract silently passes 'unknown' on multi-branch callees (latent unsoundness on main/main2) | `StatementEval.lean:145-208` `inlineCallContract` single-env on all branches; `MULTIPATH_COMMAND_EVAL.md` table | Y / Y / Y | 1 demonstrated; mechanism general | Widen `Command.eval` to `List Env` (per `MULTIPATH_COMMAND_EVAL.md`); ensure contract path raises obligation on multi-branch callees |
| 4 | S0 | abs_func / pointer_arith: deductive=PASS, cbmc-native=FAIL on trivially-safe programs (S vs CBN comparator-axis silent disagreement) | `README.md:354,362`; `cbmc_native_flags.json:1-10` | N / N / Y | 2 | Triage cbmc-native shim: per-program audit `__VERIFIER_*` macro mapping, `--pointer-check` configuration |
| 5 | S0 | EQ-200 vacuous PASS subset: 100% (46/46) PASS files have only `assert true` and havoc-OR EQ accumulators | `/tmp/claude-503/eq200-cores/*.core.st` sweep; `Examples/smack-docker/boogie-files/EQ_*.bpl` line ~2647 | Y / Y / Y (corpus) | 46 | File upstream SMACK issue; add Strata UX disclaimer "PASS modulo havoc-init abstraction" on EQ harnesses |
| 6 | S0 | 14 PASS->PASS-? cosmetic flips (6 hidden display escapes); display-collapse fix is htd/smack-only | `README.md:482,490`; commit `a817909fc` not on main/main2 | N / N / Y | 14 | Backport `a817909fc` PASS-? parsing to upstream `run_pipeline` shim once it merges |
| 7 | S0 | EQ-equivalence postcondition vacuously satisfied by havoc-then-OR (SMACK-emitted .bpl) | `EQ_352f2nb4xnj_out.bpl:2647`; corpus-wide | Y / Y / Y (corpus) | 46 | File SMACK upstream issue: initialize EQ accumulators to `false`, not `havoc` |
| 8 | S0 | 100% asserts in EQ-200 PASS files are `assert true` (SMACK scaffolding) | corpus sweep; `EQ_352f2nb4xnj_out.bpl` SourceLoc attrs | Y / Y / Y (corpus) | 46 | File SMACK upstream issue: preserve original Java assertion semantics |
| 9 | S1 | SMT-emitter heap-vs-element type confusion in `mkReturnSubst` (8/200 EQ files; visible Z3 parse errors) | `eq200-verify-stderr/EQ_1ncwryiy1qx_out.err` lines 4-7; `StatementEval.lean:86` `mkReturnSubst`; introducing commit `01b11a540` ancestor of all three | Y / Y / Y | 8 | Fix `mkReturnSubst` to preserve type when `findD` returns `none`; recover type from procedure signature outputs rather than `state` lookup |
| 10 | S1 | skipEscape_harness: deductive SIGABRT (stack overflow in `translateExpr`) | `Translate.lean:818` unbounded `partial def`; reproducer in `reports/strata-verify-stack-overflow-deeply-nested-expr.md` | Y / Y / Y | 1 (corpus) + synthetic | Iterativize `translateExpr` analogously to `95abbe5671`'s `translateCoreDecls` rewrite; land on main |
| 11 | S1 | 16+ harness programs: deductive=PASS, cbmc-native=FAIL (definitional VC-set disagreement) | `README.md:392-431`; `CROSS_VALIDATION.md:122-136` | N / N / Y | 16 | Document VC-set semantics in CROSS_VALIDATION.md; flag harness-side spec gaps |
| 12 | S1 | Pipeline-hang fix `8f019818f` on htd/smack only; `main`'s Core lacks the `condGoto` code path entirely | `ProcedureEval.lean:119-129` on htd/smack; `git show main:Strata/Languages/Core/StatementEval.lean \| grep condGoto` = 0 | N (no path) / N (no path) / Y (fixed) | 8 large .bpl | Mark `MEMORY.md` note as obsolete; if `main` ever gains CFG-condGoto, port the deferred-clear fix |
| 13 | S1 | EQ-200 misclassification: `EQ_iwjr2x5ta4a_out` finishes with goals report but bucketed TIMEOUT | `/tmp/claude-503/eq200-verify-stdout/EQ_iwjr2x5ta4a_out.out` last line; `verify-one.sh` regex bug | N / N / Y | 1 firm + 1 soft | Fix `/tmp/claude-503/verify-one.sh` regex to `Finished with [0-9]+ goals passed, [0-9]+ failed`; inspect rc=143 cases for substantive completion |
| 14 | S1 | EQ-200 v6→mc transition: 1 TIMEOUT→PASS rescue + 2 ELAB↔TIMEOUT borderline flips | `eq-200-file-sweep-2026-06-06.md:152-167`; v6 wrapper SIGTERM bug | N / N / N (wrapper) | 5 | None — wrapper script discarded; mem-cap wrapper is canonical |
| 15 | S1 | Stub `_ensures_` goals discharge under shared-UF (twin-stub abstraction) | `EQ_352f2nb4xnj_out.out` 125 ✅ pass; intentional EQ-harness design | Y / Y / Y (corpus) | 46 | Surface "PASS modulo abstraction" disclaimer; not a code defect |
| 16 | S1 | SMACK-pilot PASS verdicts for `assert_.i32` body-less procedures (mitigated by `--smack` requires injection) | `Examples/smack-docker/programs/*.bpl`; `StrataGenerator.cs:1955-1963` | N / N / Y | 12 | None — `--smack` flag injects `requires` so PASS is sound; document the dependency |
| 17 | S2 | Strata-CBMC FAIL on 94/94 programs (lowering chain bodyless prelude stubs) | `README.md:244,502-510`; `CoreCFGToGOTOPipeline.lean:571,608` `[.no-body.<callee>]` | N / N / Y | 94 | Implement `__VERIFIER_*` and `assert_.iN` prelude stub bodies in `coreToGotoFilesDispatch` |
| 18 | S2 | ELAB_FAIL 56/56 hit lean4 #1331 shape: `old <X>` for non-inout params | `eq200-verify-stdout/EQ_*.out` "Cannot find this fvar"; `ProcedureType.lean:100-105` (main) `getInoutParams.toList` restriction | Y / Y / Y | 56 | One-line fix: extend `withOldBindings`-style check in `ProcedureType.lean` to all input params, or add explicit modifies-set support |
| 19 | S3 | 7 sv-loop / sv-rc programs PART vs cbmc-native PASS (no loop-invariant inference) | `README.md:445-449,458,459,461`; `:333-338` | Y / Y / Y | 7 | Long-term: add invariant-inference pass; short-term: document gap |
| 20 | S3 | 9 PASS-? programs (oracle-safe) — vacuous discharge happens to coincide with truth | `README.md:434-437,450,451,456`; `:255-260` | Y / Y / Y | 9 | Same lever as #1 — `--check-level full` surfaces them; underlying loop-havoc weakness shared |
| 21 | S3 | nondet_branch v3→v6 PART regression (multi-branch body-eval refusal) | `README.md:484,492`; `MULTIPATH_COMMAND_EVAL.md` | N / N / Y | 1 | Fork-and-continue (List Env) per `MULTIPATH_COMMAND_EVAL.md` |
| 22 | S3 | 39 PART→PASS portfolio gains v3→v6 (informational; bodyOrContract completeness lift) | `wt-test/comparison-bugFinding-call-policies-v4.md` | N / N / Y | 39 | None — improvement; track |
| 23 | S3 | Pre-solver elaboration TIMEOUT on 4 small Q1 files (frontend cost density) | `eq-200-anomaly-analysis-2026-06-06.md` A7; sec 4 Axis 3 | ? / ? / Y observed | 4 | 60–180s wall validator on Q1+Q3+Q4 low-density TIMEOUTs; profile `translateCoreDecls` |
| 24 | S4 | Pipeline 'Detail' column conflates cbmc translator error with deductive PASS verdict | `Examples/smack-docker/run_pipeline.py:600` | N / N / Y | all | Per-backend Detail columns or rename to "cbmc detail" |

---

## 4. Per-Finding Detail (top 6 by severity)

### #1 — `--check-level minimal` silently PASSes vacuous obligations on oracle-unsafe SV-COMP programs

**Symptom.** Default-flag `strata verify` reports `PASS` on 6 programs the SV-COMP oracle marks unsafe (sv_locks_14_2, sv_locks_15_2, sv_loops_mono3_1, sv_loops_mono4_1, sv_loops_mono5_1, sv_loops_mono6_1). Each contains a `while(1)` loop with an ERROR arm; Strata's `loopHasNoInvariants` havocs loop-modified state and assumes the loop guard false; the post-loop assertion runs against havoc'd state, path-condition collapses to UNSAT, and the goal is discharged as `pass (❗path unreachable)`. Under `--check-level minimal` (the default) the qualifier is dropped and the user sees `PASS`.

**Root cause.** Two layers, both shared across `main` / `main2` / `htd/smack`:
1. `Strata/Languages/Core/Options.lean` line ~218 default `checkLevel := .minimal`.
2. `Strata/Languages/Core/Verifier.lean:785` `pass (❗path unreachable)` label string only fires under `.full`; minimal-mode collapses the qualifier.

Verified `git merge-base --is-ancestor 891e36287 main` is true; the `.minimal` default is universal.

**Branch locality.** All three branches. The htd/smack-only `a817909fc` `run_pipeline` parser change *surfaces* `PASS-?` when `--check-level full` is also passed; it does not fix the underlying minimal-mode default. Consequently the latent display gap exists on `main` as well as `htd/smack`.

**Recommended next step.** Land a one-line change to `Options.lean` default (`.minimal` → `.minimalVerbose`) on `main` so PASS-? is surfaced out-of-the-box; alternatively, change the minimal-mode logic in `Verifier.lean` to refuse to emit literal `PASS` when the path-condition collapsed to UNSAT (delegate to `PASS-?`). This single change closes findings #1, #2, #6, and #20 simultaneously.

---

### #3 — call-policy=contract silently passes 'unknown' on multi-branch callees (latent on main)

**Symptom.** `Command.inlineCallContract` returns a single Env (havoc the lhs, assume the contract). When a callee body produces multiple symbolic branches, the contract-only path collapses them silently into a single env; the post-call obligation is discharged via the (possibly weak or missing) ensures clause, with no obligation generated for the multi-branch collapse. On the cited example `nondet_branch.c` the assertion happens to be true (so the silent collapse coincides with a sound verdict), but the *mechanism* is general silent under-checking and would mask real bugs on adversarial inputs.

**Root cause.** `Strata/Languages/Core/StatementEval.lean:145-208` `Command.inlineCallContract` returns `Command × Env` (single env); `Command.eval` `.call` arm calls `inlineCallContract` unconditionally under `--call-policy contract`. Code byte-identical between `main` and `htd/smack`. The bodyOrContract comparator that exposes the gap is htd/smack-only (`dd0c0d7cd`, `5648bdf62`, `5876eb06f`), but the under-checking is the universal default behaviour upstream.

**Branch locality.** Defect on all three branches. Comparator that surfaces it is htd/smack-only — so on `main`/`main2` the gap is silently latent.

**Recommended next step.** Adopt the design proposal in `Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md`: widen `Command.eval` to `List Env` so the type system enforces multi-branch callees raise an obligation. Land on `main` first; cherry-pick to `htd/smack` as a no-op refactor.

---

### #5 — EQ-200 vacuous-PASS rate is 100% (46/46)

**Symptom.** Every PASS verdict in the 200-program EQ portfolio's PASS bucket is semantically vacuous: 0 nontrivial assert goals (all `assert true`); 0 init-with-`:= false` EQ accumulators (all use `havoc`); 0 substantively-verified equivalence postconditions (all vacuous via havoc-then-OR pattern). Verifier dutifully reports `All N goals passed` (where N ranges 33–719 per file). User reads PASS as "equivalence verified" but the verifier saw no meaningful obligations.

**Root cause.** Defect at the SMACK harness/corpus layer, not in Strata: (a) SMACK's javabytecode-to-bpl frontend emits `assert {:sourceloc ...} true;` scaffolding at every basic block; (b) SMACK's EQ-harness emitter initializes accumulator booleans via `havoc` then OR-accumulates (`AA_TEMP50 := AA_TEMP50 || (AA_TEMP20 == _return)`), letting Z3 pick `true` for the havoc'd value; (c) twin-stub `otherfile_/reffile_` JDK abstraction shares output-variable names so `_ensures_` goals reduce to `X = X`. Verified via `Examples/smack-docker/boogie-files/EQ_352f2nb4xnj_out.bpl:2623,2647`.

**Branch locality.** Corpus-layer; would manifest identically on Boogie verifying the same `.bpl`. Strata is correctly verifying what it was given. The OBSERVATION rate (46 PASS files) is higher on `htd/smack` because the e-15 SMT fix and SMT-options-strip let more EQ files reach the solver — on `main`/`main2` the same files would more often ELAB_FAIL or hit upstream bugs first.

**Recommended next step.** File SMACK upstream issue (initialize accumulators to `false`, preserve Java assertion semantics). Add a Strata-side corpus lint that flags `havoc AA_TEMP*; AA_TEMPi := AA_TEMPi || ...` patterns and emits "PASS modulo havoc-init abstraction" disclaimer. Re-baseline EQ-200 PASS metric against nontrivial-assert pass rates only.

---

### #9 — SMT-emitter heap-vs-element type confusion (`mkReturnSubst`)

**Symptom.** 8/200 EQ files crash with Z3 parse errors: `"Subexpressions must have the same type"` on `(= shortArrHeap@30 otherfile__null)` (heap-typed value compared to `StrataRef`); `"argument type is not the type of the function's argument type"` on `($__f.NNN floatArrHeap@N 0.0)` (heap-typed arg where `Real` expected). All variants fire on `Output_of_<procname>_otherfile__<heapname>@N` SMACK-generated locals that share a long common prefix and differ only by heap-type suffix. 4 land in PARTIAL/rc=3 (OTHER bucket), 4 leak into TIMEOUT bucket because the SMT crash happens late enough that wall-clock fires first.

**Root cause.** `Strata/Languages/Core/StatementEval.lean:86-95` `mkReturnSubst` recovers `lhs_tys` via `(E.exprEnv.state.findD l (none, .fvar () l none)).fst`. For procedure-output locals not yet in `state`, this returns `none`; `Env.genFVar`/`genFVars` then emits an untyped `.fvar` with `ty? = none`. Downstream SMT encoding recovers the type via `Strata.Name.findUnique` (`Strata/Util/Name.lean:68-82`), which disambiguates by base name only. Two SMACK-modifies-set siblings sharing a long prefix but with different types (`StrataRef` vs `<heap-type>`) collide on `<base>@N` after disambiguation; the post-call output fvar gets matched against the wrong-typed sibling. Introducing commit `01b11a540` ("Fix variable versioning bug in procedure call evaluation", #337) is ancestor of all three branches.

**Branch locality.** `main`, `main2`, `htd/smack` — code byte-identical (htd/smack diff vs main is a `private` keyword). htd/smack-only multi-path body-eval changes (`5648bdf62`, `dd0c0d7cd`) extend `inlineCallBody` only; the SMACK pipeline runs the unchanged contract-policy `inlineCallContract` path, which carries the upstream `mkReturnSubst`.

**Recommended next step.** Recover type information at `mkReturnSubst` from the procedure signature's declared output parameters, rather than from `state` lookup with `none` fallback. Alternatively, disambiguate `findUnique` by full qualified name (including type suffix) for `Output_of_*` locals. Land on `main`; auto-propagates to `main2` and `htd/smack`.

---

### #10 — `skipEscape_harness` SIGABRT in `translateExpr`

**Symptom.** Deductive verifier exits with `Stack overflow detected. Aborting.` on `skipEscape_harness.bpl` (and on a hand-crafted 5000-deep nested-`if` reproducer constructed during triage). cbmc-native FAILs separately. v6's deferred-dedup fix on htd/smack lets the original harness PASS, but the underlying recursion hazard remains exploitable on adversarial inputs.

**Root cause.** `Strata/Languages/Core/DDMTransform/Translate.lean` declares `partial def translateExpr` with unbounded mutual recursion on every expression branch (line 818 on `main`, line 835 on `main2`, line 818 on `htd/smack`). The recursion shape is identical across branches — `git merge-base --is-ancestor d031c5a58 {main,main2,htd/smack}` is true for all three (the recursion was present in the initial commit, then renamed Boogie→Core in `5a7b44a75`/PR #330). The `htd/smack` iterativization commit `95abbe5671` only addressed `translateCoreDecls` and `Program.typeCheck`; `translateExpr` was not touched.

**Branch locality.** All three branches (latent crash hazard for hand-crafted deeply-nested inputs).

**Recommended next step.** Iterativize `translateExpr` analogously to `95abbe5671` — convert the recursive descent into an explicit work-list / continuation-passing form. Filed bug report `reports/strata-verify-stack-overflow-deeply-nested-expr.md`. Land on `main` and propagate.

---

### #18 — ELAB_FAIL 56/56: `old <X>` rejected for non-inout params

**Symptom.** All 56 ELAB_FAIL verdicts on the EQ-200 sweep emit the identical surface: `Type checking error. [<proc>:<proc>_ensures_0]: Cannot find this fvar in the context! old <var>`. Distribution: 27 on `otherfile__heap`, 9 on `otherfile__refArrHeap`, 20 on Java static field globals lifted into params.

**Root cause.** Mismatch between BoogieToStrata translator and Strata Core typechecker. `Tools/BoogieToStrata/Source/StrataGenerator.cs:382` `EmitOldExpr` emits `old <ident>` for any identifier appearing inside `old(...)` in source Boogie, including pure-input parameters and Java-static-field globals. But `Strata/Languages/Core/ProcedureType.lean:167-172` (htd/smack) / `:100-105` (main, main2) only adds `old <name>` bindings for `proc.header.getInoutParams.toList` — variables that are BOTH inputs AND outputs. SMACK-derived heaps appear as PURE-input parameters (passed by value, with shadow `Output_of_*` returns), so `old otherfile__heap` is unbound. Ironically, `StatementSemantics.lean:434` `withOldBindings` extends the runtime store for arbitrary modifies-clause names — runtime layer would handle these, but the typechecker rejects them first.

**Branch locality.** All three branches; identical text on `main` (`ProcedureType.lean:100-105`), `main2` (same), and `htd/smack` (`:167-172`). No fix in flight on any branch.

**Recommended next step.** One-line fix in `ProcedureType.lean`: extend `getInoutParams.toList` to all input parameters (or all params in a procedure-level explicit modifies set if reintroduced). The fix unblocks 56 EQ-200 files immediately. Land on `main`.

---

## 5. What the Data Refutes

- **Random-seed-driven verdict drift on bc4717354 (Z3 setOption strip).** No evidence collected; not exercised. Cannot refute or confirm — see §6.
- **Deferred-dedup hang reproducible on `main` (per stale `MEMORY.md`).** REFUTED for the CFG-condGoto path: `git show main:Strata/Languages/Core/StatementEval.lean | grep -c condGoto` returns 0; `main` does not have the code path the bug exists in. The hang is htd/smack-specific; the fix at `8f019818f` is landed on htd/smack. The cited SHA `277c468cb` is not on any branch tip.
- **Inline-fuel sweeps cause verdict changes.** REFUTED: empirical fuel=100 vs fuel=500 on 12 PASS-? programs produced zero verdict changes (`README.md`). Loop-havoc is the actual completeness blocker.
- **bugFinding backend provides independent counter-signal under bodyOrContract.** REFUTED: 0 verdict flips between contract and bodyOrContract for bugFinding (`comparison-bugFinding-call-policies-v4.md`); only fail-count inflation. Diversity goal defeated under bodyOrContract.
- **Stack-overflow class on small inputs in EQ-200.** REFUTED for this corpus: `grep` across 200 stdout/stderr files for "stack overflow", "panic", "SIGABRT" returns 0 hits. The translateExpr hazard (#10) is exercised only by skipEscape and synthetic reproducers.
- **Hunter-claim "v6 wrapper bug also affects engine."** REFUTED by Skeptic 4: same strata binary mtime `Jun 6 12:22` drove both runs; engine produces identical verdicts under mem-cap wrapper.
- **`277c468cb` deferred-dedup fix on htd/smack.** REFUTED by branch ancestry: SHA does not exist on any branch. Equivalent fix is `8f019818f` on htd/smack; `MEMORY.md` note is stale.

---

## 6. Coverage Gaps (per Skeptic Completeness)

The following modalities were NOT hunted in this audit and merit a follow-on round:

1. **Cross-solver disagreement (z3 vs cvc5).** Default solver is cvc5; z3 supported via `--solver z3`. The README notes cvc5 1.3.3 rejects `1e-15` as parse-unknown — a confirmed solver divergence. No hunter ran the EQ-200 corpus through both solvers and diffed verdicts.
2. **Random-seed sensitivity / verdict flakiness across reruns.** `bc4717354` stripped Z3 setOption pins; no validation that the same `.core.st` produces stable verdicts on multiple runs (z3 default has nondet resource-limit-driven branching).
3. **Cache vs clean-rebuild verdict diff.** Skeptic 4 confirmed same-binary-mtime; no rebuilt-from-scratch rerun. Possible Lean elaboration cache divergence not probed.
4. **FP semantics beyond decimal-e15** (Real/Float/Double, NaN/Inf, IEEE rounding). EQ corpus has many `Math_log`, `floatArrHeap`, `Real`-typed parameters; the 8 SMT-crash files all involve Real or floatArrHeap.
5. **Modifies-clause under-inference causing post-call vacuity** (vs the `old`-of-non-modifies surface of #18). Strata "has no modifies clause"; under-modifies could silently discharge post-call assertions.
6. **Symbolic loop-unroll / recursion depth limits.** `--inline-fuel` was tested but loop-unrolling, CFG depth, CallElim recursion were not.
7. **Lean typeclass synth instability across runs.** Q1 ELAB-TIMEOUT finding lists this as one possible cause; not probed.
8. **Run-to-run determinism on identical input.** No 10x rerun on a borderline-TIMEOUT file performed.

Recommended Hunter-9 round: GAP 1 (cross-solver), GAP 2 (random-seed), GAP 8 (run-to-run stability) — cheapest to validate and most likely to surface real soundness issues.

---

## 7. Recommended Next Steps (Ranked)

### Code fixes (land on main first; auto-propagate)

1. **Change `Options.lean` default `checkLevel := .minimal` → `.minimalVerbose`** (or have minimal mode refuse PASS on UNSAT path-condition). Closes #1, #2, #6, #20. One-line change on `main`.
2. **Fix `mkReturnSubst` type recovery in `StatementEval.lean:86`.** Recover type from procedure signature outputs rather than `state` lookup with `none` fallback. Closes #9 (8 EQ files unblock immediately).
3. **Extend `ProcedureType.lean` `old`-binding scope to all input params.** Closes #18 (56 EQ files unblock).
4. **Iterativize `translateExpr` in `Translate.lean`.** Closes #10 latent stack-overflow on hand-crafted inputs.
5. **Widen `Command.eval` to `List Env` per `MULTIPATH_COMMAND_EVAL.md`.** Closes #3 latent silent under-checking; subsumes #21.
6. **Implement `__VERIFIER_*` and `assert_.iN` prelude stub bodies in `coreToGotoFilesDispatch`.** Closes #17 (94/94 Strata-CBMC FAIL).

### Filing / triage (no code change)

7. **File SMACK upstream issue:** initialize EQ accumulators to `false`; preserve Java assertion semantics (don't lower to `assert true`). Closes #5, #7, #8 at the corpus layer.
8. **Mark `MEMORY.md` `277c468cb` note as obsolete.** Replace with `8f019818f` reference.
9. **Triage cbmc-native shim** for `abs_func`, `pointer_arith` (#4): per-program audit of `__VERIFIER_*` macro mapping, `--pointer-check` configuration. Document CBN as not-ground-truth without per-program triage.
10. **Per-backend Detail columns in `run_pipeline.py:600`** (#24). Cosmetic; rename to "cbmc detail" or split.
11. **Fix `/tmp/claude-503/verify-one.sh` regex** (#13): match `Finished with [0-9]+ goals passed, [0-9]+ failed`; inspect rc=143 for substantive completion before bucketing TIMEOUT.

### Coverage extension

12. **Hunter-9 round** on cross-solver (z3 vs cvc5), random-seed determinism, and 10x-rerun verdict stability (Coverage gaps 1, 2, 8).
13. **60–180s wall-clock validator** on Q1+Q3+Q4 low-density TIMEOUT cluster (#23) to disambiguate frontend cost vs solver cost.

---

## 8. Files Referenced

### Reports (committed)

- `/Users/htd/Documents/Strata-smack/reports/eq-200-anomaly-analysis-2026-06-06.md`
- `/Users/htd/Documents/Strata-smack/reports/eq-200-file-sweep-2026-06-06.md`
- `/Users/htd/Documents/Strata-smack/reports/eq-cfg-emit-order-affected-count-2026-06-08.md`
- `/Users/htd/Documents/Strata-smack/reports/strata-verify-stack-overflow-deeply-nested-expr.md`
- `/Users/htd/Documents/Strata-smack/reports/eq-push-trackb-evalprofile-2026-06-06.md`
- `/Users/htd/Documents/Strata-smack/reports/aaron-eq-portfolio-qualitative-analysis-v2-2026-06-05.md`

### Pipeline docs (committed)

- `/Users/htd/Documents/Strata-smack/Examples/smack-docker/README.md`
- `/Users/htd/Documents/Strata-smack/Examples/smack-docker/CROSS_VALIDATION.md`
- `/Users/htd/Documents/Strata-smack/Examples/smack-docker/BRANCH_FEATURES.md`
- `/Users/htd/Documents/Strata-smack/Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md`
- `/Users/htd/Documents/Strata-smack/wt-test/comparison-bugFinding-call-policies-v4.md`

### Source files (defect-bearing)

- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Options.lean` — default `checkLevel`
- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean` — vacuity collapse, PASS-? label
- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/StatementEval.lean` — `mkReturnSubst`, `inlineCallContract`
- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/ProcedureType.lean` — old-binding restriction
- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/ProcedureEval.lean` — CFG condGoto deferred-clear (htd/smack)
- `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/DDMTransform/Translate.lean` — `partial def translateExpr`
- `/Users/htd/Documents/Strata-smack/Strata/DL/SMT/Encoder.lean`
- `/Users/htd/Documents/Strata-smack/Strata/Util/Name.lean` — `findUnique`
- `/Users/htd/Documents/Strata-smack/Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean` — bodyless prelude stubs
- `/Users/htd/Documents/Strata-smack/Tools/BoogieToStrata/Source/StrataGenerator.cs` — `EmitOldExpr`, `--smack` requires injection

### Audit corpora (transient)

- `/tmp/claude-503/eq200-joined-mem-cap.tsv` — 200-row mem-cap verdict join
- `/tmp/claude-503/eq200-verify-stdout/` — per-file verifier stdout
- `/tmp/claude-503/eq200-verify-stderr/` — per-file verifier stderr
- `/tmp/claude-503/eq200-cores/` — 200 .core.st artifacts
- `/tmp/claude-503/cfg-order-A-results.tsv` — 3,293-row CFG order audit
- `/tmp/claude-503/verify-one.sh` — unversioned audit driver (#13)

### Branch tips

- `main` = `1d2b555fb128bfd17fbd8dc1dc05b42d531071a1`
- `main2` = `688e125134c043bcf59140a390d4cfe22672f4d4`
- `htd/smack` = `8c588fb89fb7ff446920793e0480c6d6573f8529`

### Inputs missing from disk

- `/tmp/claude/probe2_retest/results.tsv` — referenced by `eq-push-trackb-evalprofile-2026-06-06.md`; not present.
- `/Users/htd/Documents/Strata-smack/Examples/smack-docker/pipeline-results-comparison.md` — task-referenced filename; does not exist. The 12-program SMACK pilot result is not 12 — the canonical pilot is 94 programs documented in `README.md`.
