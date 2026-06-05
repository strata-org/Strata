# Backlog

Open feature work on `htd/smack` not tied to a specific bug report. Each entry: status + design pointer + next action.

## Evaluator

### Multi-`Env` return signature for `Command.eval`

**Status:** MERGED into `htd/smack` at commit `5648bdf62` (fast-forward).

**Design:** [`Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md`](../Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md).

**Summary.** Widened `Command.eval`, `Command.handleCall`, `Command.inlineCallContract`, and `Command.inlineCallBody` from `Command × Env` to `Command × List Env`. The single-env squeeze in `inlineCallBody` (commit `fa82fe42b`) is removed; per-path envs flow upward through `evalAuxGo`'s active-path machinery and each path's assertions are evaluated independently. `.BodyOrContract` falls back only on `OutOfFuel` / `.Misc`; multi-path success is no longer a failure mode.

**Verification.** smack-docker portfolio under `--call-policy bodyOrContract --split-procs` produces byte-identical verdicts vs `htd/smack` baseline on all 94 programs (68 PASS / 15 PASS-? / 11 PARTIAL / 0 FAIL). Regression-free, no new PASSes — the residual `nondet_branch` PARTIAL turns out to be a top-level CFG case (handled by `evalCFGStep` in `ProcedureEval.lean`, not `inlineCallBody`), not the callee fan-out the design assumed.

**Caveat — design's claim about `nondet_branch` is wrong.** `BRANCH_FEATURES.md` §4.3 and `MULTIPATH_COMMAND_EVAL.md` framed `nondet_branch` as the sole portfolio program where this change would lift PARTIAL → PASS. It isn't: that program's symbolic branch is in `main`'s top-level CFG, not in a callee body. The change is still sound and safe; its empirical uplift on the current portfolio is zero, but it removes the soundness gap and unblocks helper-procedure-with-symbolic-branching cases that don't appear here.

**Regression test.** `StrataTest/Languages/Core/Tests/InlineCallBodyTests.lean` Tests 7-9 (CFG-bodied callee with symbolic `condGoto`). TDD-confirmed: with the eval changes reverted to baseline, Tests 7 and 9 fail (`expected 2 envs, got 1` — the `.Misc` squeeze fired); with the eval changes restored, all three pass.

**Demonstration in the smack-docker matrix is deferred.** Adding a `caller → helper(symbolic if) → assert` program to `Examples/smack-docker/programs/` would require SMACK to regenerate `.bpl` from a new `.c`. SMACK runs only inside a Docker image (`Examples/smack-docker/Dockerfile`) which is sandbox-blocked in this environment. When Docker is available, follow the README's "Regenerating .bpl from .c" instructions and add a minimal program shaped like:
```c
int select_one_or_two(int b) { return b ? 1 : 2; }
int main(void) {
  int x = select_one_or_two(__VERIFIER_nondet_int());
  assert(x == 1 || x == 2);
  return 0;
}
```
Expected lift: PARTIAL on baseline `htd/smack`, PASS on `htd/multipath-cmd-eval`.

**Next action.** Done. Follow-up: add the smack-docker matrix demonstration when Docker is available (see template above).

## Benchmarks

### Test the pipeline on the equalizer benchmark

**Status:** IN PROGRESS — 72 of 3530 files swept (batch 1 + batch 2). Combined report at [`reports/aaron-eq-portfolio-batch2-2026-06-04.md`](aaron-eq-portfolio-batch2-2026-06-04.md).

**Findings.** Multi-env body-eval is decisively non-trivial on this corpus — 30/72 verdict-differ (42%, stable across batches). The multi-env work itself is sound; non-trivial findings reduce to two new actionable defects (filed below) plus an Aaron-side benchmark methodology question.

**Next action.** Optional third sweep (~36 more files) at varied timeouts {30, 120, 300}s on the 7 cost-regression files (`0exak45poxy`, `s541ce4abnj`, `oqt2xfezy0x`, `vtepk5bv3ld`, `mtonvj3sujq`, etc.) to bucket those as slow-but-bounded vs. unbounded. Otherwise considered enough coverage.

### Aaron-side: harness mis-construction in `multiple_Eq_SameV` benchmarks

**Status:** OPEN — needs Aaron to confirm or fix.

**Summary.** The `EQ_*_out.bpl` files for `benchmarks.CLEVER.multiple.Eq.SameV` (4 of 36 batch-1 files) call `_lib` directly with the original input rather than going through `_client`. The two `_lib` bodies compute `mod 5` and `mod 6` respectively — non-equivalent on arbitrary inputs. Equivalence holds only at the client level (the client preprocesses input as `l1 * 30`, after which both libs return 0). The harness as constructed asks the wrong question; contract mode passes vacuously by abstracting both libs to the same UF; body-eval correctly reports PARTIAL on the obligation as written.

**Why it matters.** Future EQ-portfolio sweeps will report PARTIAL on these `multiple_Eq_SameV` files. That's the truthful verdict on the harness as written; the underlying programs may or may not actually be equivalent. Without harness-generator clarification, we can't tell which `Eq` benchmarks are correctly-harnessed (genuinely lib-equivalent) vs. mis-harnessed (only client-equivalent).

**Next action.** Ask Aaron whether the EQ-harness generator should call `_client` instead of `_lib` for `Eq` benchmarks. If yes: regenerate. If no: document the methodology so future PARTIAL counts are interpretable.

### Strata-side: stack overflow under `bodyOrContract` — RESOLVED on htd/smack via `balancedNondetIte` (2026-06-05)

**Status: RESOLVED on htd/smack (2026-06-05)** via commit `494cf1147` introducing `balancedNondetIte` in `Strata/Languages/Core/Core.lean`. The fix replaces the `foldl`-built left-deep ITE tree (depth O(n) where n = deferred-obligations-count, reaching 2.86M on the worst reproducer) with a balanced bisection (depth O(log n) ≈ 22 for the same input). Per-obligation path-condition isolation is preserved by `ObligationExtraction.extractGo`, which still resets pc per arm.

**Validation (2026-06-05).** All 7 SO reproducers (`EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe`, `EQ_2aa5bx1uwko`, `EQ_wfgmxv3m3tx`, `EQ_sertrlracdg`, `EQ_0xaksnfuqqv`) cleared on the so-fix worktree: zero rc=134 (SIGABRT), zero "Stack overflow detected" stderr lines. All 7 now hit the post-SO long-running SMT regime within `gtimeout=90s` (rc=124) — acceptable behavior; a TIMEOUT is not a verifier crash. 94-program SMACK matrix is bit-identical on PASS and PARTIAL file sets vs the v6 baseline: 68 PASS / 11 PARTIAL / 0 FAIL (the 6 PASS-? → TIMEOUT shifts on `sv_locks_*` are pre-documented probe variance, not fix-induced).

**Filing.** Still not filed upstream — the bug requires `--call-policy bodyOrContract`, which exists only on the htd/smack feature line. When body-eval merges to main/main2, this fix should ship in the same merge. The fix is small (one helper + one call-site change in `Core.lean`) and self-contained.

**Lineage preserved below for context.**

**Summary.** 7 files crash with "Stack overflow detected. Aborting." (rc=-6/SIGABRT, exit 134) under `--call-policy bodyOrContract` on programs where `--call-policy contract` simply times out at 60s.

- Batch 1 (large): `EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe`
- Batch 2 (3 medium + 1 large): `EQ_2aa5bx1uwko`, `EQ_wfgmxv3m3tx`, `EQ_sertrlracdg`, `EQ_0xaksnfuqqv`

Initial framing as "large-file issue" was wrong — 4 of 7 are medium (3-4K lines). Trigger is body-eval recursion-depth on SMACK output shape, not file size. A timeout is a soft failure; a stack overflow is a verifier crash and should not happen — at minimum it should surface as `OutOfFuel` or fall back via `.BodyOrContract`'s contract path.

**Bisect confirmed pre-existing.** A pre-multi-Env strata binary (built from commit `dd0c0d7cd`, the parent of the multi-Env merge `5648bdf62`) was tested on the 3 batch-1 SO files. In all 3 cases, pre-multi-Env produced TIMEOUT with empty stdout (i.e., never reached a verdict — the squeeze didn't "protect" anything; it just delayed the same broken recursive-eval until 60s). Post-multi-Env reaches the SIGABRT deterministically inside 60s. The multi-Env work did not introduce this bug; it makes the latent crash visible faster.

**Skeptic-verified attribution (workflow `wf_941e83f2-00f`).** Three alternative hypotheses tested and refuted:
- *Not a translation crash:* the same `.core.st` artifact crashes under bodyOrContract (rc=134) and times out cleanly under contract (rc=124). A translation-stage crash would affect both policies equally.
- *Not an SMT subprocess crash:* `strings strata | grep "Stack overflow detected"` finds the literal string baked into the Lean-compiled binary. This is Lean's runtime stack-guard message, fired inside the strata process before any SMT subprocess is invoked.
- *Not an intentional cutoff:* the message is the generic Lean runtime form, not a domain-specific `panic!` like "inline-fuel exhausted" — and an intentional cutoff would also fire under contract.

**Diagnosis (probe-refined 2026-06-05).** Body-inlining drives the Lean verifier into deep non-tail recursion on SMACK call-graph shape; OS C stack exhausts; SIGABRT. `--inline-fuel 100` does not catch this case because the recursion isn't gated by inline-fuel — it's deep within Lean's own evaluation. Repro artifacts at `/private/tmp/claude-503/eq_2zvm.body.{stderr,stdout}` and `/private/tmp/claude-503/eq_0xak.body.stderr`.

*Probe 1 (fuel sweep + ulimit, 30s cap, 2026-06-04).* All four fuel levels (1, 10, 100, 1000) at default stack hit the 30s timeout WITHOUT producing output — masked the signal. fuel=100 + `ulimit -s 65520` (8x stack) STILL crashed with rc=134 in 14.85s. Sub-conclusion at the time: "unbounded — TCO alone won't fix it".

*Probe 2 (300s cap re-run, 2026-06-05).* Lifting the cap exposed fuel-independence and stack-unboundedness:

| Config                                | Outcome             | Time   |
|---------------------------------------|---------------------|--------|
| fuel=1,    default stack, 300s cap    | SIGABRT rc=134      | 226s   |
| fuel=100,  default stack, 300s cap    | SIGABRT rc=134      | 226s   |
| fuel=1000, default stack, 300s cap    | SIGABRT rc=134      | 205s   |
| fuel=1   + `ulimit -s 65520` (8x)     | SIGABRT rc=134      | 15s    |

The 8x-stack run crashes *faster* (more frames per second of wall time) — confirming the recursion is unbounded, not merely deep.

*Refined component localization (probe-3 measured 2026-06-05).* Counter trace via `dbg_trace` instrumentation, raised ulimit, bodyOrContract, fuel=100, on `EQ_2aa5bx1uwko`:

| Tag              | Count    |
|------------------|---------:|
| `[ITE-FORK]`     | **0**    |
| `[INLINE-CALL]`  | 1131     |
| `[CFG-CALL]`     | 1552     |
| `[CFG-CONDGOTO]` | 76       |

Total stderr lines 2761. rc=134. Final frame before SIGABRT: `[CFG-CALL] active=0 finished=40` followed by "Stack overflow detected. Aborting."

- `processIteBranches`: **0 entries — falsified.** The symbolic-ITE path was never entered on this input; the prior process-of-elimination conclusion was wrong.
- `inlineCallBody` / `evalCalleeCFG`-fork / `evalCFGStep` `condGoto`-arm: still consistent with not being the unbounded-recursion offender (fuel-independence evidence from probe 2 unchanged).
- **New candidate region: downstream of `evalCFGBlocks`.** The `active=0 finished=40` terminal frame indicates the CFG-walk *completed* before SIGABRT. The non-tail recursion is in a phase that consumes the 1131 accumulated inlined-body environments. Likely sites:
  - A `List.foldl`/`List.foldr` over the accumulated env list
  - The verifier's VC emission walking deferred obligations from each Env
  - `SMTEncoder.lean` processing the accumulated obligations

*Probe 3 (completed 2026-06-05).* `dbg_trace` counter instrumentation ran on `EQ_2aa5bx1uwko` with raised ulimit, fuel=100. Result: `[ITE-FORK]=0`, `[INLINE-CALL]=1131`, `[CFG-CALL]=1552`, `[CFG-CONDGOTO]=76`. The processIteBranches fork-explosion hypothesis is **falsified**. See counter table above. **The "1131 inlined bodies" estimate underestimated the real depth-driver by 5 orders of magnitude — see probe 4.**

*Probe 4 (completed 2026-06-05; report at [`reports/so-localization-probe4-2026-06-05.md`](so-localization-probe4-2026-06-05.md)).* Instrumented `Verifier.lean`, `ProgramEval.lean`, `Core.lean`'s `toCoreProofObligationProgram`, `ANFEncoder.lean`, `ObligationExtraction.lean`. Terminal stderr trace before SIGABRT:

```
[CFG-CALL] active=0 finished=40                        ← CFG walker drained
[FOLD-DEFERRED] ... blocks=2857392 deferred=2857392    ← fold accepted 2.86M-block input
[ENCODE-VC] anfEncodeBody entered: stmts=1 startIdx=0  ← entered ANF, never returned
Stack overflow detected. Aborting.
```

`[OBLIGATIONS]` never fired (count 0). The depth-driver is **2,857,392 blocks**, not 1131 — the prior probe-3 estimate based on `[INLINE-CALL]=1131` underestimated by 2,500× because each CFG completion deferred ~71k obligations on average. The `[FOLD-DEFERRED]` site at `Strata/Languages/Core/Core.lean:184-189` (`Core.toCoreProofObligationProgram`) `foldl`s the deferred-blocks list into a **left-nested `Stmt.ite .nondet` tree of depth 2.86M**:

```lean
-- /Users/htd/Documents/Strata-smack/Strata/Languages/Core/Core.lean:185-189
let body := match blocks with
  | [] => []
  | [b] => b
  | b :: rest => rest.foldl (fun acc block =>
      [Imperative.Stmt.ite .nondet acc block .empty]) b
```

The `foldl` itself is TCO and completes — but it produces a **single statement whose AST depth equals the number of deferred blocks**. The first downstream consumer that recurses structurally on `Stmt.ite` arms is `ANFEncoder.anfEncodeBody` at `Strata/Transform/ANFEncoder.lean:197+` (callee `Statements.collectExprs` at `Statement.lean:486-518`, walking then-branch then else-branch with `++`). At depth 2.86M, the C stack exhausts long before the recursion completes.

**SO offender pinned (probe 4).** Root cause: `Core.toCoreProofObligationProgram` body-builder at `Core.lean:185-189`. Trigger site (where the SO actually fires): `ANFEncoder.anfEncodeBody`. CFG walking, body-eval, and `processIteBranches` are all empirically clean — the SO is purely a post-evaluation lowering-shape pathology.

**Fix axis (revised post-probe-4, 2026-06-05).** The fix lives in `Core.lean:185-189`, NOT in ANF or `processIteBranches`. Two options:

- **Option A (recommended) — flatten.** Each deferred block is an independent obligation; the nondet wrapping is redundant scaffolding because `ObligationExtraction` already iterates per-obligation. Replace the foldl with `blocks.flatten` (a flat list of statements). Single-line change.
- **Option B — balance the tree.** If alternatives semantics is required for some downstream consumer, replace the left-nested foldl with a balanced bisection. Depth becomes `log₂(2.86M) ≈ 22` instead of 2.86M:
  ```lean
  let rec balanced : List (List Stmt) → List Stmt
    | [] => []
    | [b] => b
    | bs => let (l, r) := bs.splitAt (bs.length / 2)
            [Stmt.ite .nondet (balanced l) (balanced r) .empty]
  ```

Either fix removes the SO without touching ANF, ObligationExtraction, or any of the eval-side code probed in probes 1-3. Workaround for users today: `--call-policy contract` (clean timeout, no crash).

**Next action (when unblocked).** Pick Option A or B (Option A is preferred unless investigation reveals a downstream consumer that depends on the nondet-alternatives shape). Implement, run the 7 SO reproducers under bodyOrContract; expected outcome is they each complete (PASS or PARTIAL or TIMEOUT-on-SMT, but no SIGABRT). File the bug report upstream once body-eval merges to main/main2, with the probe-4 counter trace + Core.lean:185-189 source + minimal repro as primary evidence. The fix is small enough to ship together with the body-eval feature merge.

### Strata-side: SMT2 emission bug — scientific-notation literal `e-15` not declared as variable

**Status:** OPEN — surfaced by bisect on `EQ_0exak45poxy_out.bpl` (2026-06-04).

**Summary.** Under `--call-policy contract`, `EQ_0exak45poxy_out.bpl` (small, `tsafe.normAngle.Neq.SameV`) produces 261 obligation failures, every one of which is the same SMT solver parse error: `Symbol 'e-15' not declared as a variable`. Strata's SMT2 emission is treating the literal `1e-15` (scientific notation, double-precision constant) as a free symbol rather than a numeric literal. Independent of multi-Env (pre-multi-Env binary times out before reaching the issue, but the bug is in SMT2 emission, not eval).

**Why it matters.** Affects any benchmark whose source contains scientific-notation floating-point constants — likely many of the `tsafe.*` and `bess.*` benchmark families. Currently surfaces as 261 spurious obligation FAILs on this one file; could be hundreds across the wider portfolio.

**Next action.** Locate where Strata's SMT2 backend emits double-precision literals — likely `Strata/Backends/SMT/` or `Strata/Languages/Core/SMTEncoder.lean`. Fix to emit `1e-15` as a `(/ 1 1000000000000000)`-style rational or as the SMT-LIB `(_ Real …)` form. Check that pre-multi-Env exhibited the same bug (likely yes) before filing.

### Multi-Env precision-restoring improvement — `EQ_vtepk5bv3ld_out.bpl`

**Status:** documented as a fixture for any future multi-Env regression test.

**Summary.** Pre-multi-Env strata stack-overflowed on `--call-policy contract` and timed out on `--call-policy bodyOrContract` for this file (`REVE.triangularMod.Neq.SameV`, medium bucket). Post-multi-Env passes both cleanly: 280 goals on contract, 1516 goals on bodyOrContract. Multi-Env's per-path env propagation enables this file to verify where the squeeze previously failed harder.

**Use as a fixture.** If we ever need to verify that multi-Env hasn't been silently reverted, this file is a deterministic forward-witness: post-multi-Env produces `All 1516 goals passed`; reverting eval to pre-multi-Env makes contract policy stack-overflow.

### Strata-side: typecheck failure on `old(<unmodified-global>)` in free-ensures (3 reproducers) — **FILED**

**Status:** FILED upstream as [#1331](https://github.com/strata-org/Strata/issues/1331) on 2026-06-05. Verified to reproduce on `origin/main2@4e4ceb9d1` with a 5-line minimal Boogie input. Independent of call-policy.

**Diagnosis update.** The original "cross-prefix" framing was a red herring — the bug fires whenever `g ∉ modifies` for any global referenced under `old`, regardless of namespace prefix. Verified by the minimal repro using same-prefix globals. Boogie permits `old(g)` for any in-scope `g`; Strata's `mkOld` bindings are minted only for inout params (`Strata/Languages/Core/ProcedureType.lean:100-105`), so the read-only globals BoogieToStrata emits for non-modifies globals lack `old`-resolvable fvars.

**Fix path (proposed in the issue).** Translator-side: in `Tools/BoogieToStrata/Source/StrataGenerator.cs:1798-1813`, pre-pass walking `proc.Requires` and `proc.Ensures` collecting any global appearing under `OldExpr` and unioning those into `modifiesNames` before the inout/read-only partition. Sound widening; preserves Strata's clean inout-only model.

**EQ-portfolio reproducers** (all 3 trip the same root cause): `EQ_koudjso4dzv_out.bpl`, `EQ_wvadqhmgjvk_out.bpl`, `EQ_cjromzqjo0n_out.bpl`.

**Next action.** Track #1331 review/merge. Local issue-draft kept at `boogietostrata-old-rejects-unmodified-global.md` for reference.

### Body-eval cost regression on bodyOrContract (deferred)

**Status:** OPEN — needs characterization at varied timeouts before filing.

**Summary.** 7 batch-2 files where contract finishes in <60s with a definite verdict (PASS or FAIL:N) but bodyOrContract hits the 60s timeout: `0exak45poxy`, `s541ce4abnj` (small), `oqt2xfezy0x`, `vtepk5bv3ld`, `mtonvj3sujq` (medium), and 2 more. Distinct from the stack-overflow issue (those crash; these just hang).

**Next action.** Re-run on these 7 files with timeouts of 120s and 300s to determine whether they're slow-but-bounded (raise CI budget) or actually unbounded (file as a body-eval performance bug). Don't file until characterized.

## Investigations

### Qualitative analysis of the 15 PASS-? unreachable cases

**Status:** RESOLVED — see [`v6-pass-question-mark-classification.md`](v6-pass-question-mark-classification.md).

**Outcome.** All 15 PASS-? cases share one mechanism: CFG-eval explores the loop's exit branch using *concrete pre-loop* induction-variable values, producing path conditions `assume false` whenever the loop guard is initially true. This is an EVALUATOR-GAP class (not a translator artifact, not a genuine vacuity). Caught with local `dbg_trace` instrumentation in `Verifier.lean`.

**Implication for matrix interpretation.** Of the 15: 9 are **would-be-PASS** (genuinely safe, vacuous due to evaluator gap) and 6 are **would-be-FAIL** (genuinely unsafe under SV-COMP oracle, hidden behind vacuity). Matrix's PASS column over-counts by 9 in the safe direction and under-counts unsafe-detection by 6.

**Follow-up (separate item).** Implement CFG-eval loop-handling fix: replace loop-modified-set with fresh symbolic variables on entering the loop, so the exit branch's path conditions don't pin the guard to pre-loop concrete values. See classification report §"Recommended fixes, ranked" for three options.

### CFG-eval loop-handling: havoc loop-modified-set on exit-branch entry

**Status:** OPEN — design pointer in classification report; no code.

**Design.** [`v6-pass-question-mark-classification.md`](v6-pass-question-mark-classification.md) §"Recommended fixes, ranked": option (1) is the minimum fix; options (2) and (3) are progressive enhancements.

**Summary.** When CFG-eval reaches a `condGoto` that exits a loop (i.e. the false-branch leaves the loop's strongly-connected component), replace the loop-modified-set with fresh symbolic variables in `env_f` before evaluating downstream blocks. Today the modified set retains pre-loop concrete values, which makes the exit-branch path conditions trivially UNSAT whenever the loop guard is initially true.

**Why it matters.** Closes the "PASS-? hides safe verdicts" gap (9 would-be-PASS programs) and surfaces the "PASS-? hides FAIL" gap (6 would-be-FAIL SV-COMP programs) as actual PARTIAL/FAIL verdicts. The matrix's deductive column would flip from 68 PASS / 15 PASS-? / 11 PARTIAL to roughly 77 PASS / 0 PASS-? / 17 PARTIAL — assuming the would-be-PASS group reaches PASS and the would-be-FAIL group surfaces as PARTIAL with concrete failing VCs. (The just-landed multi-env work `5648bdf62` does not contribute to this projection — verified by full-matrix re-run on `htd/smack` HEAD: byte-identical 68/15/11 verdicts to the pre-multi-env baseline. `nondet_branch` is a top-level CFG case unaffected by the multi-env contract change.)

**Next action.** Identify the loop-modified-set per CFG cycle in `Strata/Languages/Core/ProcedureEval.lean`'s `evalCFGStep` (use the back-edge information already present in the CFG analyzer); on exit-branch construction, fold a `havoc` of the modified set into `env_f` before adding the path-condition assumption. Validate against the 15 PASS-? programs from the classification report.
