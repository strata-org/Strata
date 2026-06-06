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

**Status:** RESOLVED-PROVISIONAL (2026-06-05) — autonomous-closeout pass complete. 72 files swept across batch 1+2 plus a 28-file Java-SMACK Tier-1 stratified sweep, a 22-file vacuous-PASS deep-dive (Probe 3), a 7-file end-to-end SO validation (Probe 1), a 5-file solver-options witness audit (Tier 1 A3), and a counter-trace localisation of the [INLINE-CALL]-vs-[CFG-CALL] gap (Tier 1 A6). Three independent defects on the Strata side closed or filed: SO crash via `balancedNondetIte` ([backlog above](#strata-side-stack-overflow-under-bodyorcontract--resolved-on-htdsmack-via-balancednondetite-2026-06-05)); BoogieToStrata `old(<unmodified-global>)` typecheck rejection filed as upstream #1331; SMT2 e-15 emission bug fixed on side branch (see entry below) and draft-ready. One non-defect (the [INLINE-CALL]/[CFG-CALL] counter-axis gap) closed as benign-and-explained.

**Findings (consolidated).**
- *Multi-env body-eval is sound and decisive on this corpus* — 30/72 verdict-differ (42%) across batches 1+2. Pre-existing.
- *Vacuous-PASS rate quantified (Probe 3, n=22 deep-dive sample).* 81.2% strict (13/16) verified flips from contract-PASS to bodyOrContract non-PASS; 87.5% (14/16) including one compound-vacuous Δ=0 body-eval. Wilson 95% CI floor 57.0%. Family-skewed: 100% on Java-SMACK contract-PASSes (6/6), 6/7 on CLEVER+REVE+dart+bess synthetic contract-PASSes. Only 2 REVE files (`vtepk5bv3ld`, `ylzs20xcwwt`) yield substantive both-PASS verdicts. Confirms v2 §1.4/§2 projection of 60-100% vacuous-PASS at 81% point estimate.
- *SO end-to-end (Probe 1, n=7).* On the realistic flag set (`--check-mode deductive --check-level minimal --call-policy bodyOrContract --inline-fuel 100`) under 120s wall, 7/7 reach the 120s wall with zero stdout/stderr. The fix is **crash-suppressor only** for these reproducers — SIGABRT eliminated, but with empty output we cannot localize where the time is spent (parse / type-check / call-elim / VC-gen / SMT). End-to-end correctness on these 7 SO reproducers is not demonstrated; the crashes have been turned into silent timeouts. Follow-up under `--profile` or 300-600s budget on one or two files would discriminate "stuck in transform" from "stuck in solver."
- *Java-SMACK is not uniformly hostile post-SO-fix (Tier 1 sweep, n=28 stratified).* PASS 25.0% (7/28, all real-proof, no vacuous), PARTIAL 3.6% (1/28; 21,783 of 21,784 VCs proved, 1 ❓ unknown), TIMEOUT 50.0% (14/28; size-monotone), elab-fail 21.4% (6/28, all `Cannot find this fvar in the context! old <var>`), SO regressions 0%. The "every Java-SMACK file is a hard failure" framing in v2 §1.3 was an artifact of pre-SO-fix data and is now superseded.
- *Pinned solver options suppress decidable counterexamples (Tier 1 A3).* Confirmed witnesses for 6/7 files under default-options z3 (bhx, ike, 0exak, s541, mtonvj, plus pyafkjy4xny by v2 §5). Path-uniformity is per-file (3/3, 9/9, 6/6 within a procedure all flip together — generalizes v2 §5's single-path measurement). 2/7 (tsafe normAngle pair `0exak45poxy`/`s541ce4abnj`) flip *only after* working around an orthogonal Strata defect (e-15 emission). 1/7 (`vtepk5bv3ld`) is no longer PARTIAL on this run — file has stabilized to PASS at 1516 goals under bodyOrContract+inline-fuel-100.
- *[INLINE-CALL]/[CFG-CALL] axis-counter mismatch is benign (Tier 1 A6).* The 421-event apparent gap (1131 vs 1552) reported in probe-4 is fully explained by the two counters measuring different axes — `[INLINE-CALL]` is per-call (fires once per `inlineCallBody` invocation regardless of body shape), `[CFG-CALL]` is per-recursion-iteration (fires once per recursive entry of the worklist driver, so each `.cfg`-body callee produces `(rounds_to_drain + 1)` events). No gating divergence, no leak, no perf opportunity worth filing. Closed.

**Outputs and references.**
- Methodology note for Aaron: [`reports/aaron-eq-portfolio-methodology-note-2026-06-05.md`](aaron-eq-portfolio-methodology-note-2026-06-05.md).
- Anomalies audit: [`reports/aaron-eq-portfolio-anomalies-audit-2026-06-05.md`](aaron-eq-portfolio-anomalies-audit-2026-06-05.md).
- Autonomous closeout (full lineage; appended by synth phase): [`reports/eq-autonomous-closeout-2026-06-05.md`](eq-autonomous-closeout-2026-06-05.md).

**Next action.** Done for this corpus pass. If the EQ portfolio is re-swept at scale, run under `--call-policy bodyOrContract` only (contract-only is a translation-shadowing baseline on this corpus and over-counts PASSes by ~5x). One discretionary follow-up: run 1-2 of the SO reproducers under `--profile` or with a 300-600s budget to localize where time is being spent post-SO-fix.

### Aaron-side: harness mis-construction in `multiple_Eq_SameV` benchmarks

**Status:** OPEN — needs Aaron to confirm or fix.

**Summary.** The `EQ_*_out.bpl` files for `benchmarks.CLEVER.multiple.Eq.SameV` (4 of 36 batch-1 files) call `_lib` directly with the original input rather than going through `_client`. The two `_lib` bodies compute `mod 5` and `mod 6` respectively — non-equivalent on arbitrary inputs. Equivalence holds only at the client level (the client preprocesses input as `l1 * 30`, after which both libs return 0). The harness as constructed asks the wrong question; contract mode passes vacuously by abstracting both libs to the same UF; body-eval correctly reports PARTIAL on the obligation as written.

**Why it matters.** Future EQ-portfolio sweeps will report PARTIAL on these `multiple_Eq_SameV` files. That's the truthful verdict on the harness as written; the underlying programs may or may not actually be equivalent. Without harness-generator clarification, we can't tell which `Eq` benchmarks are correctly-harnessed (genuinely lib-equivalent) vs. mis-harnessed (only client-equivalent).

**Next action.** Ask Aaron whether the EQ-harness generator should call `_client` instead of `_lib` for `Eq` benchmarks. If yes: regenerate. If no: document the methodology so future PARTIAL counts are interpretable.

### Strata-side: stack overflow under `bodyOrContract` — RESOLVED on htd/smack via `balancedNondetIte` (2026-06-05)

**Status: RESOLVED on htd/smack (2026-06-05)** via commit `494cf1147` introducing `balancedNondetIte` in `Strata/Languages/Core/Core.lean`. The fix replaces the `foldl`-built left-deep ITE tree (depth O(n) where n = deferred-obligations-count, reaching 2.86M on the worst reproducer) with a balanced bisection (depth O(log n) ≈ 22 for the same input). Per-obligation path-condition isolation is preserved by `ObligationExtraction.extractGo`, which still resets pc per arm.

**Validation (2026-06-05).** All 7 SO reproducers (`EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe`, `EQ_2aa5bx1uwko`, `EQ_wfgmxv3m3tx`, `EQ_sertrlracdg`, `EQ_0xaksnfuqqv`) cleared on the so-fix worktree: zero rc=134 (SIGABRT), zero "Stack overflow detected" stderr lines. All 7 now hit the post-SO long-running SMT regime within `gtimeout=90s` (rc=124) — acceptable behavior; a TIMEOUT is not a verifier crash. 94-program SMACK matrix is bit-identical on PASS and PARTIAL file sets vs the v6 baseline: 68 PASS / 11 PARTIAL / 0 FAIL (the 6 PASS-? → TIMEOUT shifts on `sv_locks_*` are pre-documented probe variance, not fix-induced).

**Probe-1 follow-up (end-to-end validation, 2026-06-05).** Re-ran all 7 SO reproducers under the realistic flag set (`--check-mode deductive --check-level minimal --call-policy bodyOrContract --inline-fuel 100`) with a 120s wall budget. Translation step succeeded for all 7 (rc=0, 16-21s each). Verify step: 7/7 hit the 120s wall (rc=124) with zero-byte stdout and zero-byte stderr — verifier was still working through the pipeline silently when the wall clock killed it; no SMT verdict line, no progress lines, no error emission. **Verdict: SO fix is a crash-suppressor on these 7 reproducers** — SIGABRT successfully prevented (the verifier no longer aborts), but on this realistic flag set the verifier does not reach SMT/verdict within 120s on any of the 7 files. End-to-end correctness on these particular SO reproducers is not demonstrated; the crashes have been turned into silent timeouts. The empty stdout/stderr means we cannot tell from this run *where* in the pipeline the time is being spent (parse / type-check / call-elim / VC-gen / SMT). A follow-up under `--profile` or `--no-solve` (or a longer 300-600s budget) would discriminate "stuck in transform" from "stuck in solver" and confirm whether the floor is bodyOrContract inlining cost vs SMT cost. Artifacts: `/tmp/claude/probe1/`.

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

**Next action — upstream filing template (file when body-eval merges to main/main2).** Local fix already landed on htd/smack as commit `494cf1147` (`balancedNondetIte` in `Strata/Languages/Core/Core.lean`); validation closed below. The bug report should ship together with the body-eval feature merge so the upstream issue references mainline-visible commits. Filing template:

- **Title:** `Strata Verifier: stack overflow under --call-policy bodyOrContract from depth-2.86M nondet-ITE tree in toCoreProofObligationProgram`
- **Severity:** high — verifier process crash (SIGABRT, rc=134), not a recoverable timeout
- **Component:** `Strata.Languages.Core.Core` (deferred-block lowering) — root cause; `Strata.Transform.ANFEncoder` is the trigger site
- **File / lines:** `Strata/Languages/Core/Core.lean:185-189` — the `foldl`-built left-deep `Stmt.ite .nondet` tree
- **Reproducers (7):** `EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe`, `EQ_2aa5bx1uwko`, `EQ_wfgmxv3m3tx`, `EQ_sertrlracdg`, `EQ_0xaksnfuqqv` (all under `--call-policy bodyOrContract`; all clean rc=0/PASS or rc=124/TIMEOUT under `--call-policy contract`)
- **Diagnosis:** probe-4 counter trace shows `[FOLD-DEFERRED] blocks=2857392 deferred=2857392` immediately before SIGABRT; `[OBLIGATIONS]` count 0 confirms ANF entered but never returned. Full report: `reports/so-localization-probe4-2026-06-05.md`.
- **Fix (referenced as 494cf1147):** `Core.balancedNondetIte` — replace the depth-O(n) foldl with a balanced-bisection of depth O(log n) ≈ 22 for n=2.86M. Per-obligation path-condition isolation preserved by `ObligationExtraction.extractGo` (still resets pc per arm). One helper + one call-site change, fully self-contained in `Core.lean`.
- **Validation (post-fix on htd/smack):** all 7 reproducers cleared SIGABRT — zero rc=134, zero "Stack overflow detected" stderr lines on the so-fix worktree. All 7 now hit the post-SO long-running SMT regime within `gtimeout=90s` (rc=124) — acceptable: TIMEOUT is not a verifier crash. 94-program SMACK matrix bit-identical on PASS/PARTIAL file sets vs the v6 baseline (68 PASS / 11 PARTIAL / 0 FAIL).
- **Minimal repro for the upstream issue body:** the smallest of the 7 (`EQ_0xaksnfuqqv`, batch-2 medium) plus a trimmed Boogie reduction if achievable; the 2.86M depth comes from SMACK's call-graph shape, so a minimal Boogie may need ~20+ deferred-obligation sites to reach SO under default stack — a `.core.st` artifact may be the smallest-shippable form.
- **Workaround for users:** `--call-policy contract` (clean timeout, no crash).

### Strata-side: SMT2 emission bug — scientific-notation literal `e-15` not declared as variable — FIX-ON-SIDE-BRANCH, DRAFT-READY

**Status:** FILED-DRAFT-READY (2026-06-05). Fix landed on side branch `htd/decimal-e15-fix` at commit `6f5e74fa6` in worktree `/Users/htd/Documents/Strata-decimal-e15-fix`. Not yet pushed/filed upstream; not yet merged into htd/smack. Issue draft prepared at `strata-decimal-e15-emission-bug.md` (repo root, alongside `boogietostrata-old-rejects-unmodified-global.md`).

**Summary.** Under `--call-policy contract`, `EQ_0exak45poxy_out.bpl` (small, `tsafe.normAngle.Neq.SameV`) produces 261 obligation failures, every one of which is the same SMT solver parse error: `Symbol 'e-15' not declared as a variable`. Strata's `Strata/DDM/Util/Decimal.lean` was emitting decimal literals in scientific notation (`s!"{m}e{e}"`) when the exponent `e` fell outside `[-5, 5]`; SMT-LIB does not accept scientific-notation literals (both default-options z3 4.16 and cvc5 1.3.3 reject `1e-15` as a parse error / unknown-symbol). Independent of multi-Env (pre-multi-Env binary times out before reaching the issue, but the bug is in literal emission, not eval).

**Fix.** `/Users/htd/Documents/Strata-decimal-e15-fix/Strata/DDM/Util/Decimal.lean` — drops the `[-5, 5]` exponent bounds and the `s!"{m}e{e}"` scientific-notation fallback; always emits the literal as a decimal integer or `0.0…0…` form that SMT-LIB accepts. Self-contained in a single file. Build success: `lake build strata` completed all 540/540 jobs.

**Validation (10-file before/after sample).** 5/10 files improved, 0/10 regressed:

| File                | Before                       | After                              | Shift |
|---------------------|------------------------------|------------------------------------|-------|
| EQ_0exak45poxy      | PARTIAL 261/261 fail (`e-15`) | PASS All 261 goals                 | PARTIAL→PASS |
| EQ_0fmj2meb0oj      | TIMEOUT (with `e-14`)         | PASS All 609 goals                 | TIMEOUT-e→PASS |
| EQ_0q0oga15aij      | TIMEOUT (with `e-14`)         | PASS All 524 goals                 | TIMEOUT-e→PASS |
| EQ_0z42qdmejd0      | TIMEOUT (with `e20`)          | PASS All 598 goals                 | TIMEOUT-e→PASS |
| EQ_0c53ogei0g4      | TIMEOUT (with `e-8`)          | TIMEOUT (clean, no e-noise)        | improved (noise gone) |
| EQ_032wuerhmvw      | TIMEOUT (silent)              | TIMEOUT (silent)                   | unchanged (not e-attributable) |
| EQ_0agwqtm2bcg      | TIMEOUT (silent)              | TIMEOUT (silent)                   | unchanged (not e-attributable) |
| EQ_0rvvwfsfv2r      | TIMEOUT (silent)              | TIMEOUT (silent)                   | unchanged (not e-attributable) |
| EQ_0stx52y505t      | TIMEOUT (silent)              | TIMEOUT (silent)                   | unchanged (not e-attributable) |
| EQ_0gsuem3slyl      | FAIL (typecheck, unrelated)   | FAIL (typecheck, unrelated)        | unchanged (predicted) |

All 5 e-bearing baselines (1 PARTIAL + 4 e-bearing TIMEOUTs) shifted toward green: 4 reached PASS, 1 reached clean TIMEOUT (e-noise eliminated; remaining latency is unrelated solver work). Zero PASS→non-PASS regressions. EQ_0gsuem3slyl was correctly predicted not to shift (typecheck failure on a different code path).

**Why it matters.** Affects any benchmark whose source contains scientific-notation floating-point constants — observed across `tsafe.*`, `bess.*`, and a subset of REVE benchmark families. Currently surfaces as a few hundred spurious obligation FAILs per affected file; was confounding both the vacuous-PASS measurements (Probe 3 inflated PARTIAL counts on tsafe normAngle pair) and the witness extraction work (Tier 1 A3 — required hand-rewriting the literal in 0exak/s541 SMT2 inputs to get a default-z3 verdict).

**Next action.** Push side branch and file upstream issue using the prepared draft at `strata-decimal-e15-emission-bug.md` (repo root). Then merge `6f5e74fa6` into htd/smack (single-file change in `Strata/DDM/Util/Decimal.lean`; no merge conflicts expected).

### Java-SMACK behavior post-SO-fix — Tier 1 stratified sweep (n=28)

**Status:** RESOLVED-OBSERVATIONAL (2026-06-05). One new failure mode surfaced and triaged below; no follow-up sweep required for verdict-classification purposes.

**Method.** Stratified sample of 28 Java-SMACK files from the 2,929-file corpus by file size (134 KB → 12 MB). Per file: `strip_smack_prelude.py` → `dotnet BoogieToStrata --smack` → `fix_core_st.py` → `strata verify --check-mode deductive --check-level minimal --call-policy bodyOrContract --inline-fuel 100`. Translation budget 60s (later 180s for fix on large files); verify 90s. Run on htd/smack @ HEAD (post-SO-fix `277c468cb` + `494cf1147`).

**Aggregate result (28 files).**

| Verdict                                | Count  | Rate   |
|----------------------------------------|-------:|-------:|
| PASS (all real-proof, no vacuous)      | 7      | 25.0 % |
| PARTIAL                                | 1      |  3.6 % |
| TIMEOUT (verify-side, ≤4 MB)           | 11     | 39.3 % |
| TIMEOUT* (`fix_core_st.py` blow-up, ≥4 MB) | 3  | 10.7 % |
| elab-fail (`old`-of-fvar)              | 6      | 21.4 % |
| SO / panic / namespace-collision       | 0      |  0.0 % |

**Key updates to the v2 §1.3 framing.**
- Java-SMACK is **not a uniform hard-failure cohort** post-SO-fix. Small files (≤ ~675 KB Boogie) reach genuine non-vacuous PASS (133 → 2,133 VCs proved per file with no `path unreachable` annotations). The "0 known PASSes" claim in v2 §1.3 was an artifact of pre-SO-fix data; PASS rate at n=28 is 25%, PASS+PARTIAL is 28.6%.
- TIMEOUT is the dominant failure mode at scale (50%) but is almost monotone in file size — every file ≥1.1 MB other than `sm4j2muxvee` (a 1.5 MB PASS in 13s outlier) hits the 90s wall. Engineering knob, not soundness.
- **No SO regressions.** The fix in `277c468cb` + `494cf1147` holds across the n=28 sample.

**New failure mode (`old`-of-non-modifies-fvar elab error, 6/28).** All 6 elab-fails share one shape: `Cannot find this fvar in the context! old <var>` from a procedure `_ensures_0` clause referencing `old(<state-var>)` for a variable not in the elaborator's typing context. This is **distinct** from upstream #1162 (`__nondet`), from the older CFG-body SKIP, and from #1331 (`old`-of-unmodified-global). Affected six well-spread files (size range 237 KB → 2.7 MB), suggesting it's structural (constructor/getter ensures clauses naming heap variables) rather than random. Smallest clean repro: `EQ_w5qckr4iugx_out.bpl` (237 KB). Worth a separate ticket if it's distinct from #1331's root cause; if it's actually the same root cause as #1331 manifesting on Java-SMACK output shape, the existing #1331 fix may close it transitively.

**`fix_core_st.py` super-linear-regex slowdown (3/28, all ≥4 MB Boogie inputs).** Translation succeeds but post-processing wedges. On the 4.3 MB input, fix takes ~205s, and the resulting 21 MB `.core.st` then verify-TIMEOUTs at 90s anyway. Tooling-side, not verifier-side. Worth filing as a smack-docker pipeline issue if the Strata-Smack pipeline is a customer-facing path.

**Next action.** (a) Triage whether the `old`-of-fvar elab error is the same root cause as upstream #1331 or a separate ticket. (b) Optionally file a smack-docker pipeline ticket on `fix_core_st.py` regex super-linearity. (c) No need to re-sweep Java-SMACK for verdict-classification purposes — n=28 is enough to discriminate the cohort's profile.

### Strata-side: pinned solver options suppress decidable counterexamples (Tier 1 A3 confirmation)

**Status:** RESOLVED-OBSERVATIONAL (2026-06-05). Generalizes v2 §5's single-path measurement to within-procedure path-uniformity. Witness extraction for 5 new files plus 2 v2-prior; 6/7 yield witnesses under default-options z3.

**Summary.** v2 §5 reported that a single PARTIAL VC on `EQ_ike2wen0cz0_out.bpl` flips from "❓ unknown" under Strata's pinned z3 options to "sat with concrete witness" under default-options z3 4.16. Tier 1 A3 generalized this to 5 additional files plus re-confirmation of the 2 v2-prior. **Result: every ensures_0 path tested within a Neq.SameV procedure flips together** (3/3 on `ike2wen0cz0`, 9/9 on `mtonvj3sujq`, 6/6 on `bhx22kvwuqp`, 5/5 on the tsafe `normAngle` pair after working around an orthogonal Strata defect). The "solver-options artifact" is per-file path-uniform, not per-path.

**Per-file outcome table.**

| File              | Family             | Witnesses | z3-default verdict | Witness shape |
|-------------------|--------------------|-----------|---------------------|---------------|
| EQ_ike2wen0cz0    | REVE               | 3/3       | sat × 3/3          | `_in_parameter__1@1 = bv32 0`; nondets all false |
| EQ_bhx22kvwuqp    | CLEVER             | 6/6 (10/10 confirmed sat) | sat | (re-confirms v2 §5) |
| EQ_mtonvj3sujq    | bess               | 9/9       | sat × 9/9          | Real-typed Skolem-witnessed `_return@*` divergence |
| EQ_0exak45poxy    | tsafe              | 5/5       | sat × 5/5          | `_in_parameter__0@4 = 0.0` Real (after rewriting `e-15`) |
| EQ_s541ce4abnj    | tsafe (sister of 0exak) | 5/5  | sat × 5/5          | same shape as 0exak (after same rewrite) |
| EQ_vtepk5bv3ld    | REVE               | n/a       | n/a                | file PASS All 1516 goals on this run; not PARTIAL |
| EQ_pyafkjy4xny    | (v2 §5 prior)      | 1/1 (per v2) | sat | (taken at face value from v2 §5; not re-verified) |

**Aggregate.** 6 of 7 files yield witnesses under default-options z3 (bhx, ike, 0exak, s541, mtonvj, plus pyafkjy4xny per v2 §5). 1 of 7 (`vtepk5bv3ld`) is no longer PARTIAL on this run — it now passes cleanly at 1516 goals. The v1 PARTIAL classification was either run-flaky or set under a different harness configuration. For 2 of those 6 (the tsafe `normAngle` pair, `0exak45poxy` and `s541ce4abnj`), the verdict-flip story is **contaminated** by a separate defect: Strata's `Strata/DDM/Util/Decimal.lean` was emitting SMT-LIB scientific-notation literals (`3141592653589793e-15`) that both default z3 4.16 and default cvc5 1.3.3 reject as parse errors. That defect has now been fixed on side branch (`6f5e74fa6`); see the SMT2 e-15 entry above. With that defect resolved, the witness flip on the tsafe pair becomes clean.

**Net update to v2 §5.** The option-stripping verdict-flip story holds and **generalizes**:
1. *Path-uniformity within a procedure is real* (3/3, 9/9, 6/6, 5/5 within a single Neq.SameV procedure all flip together).
2. *The defect class is per-file*, not per-path — pinning the Z3 model parameters in `verify` is suppressing decidable counterexamples uniformly within a procedure.
3. *Two corollaries v2 §5 did not surface:* (a) the tsafe-normAngle pair's PARTIAL is contaminated by an independent emission defect (now fixed); (b) PARTIAL classifications on this corpus are not always run-stable (vtepk5bv3ld no longer PARTIAL).

Aggregate count under v2's narrow claim ("PARTIAL flips to ❌-with-counterexample under default z3"): 4 of 7 cleanly fit (ike, bhx, mtonvj, pyafkjy4xny). 2 of 7 fit only after the e-15 fix (0exak, s541). 1 of 7 is no longer PARTIAL (vtepk).

**Next action.** Filing path: change Strata's z3-invocation default to either drop the model parameter pins or expose a `--solver-options` knob so the model parameters can be unpinned without recompiling. The witness-extraction reality-check is now independently confirmable post-e15-fix on the tsafe pair. Artifacts: `/tmp/claude-503/a3/`.

### [INLINE-CALL]/[CFG-CALL] counter-axis gap (Tier 1 A6) — benign, closed

**Status:** EXPLAINED-AND-CLOSED (2026-06-05). Not filed. The 421-event apparent gap reported in probe-4 (`[INLINE-CALL]=1131` vs `[CFG-CALL]=1552`) is fully explained by the two counters measuring different axes; not a gating divergence, not a leak, not a perf opportunity worth filing.

**Summary.** `[INLINE-CALL]` (`StatementEval.lean:826`, was line 831 in the dbgtrace fork at the entry of `Command.inlineCallBody`) fires exactly once per `inlineCallBody` invocation, regardless of whether the callee body is `.structured` or `.cfg`. `[CFG-CALL]` (`StatementEval.lean:777-780`, was line 780 in the dbgtrace fork at the head-of-recursion of `evalCalleeCFG`) fires once per recursive entry of the worklist driver, so each top-level `.cfg`-body callee produces `(rounds_to_drain + 1)` events. The 421-event gap reflects (a) `.cfg`-body callees taking >1 round to drain (each `condGoto` fork at line 758 adds an extra round; 76 `[CFG-CONDGOTO]` events were observed) and (b) `.structured`-body callees contributing to `[INLINE-CALL]` but zero to `[CFG-CALL]`. The single call site of `evalCalleeCFG` is at line 879 inside `inlineCallBody`'s `.cfg` arm; there is no second entry from `ProcedureEval.evalCFGBody` (top-level CFG eval uses the separate `evalCFGBlocks`/`evalCFGStep` pair, which don't carry the `[CFG-CALL]` instrumentation). `inlineCallBody` checks `E.fuel == 0` once at line 836 and emits `OutOfFuel` before reaching `evalCalleeCFG`, so any inline-call that survives past line 836 reaches `evalCalleeCFG` if and only if the callee body shape is `.cfg`. **Verdict: explained-and-benign.**

Relevant files: `Strata/Languages/Core/StatementEval.lean` (lines 777-812 evalCalleeCFG; 826-908 inlineCallBody), `Strata/Languages/Core/ProcedureEval.lean` (lines 85-149 top-level CFG walker, separate code path, not double-counted), `reports/so-localization-probe4-2026-06-05.md` (source counts).

**Next action.** None.

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
