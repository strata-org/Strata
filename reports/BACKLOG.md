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

**Status:** BLOCKED — waiting for Aaron.

**Next action.** Once Aaron hands off the equalizer benchmark, run it through the smack-docker pipeline (`python3 run_pipeline.py` against `Examples/smack-docker/programs/`) and record verdicts alongside the existing 93-program suite.

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
