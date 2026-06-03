# Backlog

Open feature work on `htd/smack` not tied to a specific bug report. Each entry: status + design pointer + next action.

## Evaluator

### Multi-`Env` return signature for `Command.eval`

**Status:** OPEN — design ready, no code.

**Design:** [`Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md`](../Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md) (build sequence in steps 1–7).

**Summary.** Widen `Command.eval`, `Command.handleCall`, `Command.inlineCallContract`, and `Command.inlineCallBody` from `Command × Env` to `Command × List Env`. Today's single-env squeeze in `inlineCallBody` (commit `fa82fe42b`) refuses callee bodies whose symbolic `if` produces multiple result envs with divergent bindings; the `.BodyOrContract` arm then falls back to contract reasoning, which is unnecessarily lossy.

**Why it matters.** Single residual portfolio PARTIAL under `--call-policy bodyOrContract` (the `nondet_branch` case) is exactly this multi-result situation — see `Examples/smack-docker/BRANCH_FEATURES.md` §4.3 "Multi-branch limitation". Landing this turns the residual PARTIAL into a PASS and removes the only known soundness-preserving precision gap in body-eval.

**Next action.** Execute steps 1–6 in `MULTIPATH_COMMAND_EVAL.md`'s build sequence; cross-validate with step 7 (full portfolio under `--call-policy bodyOrContract`).

## Benchmarks

### Test the pipeline on the equalizer benchmark

**Status:** BLOCKED — waiting for Aaron.

**Next action.** Once Aaron hands off the equalizer benchmark, run it through the smack-docker pipeline (`python3 run_pipeline.py` against `Examples/smack-docker/programs/`) and record verdicts alongside the existing 93-program suite.

## Investigations

### Qualitative analysis of the 15 PASS-? unreachable cases

**Status:** OPEN.

**Summary.** v5/v6 surfacing flagged 15 programs in the portfolio whose deductive PASS verdicts come from `path unreachable` rather than a discharged obligation. We currently distinguish them in the matrix as `PASS-?`. Goal: for each of the 15, determine whether the unreachability is genuine (program-as-modeled has no live path to the assertion) or spurious (modeling artifact — e.g. assume(false) introduced by translation, dead branch, missing havoc).

**Why it matters.** A genuine unreachable assertion is a vacuous PASS that should not count toward soundness; a spurious one is a translator/evaluator gap masquerading as a proof and points to a real fix. Without this analysis the v6 PASS column over-counts.

**Pointers.** Background analysis in [`v5-pass-question-mark-analysis.md`](v5-pass-question-mark-analysis.md); v6 surfacing logic in `Examples/smack-docker/run_pipeline.py`'s `parse_strata_output`. Per-program PASS-? list in `Examples/smack-docker/README.md` "v6 per-program detail".

**Next action.** Walk each of the 15 programs: re-run with `--strata-verify-flag --print-paths`, inspect which assertion produced the unreachable verdict, and classify (genuine / translator artifact / evaluator gap). Document classification + per-class fix in a follow-up report.
