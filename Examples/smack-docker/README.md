# SMACK → BoogieToStrata Pipeline

End-to-end pipeline for verifying SMACK-generated Boogie programs through
the Strata toolchain. Source `.c` programs live in `programs/`. SMACK,
BoogieToStrata, and the verifier backends are run via the scripts in this
directory.

## Pipeline

```
.c → SMACK (Docker) → .bpl → BoogieToStrata → .core.st → backend
                                                          ├── strata verify (deductive)
                                                          ├── strata verify (bugFinding)
                                                          └── StrataCoreToGoto + symtab2gb + cbmc
```

## Prerequisites

- [Finch](https://github.com/runfinch/finch) installed and the VM initialized
  (`finch vm init`).
- The `smack` container image built (instructions below).
- The Strata project built locally (`lake build` from the repo root) so the
  `strata` and `StrataCoreToGoto` binaries are available under
  `.lake/build/bin/`.
- `cbmc` (≥6.9) and `symtab2gb` on `PATH` if running the cbmc backend.
  On macOS: `brew install cbmc`.

## Building the SMACK image

```bash
cd Examples/smack-docker
finch build --platform linux/amd64 -t smack .
```

The image uses `--platform linux/amd64` because SMACK's dependencies
(dotnet-sdk-5.0, Z3 x86_64 binaries) are not available for ARM64.

## Regenerating .bpl from .c

The `.bpl` files are not committed to the repo (they are SMACK-generated and
each ~16k lines). Regenerate them locally:

```bash
finch run --rm --entrypoint /bin/sh \
  -v "$PWD/programs:/programs" \
  smack -c '. /home/user/smack.environment && \
            cd /programs && \
            for f in *.c; do \
              smack --no-verify -bpl "${f%.c}.bpl" "$f"; \
            done'
```

This produces one `.bpl` per `.c`. The `.gitignore` in `programs/` keeps
these out of version control.

## Running the multi-backend pipeline

```bash
python3 run_pipeline.py --backends deductive,bugFinding,cbmc
```

By default this picks up every `.bpl` in `programs/`. Pass specific files
to restrict the run:

```bash
python3 run_pipeline.py --backends deductive programs/simple_add.bpl
```

The script handles each program through the full chain:
strip prelude → BoogieToStrata → fix_core_st → backend(s).

## Current verification results

Snapshot from the latest run on the 25-program benchmark (12 original +
13 simplified AWS C Common functions). `OK` columns report pipeline-stage
success; backend columns report verification outcome. Run with
`--split-procs` to surface obligations the env-error contamination would
otherwise suppress.

```
Program                       |  Strip |    B2S |    Fix |    deductive |   bugFinding |         cbmc
-------------------------------------------------------------------------------------------------------
# Original benchmark
abs_func                      |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
array_sum                     |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_array_eq                  |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_byte_cursor_advance       |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_ring_buffer               |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
loop_sum                      |     OK |     OK |     OK |         PASS |      PARTIAL |      TIMEOUT
max_func                      |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
nondet_branch                 |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
pointer_arith                 |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
simple_add                    |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
simple_assert                 |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
swap                          |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL

# Extended benchmark (simplified AWS C Common)
aws_add_size_checked          |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_array_list_get            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_array_list_set            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_byte_buf_append           |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_byte_buf_init             |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_byte_cursor_eq            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_hash_string               |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_is_power_of_two           |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_linked_list_push          |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_min_max                   |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_mul_size_checked          |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_round_up_to_power_of_two  |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_string_eq                 |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL

     deductive: 5 pass, 20 partial, 0 warn, 0 fail, 0 n/a
    bugFinding: 0 pass, 25 partial, 0 warn, 0 fail, 0 n/a
          cbmc: 0 pass, 24 fail, 1 timeout, 0 n/a
```

## Known blockers

- **CBMC: structured-body assumption (resolved on this branch).**
  `coreToGotoFiles` (in `CoreToGOTOPipeline.lean`) dispatched every
  procedure through `procedureToGotoCtx`, which errored on CFG bodies
  with "expected structured body, got CFG". `procedureToGotoCtxViaCFG`
  already existed in `CoreCFGToGOTOPipeline.lean` but was only wired
  into a test E2E. Fixed by adding `procedureToGotoCtxDispatch` and
  `coreToGotoFilesDispatch` in `CoreCFGToGOTOPipeline.lean` that
  switch on `p.body` (avoiding the import cycle that would result from
  adding the dispatch directly to `CoreToGOTOPipeline.lean`), and
  pointing the `StrataCoreToGoto` binary at the dispatching wrapper.
  Was visible on 5 of the 25 programs (`abs_func`, `array_sum`,
  `loop_sum`, `max_func`, `nondet_branch`); they now translate cleanly
  through the CFG path. Regression test in
  `StrataTest/Backends/CBMC/GOTO/E2E_CoreToGOTO.lean` (programmatic CFG
  procedure construction; the `cfg ...` surface syntax is not
  parseable in `#strata` macros on this branch). See commit `74f0cc23a`.
- **CoreToGoto: inout-parameter rename collision (resolved on this
  branch).** By Strata Core convention, every `inout` parameter appears
  in BOTH `Procedure.Header.inputs` AND `Procedure.Header.outputs` with
  the same identifier. `procedureToGotoCtx` folded
  `formals.zip new_formals ++ outputs.zip new_outputs ++ …` into the
  rename map; outputs came second, so any inout name ended up bound to
  the local-symbol form (`main::1::x`) instead of the formal
  (`main::x`). At call sites, `CallArg.getInputExprs`
  (`Strata/Languages/Core/Statement.lean:105-109`) synthesizes
  `LExpr.fvar () id none` for inout args, and `LExpr.toGotoExprCtx`
  rejects typeless fvars — surfacing as `[toGotoExprCtx] Not yet
  implemented: LExpr.fvar () { name := "main::1::_exn" } none`. Fixed
  by filtering inouts out of the outputs list (so they bind to the
  formal-symbol form) and looking up the type from the threaded typing
  env at call-translation time. Both the structured and CFG paths
  patched (`CoreToGOTOPipeline.lean`, `CoreCFGToGOTOPipeline.lean`).
  Regression tests in `StrataTest/Backends/CBMC/GOTO/E2E_CoreToGOTO.lean`.
  See commit `f265cda63`.
- **`run_pipeline.py` cbmc-invocation flags (resolved on this branch).**
  Two latent bugs in `run_pipeline.py`'s cbmc invocation: line 331
  passed the GOTO JSON as a second positional argument to `symtab2gb`
  instead of via `--goto-functions`, and line 235 invoked `cbmc`
  without `--function main`. Both fixed; commit `4f309c63b`. Related:
  `InstToJson.lean` previously omitted the `guard` JSON field on
  ASSUME/ASSERT instructions when the guard was the constant `true`,
  which broke `symtab2gb` on every SMACK-generated program (which has
  `assume true` between every two source statements). Fixed by
  always emitting `guard` for ASSUME/ASSERT; commit `66e659656`.
- **CBMC: non-standard `main` signature (resolved on this branch).**
  SMACK-translated `main` takes parameters (memory maps, exception
  flags, address state) that don't match cbmc's expected entry-point
  signatures, so cbmc rejected the binary with "the program has no
  entry point" / rc=6. Fixed by emitting a synthetic `__cprover_entry()`
  shim alongside `main`: the shim declares one local per main formal,
  havocs each from `nondet`, calls main, ends. `buildEntryShim` lives
  in `CoreCFGToGOTOPipeline.lean`; `run_pipeline.py` invokes
  `cbmc --function __cprover_entry`. See commit `7e2b1fc25`.
- **CBMC: callee bodies not emitted.** `coreToGotoFiles*` translates
  only the entry procedure (`main`), leaving every callee — `add`,
  `assert__i32`, `_initialize`, the SMACK prelude stubs — as bodyless
  declarations in the symbol table. cbmc symbolically executes main,
  reaches a call, and reports `[.no-body.<callee>] no body for
  callee <callee>: FAILURE`. With the entry-point shim resolved, this
  is the dominant failure mode (5 programs, including
  `simple_assert`, `simple_add`, `aws_min_max`,
  `aws_is_power_of_two`, `aws_round_up_to_power_of_two`). Fix path:
  iterate over all reachable procedures in `coreToGotoFilesDispatch`,
  not just the entry; emit each via `procedureToGotoCtxDispatch` and
  splice all into the output JSON. The lifted-functions infrastructure
  in `emitProcWithLifted` is the right shape for this, but currently
  only handles `Core.Function` (purely-defined functions), not
  `Core.Procedure` (commands with side effects).
- **CBMC: array type mismatch on memory-map params.** Programs with
  memory-map parameters (the AWS C Common programs that pass `Map ref
  i8` for memory state) hit a different cbmc error after the shim:
  `function call: parameter "main::_M_0" type mismatch — got array
  size: integer, expected array 0: integer`. The shim's nondet
  initializer for the memory-map params produces an array shape cbmc
  considers incompatible with main's declared parameter type. 16 of
  25 programs hit this. Likely fix on the array-type emission for
  `Map ref i8` (`Strata/Backends/CBMC/GOTO/LambdaToCProverGOTO.lean`'s
  `LMonoTy.toGotoType`).
- **CBMC: BMC unrolling timeouts (mostly resolved on this branch).**
  4 programs (`abs_func`, `loop_sum`, `max_func`, `nondet_branch`)
  previously timed out at the default 120s. Cause:
  `coreCFGToGotoTransform` iterated blocks in `cfg.blocks` source
  order, where SMACK's CFG emission has if/else join points landing
  textually before their predecessors. Forward CFG edges thus
  rendered as `GOTO N` to earlier-numbered locations, which CBMC's
  loop detector classified as back-edges and instrumented with
  unwinding-assertions; the unwinding logic blew the timeout.
  `cbmc --show-loops` reported 8 spurious "loops" on `nondet_branch`
  despite the C source having zero loops. Fixed by emitting blocks
  in reverse-postorder via a new `cfgReversePostorder` helper in
  `CoreCFGToGOTOPipeline.lean`. After the fix, `--show-loops`
  reports 0 spurious loops on the 3 loop-free programs (abs_func,
  max_func, nondet_branch); they reach real verdicts in <100ms.
  `loop_sum` remains TIMEOUT because it has a real C `for` loop:
  cbmc correctly identifies the genuine back-edge and unrolls it,
  hitting the unwinding-assertion bound. That's the next-tier
  problem (real-loop bound or loop invariants), distinct from the
  spurious-back-edge issue this fix addresses. Regression test in
  `StrataTest/Backends/CBMC/GOTO/E2E_CoreToGOTO.lean`
  (`E2E_CFGRPOReorder`). See commit `520f3f573`.
- **Deductive PARTIAL breakdown (sample-based).** All 21 deductive
  PARTIALs sampled across the 25-program suite split into three
  sub-classes by failing-VC verdict and origin:
  - **(a) Missing `ensures` on a user-defined helper** — solver
    refutes with `🔶 can be both true and false`, label
    `callElimAssert_assert__i32_requires_0_NN`. Every assertion of
    the form `assert(callee(...) == expected)` where the user fn has
    no spec block. ~17 of 25 programs, varies in VC count per program.
    Fix lever: synthesize `ensures` from procedure bodies (Strata-side
    pass; not a Python regex — too easy to be unsound). The previously
    discussed approach via SMACK's `__CONTRACT_ensures` macro is
    blocked upstream by SMACK's missing `result()` expression.
  - **(b) `__VERIFIER_assume` is uninterpreted (partially resolved on
    this branch).** Same refuted verdict but label
    `(Origin_assert__i32_Requires)assert__i32_requires_0`, indicating
    a top-level requires-discharge VC rather than a per-call VC.
    Affected programs whose C source uses `assume(...)` to bound
    inputs; the assumption was dropped because `__VERIFIER_assume`
    had no spec after `strip_smack_prelude.py`. Fixed by synthesizing
    `free ensures (_i0 != 0)` on `__VERIFIER_assume` declarations
    during BoogieToStrata translation, gated on `--smack`. The
    `free ensures` form (Boogie semantics: callers may assume,
    implementation has no proof obligation) matches `assume`'s
    polarity. Mirrors the existing `assert_.<type>` `Requires`
    synthesis at `StrataGenerator.cs:VisitProcedure` with the dual
    polarity. Regression tests in
    `Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`.
    See commit `1b2231f99`.

    Empirically verified the synthesis propagates: every
    `[__VERIFIER_assume_ensures_0]` VC is discharged by the verifier
    (`✅ always true and is reachable from declaration entry`).
    `nondet_branch` flipped PARTIAL → PASS (one direct gain on the
    deductive backend). `abs_func` improved from 0 pass / 1 fail to
    7 pass / 1 fail; `max_func` from 0 pass / 1 fail to 1 pass / 1 fail.
    The remaining single failing VC on each is a separate sub-class
    (a) issue: an assert downstream of a user function call (`abs_val`,
    `max`) that lacks an `ensures` clause. Closing those needs the
    sub-class (a) lever, not more `__VERIFIER_assume` work.

    Side effect on cbmc: the synthesis adds path-condition constraints
    that cbmc's BMC unrolling now expands further on the
    `__VERIFIER_assume`-using programs. 4 of those (`abs_func`,
    `loop_sum`, `max_func`, `nondet_branch`) now timeout where they
    previously fast-FAILed at the symtab2gb stage; net cbmc column
    count moved from 0/25/0 pass/fail/timeout to 0/21/4.
  - **(e) Solver returns `unknown`** — verdict `❓ unknown`. Sample:
    `aws_byte_buf_append`, all 7 VCs. The asserted predicate chain
    involves nested int↔bit conversions (`_zext`, `_trunc`) over
    memory-map loads (`_load_i64`, `_load_ref`) on a program with 13
    `_M_N` map params. SMT formula complexity exceeds the solver's
    reach. Fix lever: SMT encoding work in
    `Strata/Languages/Core/SMTEncoder.lean` — array theory vs
    axiomatized maps, axiom pruning. Significant effort; likely the
    last sub-class to address.
- **`strip_smack_prelude.py` rationale is obsolete.** The strip
  pass's docstring claims the SMACK prelude bodies "use unstructured
  multi-target gotos incompatible with BoogieToStrata." Audited the
  actual bodies: only `__SMACK_and{32,16,8}` and `__SMACK_or32` have
  multi-target gotos (192/48/24/64 blocks each). All other names the
  strip removes (`__VERIFIER_assume`, `__SMACK_dummy`,
  `__SMACK_or{8,16,64}`, `__SMACK_check_overflow`,
  `__SMACK_loop_exit`, `boogie_si_record_*`, `corral_*`, `$alloc`)
  have structured bodies that BoogieToStrata translates cleanly —
  even with `--smack` and the now-required `InferModifies = true`,
  exit 0, no errors. The strip is broader than necessary by historical
  accident (prefix-match collateral damage); narrowing to just the
  bitwise-decompose family would be safe. Empirically, removing the
  strip does NOT close sub-class (b) on its own — see (b) above for
  why. So the strip narrowing is a code-hygiene improvement, not a
  verdict-improvement lever.
- **bugFinding partials.** Symbolic execution finds potential
  counterexamples for assertions on programs whose preconditions are
  insufficient. Same root cause as deductive sub-class (b) for the
  programs that use `assume(...)`; same root cause as sub-class (a)
  for the programs that call user fns without `ensures`. Expected
  behaviour given the current translation; not a pipeline bug.
- **Cross-procedure PE error contamination (`aws_array_eq` → 0 VCs).**
  `Strata/Languages/Core/ProgramEval.lean` threads a single `Env`
  through every procedure in declaration order: each `.proc` decl runs
  `Procedure.eval declsE proc`, and the resulting env is passed as
  `declsE` to the next procedure. If any procedure's evaluation sets
  `Env.error`, `Procedure.fixupError`
  (`Strata/Languages/Core/ProcedureEval.lean:23-27`) leaves the error
  in place rather than clearing it. Subsequent procedures' bodies then
  short-circuit on every command — `Statement.Command.eval` and
  `evalAuxGo` both early-return when `env.error.isSome`
  (`Strata/Languages/Core/StatementEval.lean:64-65, 618-619`) — so
  their `deferred` obligations are never produced and
  `extractObligations` walks empty bodies.

  On `aws_array_eq`, the upstream procedure that errors is
  `aws_array_eq` itself: its CFG body has a back-edge
  (`_bb5 → _bb4` in the SMACK output, encoding the C `for` loop) and
  `Procedure.eval`'s CFG branch
  (`ProcedureEval.lean:204-211`) unrolls it with bounded fuel,
  producing an `Env.error` on at least one path. That error rides
  through to `main`'s evaluation, killing the three
  `callElimAssert_assert__i32_requires_*` obligations.

  Empirical confirmation:
  - `strata verify --procedures main aws_array_eq.core.st` → 3 VCs
    (skips `aws_array_eq` evaluation entirely, so no error to
    propagate).
  - Reordering the `.core.st` so `main` precedes `aws_array_eq` → 12
    VCs (previously-suppressed obligations from `main`,
    `__SMACK_static_init`, `_initialize`, etc. all reappear).
  - Replacing `aws_array_eq`'s body with a linear CFG (no back-edge)
    → 3 VCs.

  The visible `WARN` is on `aws_array_eq` because SMACK's translation
  emits `aws_array_eq` (a CFG procedure with a loop) ahead of `main`
  in the program. The same mechanism would suppress VCs in any
  benchmark where a procedure with a looping CFG body is declared
  before any procedure that contains assert calls.

  Fix path: clear `Env.error` (and reset the affected per-procedure
  state) at the boundary between procedures in `Program.eval` (or in
  `Procedure.eval`'s return), so per-procedure evaluation failures
  don't bleed into the rest of the program.
- **`Strata.Transform.ProcBodyVerifyCorrect` proof file (fixed on
  this branch tip).** Surfaced during this reproduction on the prior
  tip: the merge from `main` left three call sites in
  `Strata/Transform/ProcBodyVerifyCorrect.lean:856,859,862` passing
  `proc.body` (now `Procedure.Body`) where a `List Statement` was
  expected. Symptom: `Application type mismatch ... Config.stmts
  proc.body`. The file has no importers in the runtime graph, so the
  three executables (`strata`, `StrataCoreToGoto`, `StrataToCBMC`)
  build despite the failure — but `lake build` exits non-zero. Fixed
  by substituting the destructured `ss` (already in scope from
  `procToVerifyStmt_is_structured`) for `proc.body` at the three
  sites; build now passes 585/585.

See [`Tools/BoogieToStrata/Docs/STATUS.md`](../../Tools/BoogieToStrata/Docs/STATUS.md)
for translator-level status.

## Scripts in this directory

- `run_pipeline.py` — end-to-end multi-backend driver.
- `strip_smack_prelude.py` — removes SMACK prelude bodies before
  translation; reduces translation work and avoids unstructured CFGs in
  prelude-only procedures.
- `fix_core_st.py` — post-processes BoogieToStrata output to work around
  a few known translation issues.
- `Dockerfile` — builds the SMACK container image.
