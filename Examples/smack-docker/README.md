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
loop_sum                      |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
max_func                      |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
nondet_branch                 |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
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

     deductive: 4 pass, 21 partial, 0 warn, 0 fail, 0 n/a
    bugFinding: 0 pass, 25 partial, 0 warn, 0 fail, 0 n/a
          cbmc: 0 pass, 25 fail, 0 n/a
```

## Known blockers

- **CBMC: structured-body assumption.** `coreToGotoFiles` (in
  `Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean:490`) dispatches
  every procedure through `procedureToGotoCtx`, which assumes a
  structured body and errors on CFG procedures with "expected
  structured body, got CFG". A `procedureToGotoCtxViaCFG` already
  exists at `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean:188`
  but is only wired into a test E2E. Fix path: dispatch CFG bodies
  through that. Visible on 5 of the 25 programs (`abs_func`,
  `array_sum`, `loop_sum`, `max_func`, `nondet_branch`).
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
- **`run_pipeline.py` invokes `symtab2gb` with the wrong flag.** With
  the inout collision resolved, the 20 affected programs now produce
  well-formed `symtab.json` and `goto.json`; `run_pipeline.py:331`
  then invokes `symtab2gb <symtab> <goto> --out …` with the GOTO file
  as a positional argument. `symtab2gb` interprets that as a second
  symtab and rejects it: `JSON object must have key 'symbolTable'`.
  Fix: pass the GOTO file via `--goto-functions <goto>`. Related: the
  cbmc invocation at `run_pipeline.py:235` is missing `--function main`,
  which will cause an exit-code-6 misclassification once symtab2gb
  works.
- **bugFinding partials.** Symbolic execution finds potential
  counterexamples for assertions on programs whose preconditions are
  insufficient. Expected behaviour for SMACK programs as currently
  translated; not a pipeline bug.
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
