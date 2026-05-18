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

Snapshot from the latest run on the 12-program benchmark. `OK` columns
report pipeline-stage success; backend columns report verification outcome.

```
Program                  |  Strip |    B2S |    Fix |    deductive |   bugFinding |         cbmc
---------------------------------------------------------------------------------------------------
abs_func                 |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
array_sum                |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_array_eq             |     OK |     OK |     OK |         WARN |         WARN |         FAIL
aws_byte_cursor_advance  |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_ring_buffer          |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
loop_sum                 |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
max_func                 |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
nondet_branch            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
pointer_arith            |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
simple_add               |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
simple_assert            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
swap                     |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL

     deductive: 4 pass, 7 partial, 1 warn
    bugFinding: 0 pass, 11 partial, 1 warn
          cbmc: 0 pass, 12 fail
```

## Known blockers

- **CBMC: structured-body assumption.** `coreToGotoFiles` (in
  `Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean:490`) dispatches
  every procedure through `procedureToGotoCtx`, which assumes a
  structured body and errors on CFG procedures with "expected
  structured body, got CFG". A `procedureToGotoCtxViaCFG` already
  exists at `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean:188`
  but is only wired into a test E2E. Fix path: dispatch CFG bodies
  through that. Visible on 5 of the 12 programs (`abs_func`,
  `array_sum`, `loop_sum`, `max_func`, `nondet_branch`); the other 7
  hit the inout blocker first.
- **CoreToGoto: inout-parameter double-collection.** Inout parameters
  (e.g., `_exn`) are assigned in the body, so `definedVars` collects
  them as locals and they get renamed with `mkLocalSymbol`
  (`main::1::_exn`) while the type env only knows the formal name
  (`main::_exn`). Surfaces as `[toGotoExprCtx] Not yet implemented:
  LExpr.fvar`. Source location: `CoreToGOTOPipeline.lean:286-292`.
  Affects 7 programs.
- **bugFinding partials.** Symbolic execution finds potential
  counterexamples for assertions on programs whose preconditions are
  insufficient. Expected behaviour for SMACK programs as currently
  translated; not a pipeline bug.
- **`aws_array_eq` emits 0 VCs (deductive=WARN, bugFinding=WARN).**
  When `main` asserts directly on the return value of a user procedure
  (`assert(aws_array_eq(...) == true)`) and that procedure is included
  in the default verification set, the call-elimination / inlining pass
  consumes the `assert__i32` calls without emitting their synthetic-
  `requires` VCs. The asserts disappear before they reach the solver,
  so the verifier reports `All 0 goals passed`. Workaround:
  `strata verify --procedures main aws_array_eq.core.st` produces the
  expected 3 VCs (all FAIL on this benchmark, since SMACK provides no
  preconditions on `main`). Affects `aws_array_eq` only on the current
  benchmark; the other programs that call user procedures from `main`
  (`abs_func`, `max_func`, `swap`, etc.) assert on a local variable
  populated from the call result, so the assert survives elimination.
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
