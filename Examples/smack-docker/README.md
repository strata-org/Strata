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

## What this branch ships (vs `origin/main`)

Pipeline / benchmark:

- `run_pipeline.py` — `--split-procs` mode (sidesteps cross-procedure
  env-error contamination) and corrected `symtab2gb`/`cbmc` flags.
  Commits `38c13c272`, `4f309c63b`, `451b06560`.
- 13 new simplified AWS C Common programs in `programs/`, expanding
  the suite from 12 to 25. Commit `ee57bb2b7`.

BoogieToStrata (cherry-picked from PR 1149 plus follow-up):

- `--smack` CLI flag, gating SMACK-specific behavior (`InferModifies`
  + `assert_.<type>` requires injection). Commits `6b04d9399`,
  `0e54ff2bd`, `ac814e582`.
- `__VERIFIER_assume` `free ensures (_i0 != 0)` synthesis under
  `--smack`, mirroring the `assert_` pattern with dual polarity.
  Commit `1b2231f99`.

CBMC backend (`Strata/Backends/CBMC/GOTO/`):

- Body-aware dispatch — CFG bodies now route through
  `procedureToGotoCtxViaCFG` instead of erroring "expected structured
  body, got CFG". Commit `74f0cc23a`.
- Inout-parameter rename-collision fix and call-site type lookup,
  patched in both the structured and CFG paths. Commit `f265cda63`.
- Synthetic `__cprover_entry()` shim with nondet-initialized main
  args, so cbmc accepts the entry point. Commit `7e2b1fc25`.
- `guard` JSON field always emitted on ASSUME/ASSERT (was elided
  when guard was constant `true`, which `symtab2gb` rejected).
  Commit `66e659656`.
- CFG block emission in reverse-postorder, eliminating the spurious
  back-edges that triggered cbmc unwinding-assertion timeouts.
  Commit `520f3f573`.

Regression coverage in `StrataTest/Backends/CBMC/GOTO/E2E_CoreToGOTO.lean`
and `Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`.

## Known blockers

- **CBMC: callee bodies not emitted.** `coreToGotoFiles*` translates
  only the entry procedure (`main`), leaving every callee — `add`,
  `assert__i32`, `_initialize`, SMACK prelude stubs, user-defined
  helpers — as bodyless declarations. cbmc reaches a call and reports
  `[.no-body.<callee>] no body for callee <callee>: FAILURE`. This is
  the dominant cbmc failure mode for programs without memory-map
  parameters. Fix path: iterate over all reachable procedures in
  `coreToGotoFilesDispatch`, not just the entry; emit each via
  `procedureToGotoCtxDispatch` and splice into the output JSON. The
  lifted-functions infrastructure in `emitProcWithLifted` is the right
  shape but currently only handles `Core.Function`, not
  `Core.Procedure`.
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
- **CBMC: real-loop unwinding bound.** `loop_sum` has a real C `for`
  loop, so cbmc's BMC unroller correctly identifies the genuine
  back-edge and tries to unroll without bound, hitting the default
  120s timeout. Fix path: pass `--unwind <N>` (with `N` chosen per
  program) or attach a loop invariant. The 3 other previously-timing-out
  programs (`abs_func`, `max_func`, `nondet_branch`) had **spurious**
  back-edges from the GOTO emission order; that's resolved on this
  branch — see *What this branch ships → CFG block emission in
  reverse-postorder*.
- **Deductive PARTIAL breakdown (sample-based).** The 20 deductive
  PARTIALs across the 25-program suite (post sub-class (b) fix)
  split into three sub-classes by failing-VC verdict and origin:
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
    this branch).** Failing-VC label
    `(Origin_assert__i32_Requires)assert__i32_requires_0` — a
    top-level requires-discharge VC. Affected programs whose C source
    uses `assume(...)` to bound inputs; the assumption was dropped
    because `__VERIFIER_assume` had no spec. Fixed by synthesizing
    `free ensures (_i0 != 0)` on `__VERIFIER_assume` declarations
    under `--smack`; commit `1b2231f99`. `nondet_branch` flipped
    PARTIAL → PASS; `abs_func`, `max_func` retained one failing VC
    each, now traced to sub-class (a) — an assert downstream of a
    user-function call (`abs_val`, `max`) with no `ensures`. Closing
    those needs the sub-class (a) lever.
  - **(e) Solver returns `unknown`** — verdict `❓ unknown`. Sample:
    `aws_byte_buf_append`, all 7 VCs. The asserted predicate chain
    involves nested int↔bit conversions (`_zext`, `_trunc`) over
    memory-map loads (`_load_i64`, `_load_ref`) on a program with 13
    `_M_N` map params. SMT formula complexity exceeds the solver's
    reach. Fix lever: SMT encoding work in
    `Strata/Languages/Core/SMTEncoder.lean` — array theory vs
    axiomatized maps, axiom pruning. Significant effort; likely the
    last sub-class to address.
- **`strip_smack_prelude.py` is overbroad.** The strip removes prelude
  bodies whose multi-target gotos BoogieToStrata used to choke on. With
  `--smack` and `InferModifies = true`, only `__SMACK_and{32,16,8}` and
  `__SMACK_or32` still need stripping; the rest translate cleanly. Code-
  hygiene cleanup (narrow the strip list), not a verdict-improvement
  lever.
- **bugFinding partials.** Symbolic execution finds potential
  counterexamples for assertions on programs whose preconditions are
  insufficient. Same root cause as deductive sub-class (b) for the
  programs that use `assume(...)`; same root cause as sub-class (a)
  for the programs that call user fns without `ensures`. Expected
  behaviour given the current translation; not a pipeline bug.
- **Cross-procedure PE error contamination (silently dropped VCs,
  issue #1185).** `ProgramEval.lean` threads a single `Env` through
  every procedure in declaration order. If `Procedure.eval` sets
  `Env.error` (e.g. CFG fuel exhaustion on a loop), `fixupError`
  doesn't clear it; subsequent procedures short-circuit on every
  command and emit no obligations. Use `--split-procs` mode in
  `run_pipeline.py` as a workaround — it runs each procedure
  independently. Fix path: clear `Env.error` at the boundary between
  procedures in `Program.eval`. See issue #1185 for full repro and
  empirical analysis.

See [`Tools/BoogieToStrata/Docs/STATUS.md`](../../Tools/BoogieToStrata/Docs/STATUS.md)
for translator-level status.

## Scripts in this directory

- `run_pipeline.py` — end-to-end multi-backend driver.
- `strip_smack_prelude.py` — removes SMACK prelude bodies before
  translation. Mostly historical now (BoogieToStrata translates the
  prelude under `--smack`); kept for the `__SMACK_and{32,16,8}` and
  `__SMACK_or32` bitwise-decompose stubs that still trip translation.
- `fix_core_st.py` — post-processes BoogieToStrata output to work around
  a few known translation issues.
- `Dockerfile` — builds the SMACK container image.
