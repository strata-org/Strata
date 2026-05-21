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

Snapshot from the latest run on the 43-program benchmark:

- 12 original benchmark programs.
- 13 simplified AWS C Common functions (hand-written, in the
  `programs/` style of `aws_array_eq.c`).
- 6 verbatim CBMC harnesses imported from `awslabs/aws-c-common`'s
  `verification/cbmc/proofs/`.
- 12 verbatim CBMC harnesses imported from `FreeRTOS/coreJSON`'s
  `test/cbmc/proofs/` (each bundles `core_json.h` + `core_json.c`
  alongside the harness body).

The verbatim harness groups use small adapter shims to map CBMC
primitives onto SMACK's `__VERIFIER_*` family; the bar for inclusion
was translatability (Strip / B2S / Fix all OK), not verification.

The deductive / bugFinding columns below are from a non-`--split-procs`
run; the cbmc column on the first 31 rows is the prior `--split-procs`
snapshot from the smaller suite. The 12 coreJSON harnesses were not
re-run through cbmc — vendoring full `core_json.c` produces large
.bpl files that hit the same callee-bodies blocker as everything else
(see *Known blockers*); marked as `n/a` to flag the lack of fresh
data.

`OK` columns report pipeline-stage success; backend columns report
verification outcome. Run with `--split-procs` to surface obligations
the env-error contamination would otherwise suppress (some PASS rows
in non-split mode become PARTIAL when split-procs runs each procedure
independently).

```
Program                               |  Strip |    B2S |    Fix |    deductive |   bugFinding |         cbmc
---------------------------------------------------------------------------------------------------------------
# Original benchmark
abs_func                              |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
array_sum                             |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_array_eq                          |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_byte_cursor_advance               |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_ring_buffer                       |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
loop_sum                              |     OK |     OK |     OK |         PASS |      PARTIAL |      TIMEOUT
max_func                              |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
nondet_branch                         |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
pointer_arith                         |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
simple_add                            |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
simple_assert                         |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
swap                                  |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL

# Extended benchmark (simplified AWS C Common)
aws_add_size_checked                  |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_array_list_get                    |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_array_list_set                    |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_byte_buf_append                   |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_byte_buf_init                     |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_byte_cursor_eq                    |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_hash_string                       |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_is_power_of_two                   |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_linked_list_push                  |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_min_max                           |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_mul_size_checked                  |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_round_up_to_power_of_two          |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL
aws_string_eq                         |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL

# CBMC harness import (verbatim from awslabs/aws-c-common)
aws_add_size_checked_harness          |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_add_size_saturating_harness       |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_is_power_of_two_harness           |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_mul_size_checked_harness          |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_mul_size_saturating_harness       |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL
aws_round_up_to_power_of_two_harness  |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL

# CBMC harness import (verbatim from FreeRTOS/coreJSON)
JSON_Iterate_harness                  |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
JSON_SearchConst_harness              |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
JSON_Validate_harness                 |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
skipAnyScalar_harness                 |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
skipCollection_harness                |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
skipDigits_harness                    |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
skipEscape_harness                    |     OK |     OK |     OK |         FAIL |         FAIL |          n/a
skipObjectScalars_harness             |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
skipScalars_harness                   |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
skipSpace_harness                     |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
skipString_harness                    |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a
skipUTF8_harness                      |     OK |     OK |     OK |         PASS |      PARTIAL |          n/a

     deductive: 29 pass, 13 partial, 0 warn, 1 fail, 0 n/a
    bugFinding: 0 pass, 42 partial, 0 warn, 1 fail, 0 n/a
          cbmc: 0 pass, 30 fail, 1 timeout, 12 n/a
```

The two CBMC-import groups represent the easy-to-translate slice of
their respective upstream proof trees:
- **aws-c-common.** 6 of ~190 upstream proofs — the rest depend on
  AWS struct types (`aws_byte_buf`, `aws_array_list`, `aws_hash_*`)
  or `proof_helpers/` infrastructure that requires stub work.
- **coreJSON.** 12 of 15 upstream proofs translate cleanly (the 3
  search harnesses — `arraySearch`, `objectSearch`, `multiSearch` —
  segfault inside SMACK's clang frontend). One of the 12,
  `skipEscape_harness`, exits the deductive verifier with SIGABRT,
  surfacing a Strata-side bug worth tracking as a regression input.

## What this branch ships (vs `origin/main`)

Pipeline / benchmark:

- `run_pipeline.py` — `--split-procs` mode (sidesteps cross-procedure
  env-error contamination) and corrected `symtab2gb`/`cbmc` flags.
  Commits `38c13c272`, `4f309c63b`, `451b06560`.
- 13 new simplified AWS C Common programs in `programs/`, expanding
  the suite from 12 to 25. Commit `ee57bb2b7`.
- 6 verbatim CBMC harnesses imported from `awslabs/aws-c-common`'s
  `verification/cbmc/proofs/` tree. The fetcher (a throwaway
  `wt-test/fetch_cbmc_harness.py`) prefilters for self-contained
  harnesses, inlines the function-under-test body from upstream's
  `math.inl` / `math.fallback.inl`, and emits one self-contained `.c`
  per program with an adapter prelude that shims CBMC primitives onto
  SMACK's `__VERIFIER_*` family. Commit `283bdac16`.
- 12 verbatim CBMC harnesses imported from `FreeRTOS/coreJSON`'s
  `test/cbmc/proofs/` tree, expanding the suite to 43. Each program
  bundles `core_json.h` + `core_json.c` verbatim alongside the harness
  body folded into `main()`; the prelude reroutes `coreJSON_ASSERT`
  through `__VERIFIER_assume` so the asserts CBMC enforces as
  preconditions become assumptions for the deductive verifier.
  Generator at `wt-test/fetch_corejson_harness.py`. Commit `2c7a49181`.

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
  the 25 hand-written programs hit this; the 18 verbatim CBMC
  harnesses use only primitive scalar params, so they avoid this
  blocker. Likely fix
  on the array-type emission for
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
- **Deductive PARTIAL breakdown (sample-based).** The deductive
  PARTIALs across the 43-program suite split into two sub-classes by
  failing-VC verdict and origin:
  - **(a) Missing `ensures` on a user-defined helper** — solver
    refutes with `🔶 can be both true and false`, label
    `callElimAssert_assert__i32_requires_0_NN`. Every assertion of
    the form `assert(callee(...) == expected)` where the user fn has
    no spec block. ~17 of the 25 hand-written programs hit this; the
    18 verbatim CBMC harnesses don't trip it because their callees
    have no postconditions to discharge (they verify call shape, not
    functional correctness).
    `abs_func` and `max_func` were previously masked as a separate
    `__VERIFIER_assume` blocker; once that was fixed (commit
    `1b2231f99`) their residual VCs landed here. Fix lever: synthesize
    `ensures` from procedure bodies (Strata-side pass; not a Python
    regex — too easy to be unsound). The previously discussed approach
    via SMACK's `__CONTRACT_ensures` macro is blocked upstream by
    SMACK's missing `result()` expression.
  - **(b) Solver returns `unknown`** — verdict `❓ unknown`. Sample:
    `aws_byte_buf_append`, all 7 VCs. The asserted predicate chain
    involves nested int↔bit conversions (`_zext`, `_trunc`) over
    memory-map loads (`_load_i64`, `_load_ref`) on a program with 13
    `_M_N` map params. SMT formula complexity exceeds the solver's
    reach. Fix lever: SMT encoding work in
    `Strata/Languages/Core/SMTEncoder.lean` — array theory vs
    axiomatized maps, axiom pruning. Significant effort; likely the
    last sub-class to address.
- **bugFinding partials.** Symbolic execution finds potential
  counterexamples for assertions on programs whose preconditions are
  insufficient. Same root cause as deductive sub-class (a) (callees
  with no `ensures`). Expected behaviour given the current translation;
  not a pipeline bug.
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

## Potential future work

Benchmark expansion — additional CBMC harness sources surveyed but
not yet imported:

- **`aws/s2n-tls`** (Apache-2.0, 161 harnesses under
  `tests/cbmc/proofs/`). Richest source by far, but most depend on
  s2n's `cbmc_proof/make_common_datastructures.h`. The
  arithmetic/predicate slice (`s2n_add_overflow`, `s2n_sub_overflow`,
  `s2n_mul_overflow`, `s2n_is_base64_char`,
  `s2n_constant_time_equals`) is verbatim-importable; ~5–10 programs.
- **`FreeRTOS/coreMQTT`** (MIT, 58 harnesses under
  `test/cbmc/proofs/`). The property-getter family
  (`MQTTPropGet_*`) verifies memory safety only (no functional
  postconditions), so values as a benchmark are limited.

Other surveyed repos with negative results: the broader `awslabs/aws-c-*`
family (cal/io/compression/checksums/etc.) has no CBMC proofs upstream;
`diffblue/cbmc/regression` is for compiler/solver regressions, not
function-under-test harnesses; `aws/aws-encryption-sdk-c`'s ~100
harnesses depend on OpenSSL EVP types and a two-level proof_helpers
hierarchy that would require nontrivial stub work.

To extend the existing fetcher (`wt-test/fetch_cbmc_harness.py`) for
these: parameterize `REPO`/`REF`/`PROOFS_DIR`/`BODY_SOURCES`, run once
per source repo, and curate the union into `programs/`.

Other levers (orthogonal to benchmark expansion):

- Address the deductive sub-class (a) blocker (synthesize `ensures`
  from procedure bodies in a Strata-side pass). Would flip ~17 of the
  25 hand-written programs from PARTIAL → PASS deductive. See *Known
  blockers*.
- Address the cbmc callee-bodies blocker (iterate over all reachable
  procedures in `coreToGotoFilesDispatch`, not just `main`). Would
  unblock the cbmc column for the ~9 programs that currently hit
  `[.no-body.<callee>]`. See *Known blockers*.

## Scripts in this directory

- `run_pipeline.py` — end-to-end multi-backend driver.
- `strip_smack_prelude.py` — removes SMACK prelude bodies before
  translation. Mostly historical now (BoogieToStrata translates the
  prelude under `--smack`); kept for the `__SMACK_and{32,16,8}` and
  `__SMACK_or32` bitwise-decompose stubs that still trip translation.
- `fix_core_st.py` — post-processes BoogieToStrata output to work around
  a few known translation issues.
- `Dockerfile` — builds the SMACK container image.
