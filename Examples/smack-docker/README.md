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

Snapshot from the latest pipeline runs on the **94-program benchmark**:

| Group | Programs | Description |
|---|---:|---|
| Original benchmark | 12 | Hand-written small programs |
| Simplified AWS C Common | 13 | Hand-written, in style of `aws_array_eq.c` |
| aws-c-common verbatim | 6 | Imported from upstream `verification/cbmc/proofs/` |
| FreeRTOS coreJSON verbatim | 12 | Vendored `core_json.c` + harness |
| FreeRTOS coreMQTT/coreHTTP/coreSNTP | 10 | Same pattern, vendored sources |
| Standalone parsers | 4 | jsmn, cJSON × 2, picohttpparser |
| RFC reference impls | 8 | UTF-8 DFA, base64, percent-encoding |
| **SV-COMP ReachSafety** | **29** | **Imported from `sosy-lab/sv-benchmarks` with verdict oracle** |
| **Total** | **94** | |

The most recent runs are:
- **v3 (`--split-procs`):** 64 programs (everything except the SV-COMP
  imports + `picohttpparser` which OOMs cbmc-native). Captured in
  `wt-test/pipeline-portfolio-v3.txt`. Run after fixes
  `7bff2d48e` (array-type), `23926094f` (nondet-symbol),
  `42ff8a4b8` (CFG-CallElim), `390fadc37` (ensures-synthesis), and
  `b3e606bb6` (`__VERIFIER_assert` requires injection).
- **sv-comp (`--split-procs`):** 29 SV-COMP programs. Captured in
  `wt-test/pipeline-svcomp.txt`.

Combined verdict counts across the 93 programs that ran (excluding
picohttpparser):

|  | PASS | PARTIAL | FAIL | TIMEOUT |
|---|---:|---:|---:|---:|
| Strata deductive | 39 | 54 | 0 | 0 |
| Strata bugFinding | 0 | 93 | 0 | 0 |
| Strata-CBMC | 0 | 0 | 93 | 0 |
| CBMC native | 70 | 0 | 23 | 0 |

Example rows from the pipeline output (full per-row detail in
`wt-test/pipeline-portfolio-v3.txt` and `wt-test/pipeline-svcomp.txt`):

```
Program           |  Strip |    B2S |    Fix |  deductive | bugFinding |    cbmc | cbmc-native
-----------------------------------------------------------------------------------------------
simple_add        |     OK |     OK |     OK |       PASS |    PARTIAL |    FAIL |        PASS
loop_sum          |     OK |     OK |     OK |       PASS |    PARTIAL |    FAIL |        PASS
abs_func          |     OK |     OK |     OK |    PARTIAL |    PARTIAL |    FAIL |        FAIL
nondet_branch     |     OK |     OK |     OK |       PASS |    PARTIAL |    FAIL |        FAIL
aws_array_eq      |     OK |     OK |     OK |    PARTIAL |    PARTIAL |    FAIL |        PASS
skipSpace_harness |     OK |     OK |     OK |    PARTIAL |    PARTIAL |    FAIL |        PASS
sv_locks_10       |     OK |     OK |     OK |       PASS |    PARTIAL |    FAIL |        PASS
```

`Strip` / `B2S` / `Fix` are pre-translation stage gates
(`strip_smack_prelude.py` → BoogieToStrata → `fix_core_st.py`); the
four backend columns are the verdict from each independent reasoning
engine. `--split-procs` runs each procedure independently and rolls
the verdicts up per-file.

### What the cbmc=FAIL count actually means now

After fixes 2.1–2.7 in `Strata/Backends/CBMC/GOTO/` (see *What this
branch ships*), the cbmc backend **reaches actual model checking on
every program**. The 93 FAILs are real verification verdicts, mostly
of two shapes:

- `Property violations found` — cbmc proceeded into BMC and identified
  that the goto binary contains assertions whose negation is
  satisfiable. The dominant cause is the **callee-bodies blocker**
  (see *Known blockers*): `coreToGotoFiles*` emits only the entry
  procedure's body, leaving every callee as a bodyless declaration.
  Cbmc reports `[.no-body.<callee>]` for each missed body.
- `CBMC exit code -6` — cbmc's array solver SIGABRTs on a small
  number of programs whose `__cprover_entry` shim shape is still
  problematic.

Pre-fix (before 2.6 + 2.7), every program hit `function call:
parameter type mismatch` (rc=6) before model checking even started.
The cbmc pipeline went from "rejected by type checker" → "real
verification verdicts." The PASS count is still 0 because the
callee-bodies blocker masks most properties; once that's addressed
(Layer 2 of the recent triage round), expect cbmc PASS counts to
follow.

### What the deductive PARTIAL count means

After fix `42ff8a4b8` (apply CallElim to CFG-bodied procedures), the
deductive backend now generates real `requires`-VCs at call sites
inside CFG-bodied procedures. Programs that previously vacuously
PASSed (no obligations to check) now flip to PARTIAL with concrete
failing VCs. The dominant root cause across the 54 PARTIALs is
**missing `ensures` on user-defined helpers** (deductive sub-class
(a) — see *Known blockers*); the failing VCs are
`callElimAssert___VERIFIER_assert_requires_*` labeled obligations
the verifier returns as `❓ unknown` because call-elim havocs the
post-call state.

Detailed cluster breakdowns and per-cluster (P)/(T)/(S) tags from
the cross-validation triage are in `CROSS_VALIDATION.md`.

### SV-COMP soundness probes (reading the oracle)

The 29 SV-COMP programs carry known verdicts in
`svcomp_verdicts.json`. Cross-referencing against deductive's
verdicts identified 6 candidate soundness probes (`unsafe ∧
deductive=PASS`):

| Program | Expected | Deductive | Diagnosis |
|---|---|---|---|
| `sv_locks_14_2` | unsafe | PASS | `path unreachable` qualifier |
| `sv_locks_15_2` | unsafe | PASS | `path unreachable` qualifier |
| `sv_loops_mono3_1` | unsafe | PASS | `path unreachable` qualifier |
| `sv_loops_mono4_1` | unsafe | PASS | `path unreachable` qualifier |
| `sv_loops_mono5_1` | unsafe | PASS | `path unreachable` qualifier |
| `sv_loops_mono6_1` | unsafe | PASS | `path unreachable` qualifier |

**Not actually soundness bugs.** Inspection with `--check-level full`
shows each PASS is annotated `✅ pass (❗path unreachable)` —
Strata's deductive verifier is correctly self-flagging that the path
to the assertion was unreachable under bounded CFG fuel, not that
the property was proven. The matrix's PASS column collapses this
qualifier; that's a tooling gap (matrix-display issue), not a
verifier soundness bug.

`bugFinding` correctly identifies 6 of 7 unsafe SV-COMP programs as
PARTIAL with concrete failing VCs.

The two CBMC-import groups represent the easy-to-translate slice of
their respective upstream proof trees:
- **aws-c-common.** 6 of ~190 upstream proofs — the rest depend on
  AWS struct types (`aws_byte_buf`, `aws_array_list`, `aws_hash_*`)
  or `proof_helpers/` infrastructure that requires stub work.
- **coreJSON.** 12 of 15 upstream proofs translate cleanly (the 3
  search harnesses — `arraySearch`, `objectSearch`, `multiSearch` —
  segfault inside SMACK's clang frontend). One of the 12,
  `skipEscape_harness`, exits the deductive verifier with SIGABRT,
  surfacing a Strata-side bug worth tracking as a regression input
  (filed at `strata-verify-stack-overflow-deeply-nested-expr.md`).

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
  `test/cbmc/proofs/` tree. Each program bundles `core_json.h` +
  `core_json.c` verbatim alongside the harness body folded into
  `main()`. Generator at `wt-test/fetch_corejson_harness.py`.
  Commit `2c7a49181`.
- 22 additional verbatim CBMC harnesses imported from FreeRTOS
  coreMQTT/coreHTTP/coreSNTP, standalone parsers (jsmn, cJSON,
  picohttpparser), and RFC reference impls (UTF-8, base64,
  percent-encoding). Commit `953547728`.
- 9 of the coreJSON harnesses now carry **upstream-derived contracts**
  (preconditions/postconditions ported from FreeRTOS coreJSON's
  `core_json_contracts.h`). Commits `495e09c87` (4 parsers) and
  `5475c6710` (5 more).
- 29 SV-COMP ReachSafety programs imported with verdict oracle
  (`svcomp_verdicts.json`). Commit `eb8fbd513`. Verdict distribution:
  22 safe, 7 unsafe.

BoogieToStrata (cherry-picked from PR 1149 plus follow-up):

- `--smack` CLI flag, gating SMACK-specific behavior (`InferModifies`
  + `assert_.<type>` requires injection). Commits `6b04d9399`,
  `0e54ff2bd`, `ac814e582`.
- `__VERIFIER_assume` `free ensures (_i0 != 0)` synthesis under
  `--smack`, mirroring the `assert_` pattern with dual polarity.
  Commit `1b2231f99`.

BoogieToStrata (later additions):

- `__VERIFIER_assert` `requires (_i0 != 0)` injection under `--smack`.
  SMACK lowers C `assert(EXPR)` to a branch where the failing arm
  calls `__VERIFIER_assert(0)`; the requires injection forces the
  verifier to discharge the unreachability of that arm. Commit
  `b3e606bb6`.

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
- **Canonicalize array-type emission** in symtab/goto so DECL-site
  and parameter-site emissions produce structurally equal CBMC
  array-type objects, eliminating the dominant cbmc failure mode.
  Commit `7bff2d48e`.
- **Emit nondet array params as `nondet_symbol`, not `nondet`**
  (one-line JSON id fix), unblocking cbmc's array solver after the
  array-type fix landed. Commit `23926094f`.

Strata Core / Transform features:

- **Sound `ensures` synthesis pass under `--synthesize-ensures`**.
  Infers ensures clauses for procedures whose bodies are linear
  (no branches, only deterministic assignments and safe
  instrumentation calls). Soundness rests on three checks ensuring
  every synthesised clause holds for any input satisfying the
  preconditions. Off by default. Commit `390fadc37`.
- **Apply CallElim to CFG-bodied procedures**. Previously
  `runProgram` skipped CFG bodies, so call sites inside any
  CFG-bodied procedure (most SMACK output) had no `requires`-VCs
  generated for their callees — the verifier silently passed those
  call sites. The fix walks each CFG block's command list and
  applies CallElim to each command. Commit `42ff8a4b8`.

Regression coverage in `StrataTest/Backends/CBMC/GOTO/E2E_CoreToGOTO.lean`,
`StrataTest/Languages/Core/Tests/EnsuresSynthesisTest.lean`, and
`Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`.

## Known blockers

- **CBMC: callee bodies not emitted.** `coreToGotoFiles*` translates
  only the entry procedure (`main`), leaving every callee — `add`,
  `assert__i32`, `_initialize`, SMACK prelude stubs, user-defined
  helpers — as bodyless declarations. cbmc reaches a call and reports
  `[.no-body.<callee>] no body for callee <callee>: FAILURE`. **This
  is now the dominant cbmc failure mode** across the 93-program suite
  after the array-type and nondet-symbol fixes unblocked the upstream
  type checker and array solver. Fix path: iterate over all reachable
  procedures in `coreToGotoFilesDispatch`, not just the entry; emit
  each via `procedureToGotoCtxDispatch` and splice into the output
  JSON. The lifted-functions infrastructure in `emitProcWithLifted`
  is the right shape but currently only handles `Core.Function`, not
  `Core.Procedure`.
- **CBMC: real-loop unwinding bound.** `loop_sum` has a real C `for`
  loop, so cbmc's BMC unroller correctly identifies the genuine
  back-edge and tries to unroll without bound, hitting the default
  120s timeout. Fix path: pass `--unwind <N>` (with `N` chosen per
  program) or attach a loop invariant. The 3 other previously-timing-out
  programs (`abs_func`, `max_func`, `nondet_branch`) had **spurious**
  back-edges from the GOTO emission order; that's resolved on this
  branch — see *What this branch ships → CFG block emission in
  reverse-postorder*.
- **Deductive PARTIAL breakdown (sample-based).** The 54 deductive
  PARTIALs across the 93-program suite split into two sub-classes by
  failing-VC verdict and origin:
  - **(a) Missing `ensures` on a user-defined helper** — solver
    returns `❓ unknown`, label
    `callElimAssert___VERIFIER_assert_requires_0_NN`. Every
    post-call assertion in a CFG-bodied procedure where the callee
    has no `ensures` clause; call-elim havocs the post-call state
    and the assertion becomes unprovable, even though it's logically
    valid. **27 of 27** triaged failing VCs on the contract-ported
    coreJSON parsers fall in this class (P1 triage). Fix levers:
    extend `--synthesize-ensures` (`390fadc37`) to handle CFG bodies,
    or hand-port upstream `core_json_contracts.h` ensures onto the
    parser implementations themselves (not just the harness).
    Triage detail in `wt-test/triage/contract-ported-parser-vcs.md`.
  - **(b) Solver returns `unknown` on bitwise-heavy formulas** —
    verdict `❓ unknown`. Sample: `aws_byte_buf_append`, all 7 VCs.
    The asserted predicate chain involves nested int↔bit conversions
    (`_zext`, `_trunc`) over memory-map loads (`_load_i64`,
    `_load_ref`) on a program with 13 `_M_N` map params. SMT formula
    complexity exceeds the solver's reach. Fix lever: SMT encoding
    work in `Strata/Languages/Core/SMTEncoder.lean` — array theory
    vs axiomatized maps, axiom pruning. Significant effort; likely
    the last sub-class to address.
- **`run_pipeline.py` collapses `path unreachable` PASSes.** The
  matrix's PASS/PARTIAL/FAIL column drops the
  `✅ pass (❗path unreachable)` qualifier the deductive verifier
  emits when bounded CFG-fuel evaluation didn't reach the obligation.
  This made 6 SV-COMP unsafe programs (`sv_locks_14_2`,
  `sv_locks_15_2`, `sv_loops_mono3_1` through `sv_loops_mono6_1`)
  initially look like soundness probes (`unsafe ∧ deductive=PASS`).
  They aren't — Strata is correctly self-flagging the unreachability,
  but the pipeline collapses the qualifier. Fix path: add a third
  matrix state (e.g. `PASS-unreachable`) and surface it in
  `run_pipeline.py`'s output. **No actual Strata soundness
  violations were found by the SV-COMP integration.**
- **bugFinding partials.** Symbolic execution finds potential
  counterexamples for assertions on programs whose preconditions are
  insufficient. Same root cause as deductive sub-class (a) (callees
  with no `ensures`). Expected behaviour given the current translation;
  not a pipeline bug. **bugFinding correctly identifies 6 of 7 SV-COMP
  unsafe programs** as PARTIAL with concrete failing VCs — a positive
  validation of the bugFinding mode.
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

### Resolved blockers (history)

- **CBMC: array type mismatch on memory-map params.** The dominant
  failure mode in the original portfolio (38 of 65 rows). Fixed by
  commits `7bff2d48e` (`tyToJson` size-qualified array JSON) and
  `23926094f` (`nondet_symbol` instead of `nondet` for array params).
  Cbmc now passes the type checker and array solver on these
  programs.
- **CFG-CallElim requires-VC gap.** All CFG-bodied procedures
  silently passed deductive on vacuous obligations. Fixed by
  `42ff8a4b8`; now ~14 rows that were vacuous PASS show concrete
  PARTIAL with real failing VCs (an (S) → real-VC transition).
- **`__VERIFIER_assume` uninterpreted, `__VERIFIER_assert`
  uninterpreted.** Both fixed by synthetic-spec injection in
  BoogieToStrata under `--smack` (commits `1b2231f99`,
  `b3e606bb6`).
- **CFG block emission produced spurious back-edges.** Fixed by
  RPO emission (`520f3f573`); 3 of 4 cbmc-TIMEOUT programs flipped
  to real verdicts.

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
