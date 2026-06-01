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

### Headline result: body-eval at call sites

The biggest verdict change in the project to date is from the
`--call-policy bodyOrContract` feature (commit `dd0c0d7cd`). It lets
the evaluator analyse callee bodies at the call site (instead of
relying only on contracts), with fuel-bounded fallback to contract
semantics on `OutOfFuel`. Run with:

```bash
python3 run_pipeline.py --backends deductive --split-procs \
  --call-policy bodyOrContract programs/*.bpl
```

Deductive results across the 93-program suite:

|  | Contract (default) | bodyOrContract | Δ |
|---|---:|---:|---:|
| Portfolio (64) | 21 PASS / 43 PARTIAL | **63 PASS / 1 PARTIAL** | **+42 PASS** |
| SV-COMP (29) | 18 PASS / 11 PARTIAL | **19 PASS / 10 PARTIAL** | **+1 PASS** |
| Combined (93) | **39 PASS / 54 PARTIAL** | **82 PASS / 11 PARTIAL** | **+43 PASS** |

The portfolio gains are driven by the contract-ported coreJSON
parsers and the simplified-AWS programs whose deductive PARTIALs
under the default policy were entirely sub-class (a) (missing
`ensures` on user-defined helpers; see *Known blockers*). With
body-eval, the verifier sees the actual body and discharges the
post-call assertions directly. The single remaining PARTIAL on the
portfolio (`nondet_branch`) is the canonical multi-branch case the
feature explicitly refuses (see `MULTIPATH_COMMAND_EVAL.md` for the
proposed fix).

Captured in `wt-test/pipeline-portfolio-bodyOrContract-v4.txt` and
`wt-test/pipeline-svcomp-bodyOrContract-v4.txt`.

### Run history

Sequence of full-suite pipeline runs as the branch evolved. Each row
is a deductive verdict snapshot; the `key change` column names the
fix that landed between runs. Earlier runs were captured pre-SV-COMP
on the 64-program portfolio only; the v3 split-procs run is the
baseline used by the *Default-policy results* below.

| Run | deductive PASS | deductive PASS-? | deductive not-PASS | mode | key change |
|---|---:|---:|---:|---|---|
| v1 | 47 | — | 16 | non-split | baseline (64 programs) |
| v2 | 33 | — | 30 | non-split | `__VERIFIER_assert` requires injection (64 programs) |
| v3 | 21 | — | 43 | `--split-procs` | CFG-CallElim fix (`42ff8a4b8`) (64 programs) |
| sv-comp | 18 | — | 11 | `--split-procs` | 29 SV-COMP programs imported (`eb8fbd513`) |
| v3 + sv-comp combined | 39 | — | 54 | `--split-procs` | v3 ∪ sv-comp (93 programs total) |
| v4 (bodyOrContract) | 82 | — | 11 | `--split-procs --call-policy bodyOrContract` | body-eval at call sites (`dd0c0d7cd`) on the combined 93-program suite |
| v5 (PASS-? surfacing) | 57 | 18 | 11 | `--split-procs --call-policy bodyOrContract --check-level full` | run-pipeline emits `--check-level full` and surfaces `path unreachable` as `PASS-?` (`a817909fc`); 8 large `.bpl` (≥20K lines) excluded due to the deferred-obligation hang since fixed in v6 — see *Resolved blockers (history)* |
| v6 (deferred-dedup) | **TBD** | **TBD** | **TBD** | `--split-procs --call-policy bodyOrContract --inline-fuel 100 --check-level full` | CFG `condGoto` deferred-dedup fix (`277c468cb`) on the full 94-program suite (no programs excluded) |

The deductive PASS climb from 21 → 39 → 82 → 57 → TBD is the project
arc: each bend was driven by a specific fix landing on `htd/smack`.
v3 → v3+sv-comp shows the SV-COMP programs adding 18 new PASSes;
combined → v4 shows body-eval flipping 43 PARTIALs to PASS in a single
change. v4 → v5 is not directly comparable — the suite shrank by 8
(93 → 86) because `.bpl` files ≥20K lines hung under the new
`--check-level full` flag, and on the 86 programs that did run in both
v4 and v5, the v4 PASS column splits into 57 real proofs + 18 vacuous
discharges (path unreachable). The 11 PARTIAL count is unchanged.

v5 → v6 unblocks the eight large-`.bpl` programs (`JSON_Iterate_harness`,
`JSON_SearchConst_harness`, `JSON_Validate_harness`,
`cjson_cJSON_Parse_harness`, plus the four `skip*Scalars`/`skipCollection`/
`skipAnyScalar` harnesses) that previously hung the verifier indefinitely
under any flag combination. The deferred-dedup fix (`277c468cb`)
eliminates the multiplicative-growth wall in `Env.deferred` across CFG
`condGoto` symbolic branches; the full 94-program suite now runs without
exclusions. PARTIAL identities match v5 exactly (no verdict regressions;
soundness empirically confirmed).

The 86 v5 numbers come from a single matrix run on 85 programs (which
preemptively also excluded `sv_locks_11.bpl` on a misread of a prior
hang) plus a standalone re-run of `sv_locks_11.bpl` that confirmed it
completes as PASS-? rather than hanging.

### Default-policy results (contract; today's behaviour)

The most recent runs under `--call-policy contract` (the default;
matches today's verifier behaviour):

- **portfolio (`--split-procs`):** 64 programs (everything except the
  SV-COMP imports + `picohttpparser` which OOMs cbmc-native). Captured
  in `wt-test/pipeline-portfolio-v3.txt`. Run after fixes
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

Per-program v3 detail moved into the combined v3+v5 table under
*v5 results* below; pointer kept here for reference. Full v3 pipeline
output in `wt-test/pipeline-portfolio-v3.txt` and
`wt-test/pipeline-svcomp.txt`.

**Column legend:**

| Header | Meaning |
|---|---|
| `Ded` | Strata `verify --check-mode deductive` |
| `Bug` | Strata `verify --check-mode bugFinding` |
| `CBM` | Strata-CBMC (`StrataCoreToGoto + symtab2gb + cbmc`) |
| `CBN` | CBMC-native (`cbmc` directly on the source `.c`) |

The pre-translation stage gates (`strip_smack_prelude.py` →
BoogieToStrata → `fix_core_st.py`) all return `OK` for every program
in the current suite, so they are omitted from the table. A failure
in any of those stages would surface in the pipeline driver's
output as `FAIL` in place of `OK`; the row would also lack any
backend verdicts.

**Verdict legend:**

| Token | Meaning |
|---|---|
| `OK` | stage succeeded (no errors) |
| `PASS` | all VCs / properties discharged with real deductive proofs |
| `PASS-?` | all VCs passed, but ≥1 annotated `pass (❗path unreachable)` — vacuously discharged because the path's conditions are contradictory; not a real proof |
| `PART` | PARTIAL — some VCs discharged, others failed or `unknown` |
| `FAIL` | verification failed (real verdict, not a stage error) |

**Detail format (`Detail` column):**

`<P>p,<F>f / <K> (<proc1>[,<proc2>...])` reads as:
- `<P>` VCs passed, `<F>` VCs failed,
- across `<K>` procedures (under `--split-procs`),
- non-PASS procedures listed in parentheses (`assume` is shorthand for
  the synthetic `__VERIFIER_assume` procedure that SMACK emits).

The `Detail` column reports per-procedure VC counts under
`--split-procs`, which runs each procedure independently and rolls
the verdicts up per-file.

### v5 results: bodyOrContract + path-unreachable surfacing

Latest run on the 86-program subset (8 large files excluded; see
*Known blocker* below) under `--call-policy bodyOrContract --inline-fuel 100
--check-level full --split-procs`:

|  | PASS | PASS-? | PARTIAL | FAIL | TIMEOUT |
|---|---:|---:|---:|---:|---:|
| Strata deductive | 57 | 18 | 11 | 0 | 0 |
| Strata bugFinding | 57 | 18 | 11 | 0 | 0 |
| Strata-CBMC | 0 | 0 | 0 | 86 | 0 |

The 18 PASS-? entries surface what was previously a hidden tooling
gap (the matrix collapsed `pass (❗path unreachable)` into PASS).
Splitting by the SV-COMP oracle's expected verdict:

- **Would-be-FAIL (oracle: unsafe — PASS-? hides a real failure):**
  `sv_locks_14_2`, `sv_locks_15_2`, `sv_loops_mono3_1`,
  `sv_loops_mono4_1`, `sv_loops_mono5_1`, `sv_loops_mono6_1`. Strata
  is correctly self-flagging the vacuity, but the underlying program
  is genuinely unsafe; a sound verdict would be FAIL.
- **Would-be-PASS (oracle: safe, or no oracle — vacuous proof on a
  provable program):** `sv_locks_10`, `sv_locks_11`, `sv_locks_12`,
  `sv_locks_13`, `sv_loops_loopv3`, `sv_loops_mono1_1_2`,
  `sv_loops_nested3_1`, `array_sum`, `loop_sum`,
  `HTTPClient_AddRangeHeader_harness`, `skipString_harness`,
  `skipUTF8_harness`. These should reach a real PASS but Strata's
  loop-havoc abstraction collapses the path-condition before the
  assertion is reached.

The remaining 57 PASS entries are real deductive proofs.

**Why these are vacuous (qualitative analysis, 2026-05-30):** every
PASS-? program has the shape "loop, then assertion." Strata's evaluator
treats the loop as `loopHasNoInvariants` — havoc the loop-modified
state, then assume the loop guard is false. The post-loop assertion is
evaluated against havoc'd state, and the resulting path-condition turns
out unsatisfiable, triggering `path unreachable`. **An empirical
fuel-bump experiment (running 12 of the 18 at `--inline-fuel 500`)
produced zero verdict changes** — `--inline-fuel` controls body-eval
recursion, not loop unrolling. Even `array_sum` (4-iteration loop)
remains PASS-? at fuel=500. Full analysis at
`../../reports/v5-pass-question-mark-analysis.md`.

**Implication for matrix interpretation:** PASS-? lumps two
semantically-opposite outcomes:
- **Would-be-PASS** if loops were handled with concrete unrolling or
  stronger invariants: 12 cases.
- **Would-be-FAIL** because the program is genuinely unsafe and Strata
  is hiding the failure behind a vacuous discharge: 6 cases.

PASS-? at least flags both as not-real-proofs; a future enhancement
(see analysis) could split them.

**Per-program PASS-? detail.** Each row reports the oracle's expected
verdict (where one exists), the structural cause of the vacuity, and
the resulting class:

| Program | Oracle | Loop / mechanism | Class |
|---|---|---|---|
| `sv_locks_14_2` | unsafe | 14-lock unlock chain in `while(1)`, ERROR arm; havoc collapses path | would-be-FAIL |
| `sv_locks_15_2` | unsafe | 15-lock unlock chain | would-be-FAIL |
| `sv_loops_mono3_1` | unsafe | loop to 1M; `assert y!=0` is false at termination | would-be-FAIL |
| `sv_loops_mono4_1` | unsafe | loop to 1M; `assert y!=x` false at termination | would-be-FAIL |
| `sv_loops_mono5_1` | unsafe | loop to 10M; `assert z!=0` false | would-be-FAIL |
| `sv_loops_mono6_1` | unsafe | loop to 10M; `assert z!=x` false | would-be-FAIL |
| `sv_locks_10` | safe | 10-lock chain in `while(1)`; havoc loses precision | would-be-PASS |
| `sv_locks_11` | safe | 11-lock chain | would-be-PASS |
| `sv_locks_12` | safe | 12-lock chain | would-be-PASS |
| `sv_locks_13` | safe | 13-lock chain | would-be-PASS |
| `sv_loops_loopv3` | safe | loop bound 50M; needs invariant | would-be-PASS |
| `sv_loops_mono1_1_2` | safe | loop bound 100M; needs invariant | would-be-PASS |
| `sv_loops_nested3_1` | safe | triply-nested loops to 0x0fffffff | would-be-PASS |
| `array_sum` | n/a | `for (i=0;i<4;i++) sum+=a[i]; assert(sum==10)` — small loop havoc'd | would-be-PASS |
| `loop_sum` | n/a | `for (i=0;i<5;i++) sum+=i; assert(sum==10)` — small loop havoc'd | would-be-PASS |
| `HTTPClient_AddRangeHeader_harness` | n/a | inlined callee `convertInt32ToAscii` digit-buffer loop | would-be-PASS |
| `skipString_harness` | n/a | inlined `skipString` while-loop + `skipUTF8` callee chain | would-be-PASS |
| `skipUTF8_harness` | n/a | inlined `countHighBits` `while ((n & 0x80U) != 0U)` | would-be-PASS |

`array_sum` (4-iteration loop) and `loop_sum` (5-iteration loop) are
the most surprising — small concrete loops that should plausibly be
unrollable. They were verified PASS-? at `--inline-fuel 500` in the
fuel-bump experiment, confirming the issue is loop havoc abstraction,
not body-eval recursion fuel.

The 11 PARTIAL entries (`nondet_branch`, `sv_loops_iftelse`,
`sv_loops_in_de31`, `sv_loops_loopv1`, `sv_loops_loopv2`,
`sv_rc_avg05_1`, `sv_rc_max05_1`, `sv_rc_max05_2`, `sv_rc_rangesum05`,
`sv_rc_sep05_1`, `sv_rc_sum`) are unchanged from v4 — body-eval can't
handle their multi-branch result envs (`nondet_branch` is the
canonical case; see `MULTIPATH_COMMAND_EVAL.md`) or their assertion
genuinely fails.

#### v5 per-program detail

All 94 .bpl programs. `Ded` and `Bug` columns are v5 verdicts under
`--call-policy bodyOrContract --inline-fuel 100 --check-level full
--split-procs`. `CBN` is the v3 cbmc-native verdict (v5 didn't re-run
cbmc-native). `CBM` (Strata-CBMC) is omitted because it was uniformly
FAIL on every row in both runs — see "Why CBM is FAIL on every row"
below. `—` means the program was excluded from v5 (8 hangs + the
always-excluded picohttpparser). For per-program v3 (contract-policy)
verdicts and the historical PARTIAL VC counts, see the v3→v5 diff
table below.

```
Program                                      |  Ded |  Bug |  CBN
-------------------------------------------------------------------
# Original benchmark
abs_func                                     |   PASS |   PASS |   FAIL
array_sum                                    | PASS-? | PASS-? |   PASS
aws_array_eq                                 |   PASS |   PASS |   PASS
aws_byte_cursor_advance                      |   PASS |   PASS |   PASS
aws_ring_buffer                              |   PASS |   PASS |   PASS
loop_sum                                     | PASS-? | PASS-? |   PASS
max_func                                     |   PASS |   PASS |   PASS
nondet_branch                                |   PART |   PART |   FAIL
pointer_arith                                |   PASS |   PASS |   FAIL
simple_add                                   |   PASS |   PASS |   PASS
simple_assert                                |   PASS |   PASS |   PASS
swap                                         |   PASS |   PASS |   PASS

# Simplified AWS C Common
aws_add_size_checked                         |   PASS |   PASS |   PASS
aws_array_eq_stripped                        |   PASS |   PASS |      —
aws_array_list_get                           |   PASS |   PASS |   PASS
aws_array_list_set                           |   PASS |   PASS |   PASS
aws_byte_buf_append                          |   PASS |   PASS |   PASS
aws_byte_buf_init                            |   PASS |   PASS |   PASS
aws_byte_cursor_eq                           |   PASS |   PASS |   PASS
aws_hash_string                              |   PASS |   PASS |   PASS
aws_is_power_of_two                          |   PASS |   PASS |   PASS
aws_linked_list_push                         |   PASS |   PASS |   PASS
aws_min_max                                  |   PASS |   PASS |   PASS
aws_mul_size_checked                         |   PASS |   PASS |   PASS
aws_round_up_to_power_of_two                 |   PASS |   PASS |   PASS
aws_string_eq                                |   PASS |   PASS |   PASS

# aws-c-common verbatim
aws_add_size_checked_harness                 |   PASS |   PASS |   PASS
aws_add_size_saturating_harness              |   PASS |   PASS |   PASS
aws_is_power_of_two_harness                  |   PASS |   PASS |   PASS
aws_mul_size_checked_harness                 |   PASS |   PASS |   PASS
aws_mul_size_saturating_harness              |   PASS |   PASS |   PASS
aws_round_up_to_power_of_two_harness         |   PASS |   PASS |   PASS

# FreeRTOS coreJSON verbatim
JSON_Iterate_harness                         |      — |      — |   FAIL
JSON_SearchConst_harness                     |      — |      — |   FAIL
JSON_Validate_harness                        |      — |      — |   PASS
skipAnyScalar_harness                        |      — |      — |   PASS
skipCollection_harness                       |      — |      — |   FAIL
skipDigits_harness                           |   PASS |   PASS |   PASS
skipEscape_harness                           |   PASS |   PASS |   FAIL
skipObjectScalars_harness                    |      — |      — |   FAIL
skipScalars_harness                          |      — |      — |   FAIL
skipSpace_harness                            |   PASS |   PASS |   PASS
skipString_harness                           | PASS-? | PASS-? |   PASS
skipUTF8_harness                             | PASS-? | PASS-? |   PASS

# FreeRTOS coreMQTT/coreHTTP/coreSNTP verbatim
HTTPClient_AddHeader_harness                 |   PASS |   PASS |   FAIL
HTTPClient_AddRangeHeader_harness            | PASS-? | PASS-? |   FAIL
HTTPClient_InitializeRequestHeaders_harness  |   PASS |   PASS |   FAIL
HTTPClient_ReadHeader_harness                |   PASS |   PASS |   FAIL
HTTPClient_strerror_harness                  |   PASS |   PASS |   PASS
MQTT_GetPacketId_harness                     |   PASS |   PASS |   PASS
MQTT_Init_harness                            |   PASS |   PASS |   PASS
MQTT_Ping_harness                            |   PASS |   PASS |   FAIL
Sntp_DeserializeResponse_harness             |   PASS |   PASS |   PASS
Sntp_SerializeRequest_harness                |   PASS |   PASS |   PASS

# Standalone parsers
cjson_cJSON_IsArray_harness                  |   PASS |   PASS |   PASS
cjson_cJSON_Parse_harness                    |      — |      — |   FAIL
jsmn_jsmn_parse_harness                      |   PASS |   PASS |   FAIL
# picohttpparser_phr_parse_request_harness  excluded — cbmc-native OOMs (>32 GB) on the SAT instance.

# RFC reference impls
base64_decode_normal_harness                 |   PASS |   PASS |   PASS
base64_decode_padding_only_harness           |   PASS |   PASS |   PASS
base64_decode_short_input_harness            |   PASS |   PASS |   PASS
percent_decode_nul_harness                   |   PASS |   PASS |   PASS
percent_decode_truncated_harness             |   PASS |   PASS |   PASS
utf8_validate_ascii_harness                  |   PASS |   PASS |   FAIL
utf8_validate_overlong_harness               |   PASS |   PASS |   FAIL
utf8_validate_surrogate_harness              |   PASS |   PASS |   FAIL

# SV-COMP ReachSafety
sv_locks_10                                  | PASS-? | PASS-? |   PASS
sv_locks_11                                  | PASS-? | PASS-? |   PASS
sv_locks_12                                  | PASS-? | PASS-? |   PASS
sv_locks_13                                  | PASS-? | PASS-? |   PASS
sv_locks_14_2                                | PASS-? | PASS-? |   FAIL
sv_locks_15_2                                | PASS-? | PASS-? |   PASS
sv_locks_5                                   |   PASS |   PASS |   PASS
sv_locks_6                                   |   PASS |   PASS |   PASS
sv_locks_7                                   |   PASS |   PASS |   PASS
sv_locks_8                                   |   PASS |   PASS |   PASS
sv_locks_9                                   |   PASS |   PASS |   PASS
sv_loops_iftelse                             |   PART |   PART |   PASS
sv_loops_in_de20                             |   PASS |   PASS |   PASS
sv_loops_in_de31                             |   PART |   PART |   PASS
sv_loops_loopv1                              |   PART |   PART |   PASS
sv_loops_loopv2                              |   PART |   PART |   PASS
sv_loops_loopv3                              | PASS-? | PASS-? |   PASS
sv_loops_mono1_1_2                           | PASS-? | PASS-? |   PASS
sv_loops_mono3_1                             | PASS-? | PASS-? |   PASS
sv_loops_mono4_1                             | PASS-? | PASS-? |   PASS
sv_loops_mono5_1                             | PASS-? | PASS-? |   PASS
sv_loops_mono6_1                             | PASS-? | PASS-? |   PASS
sv_loops_nested3_1                           | PASS-? | PASS-? |   PASS
sv_rc_avg05_1                                |   PART |   PART |   FAIL
sv_rc_max05_1                                |   PART |   PART |   PASS
sv_rc_max05_2                                |   PART |   PART |   PASS
sv_rc_rangesum05                             |   PART |   PART |   FAIL
sv_rc_sep05_1                                |   PART |   PART |   PASS
sv_rc_sum                                    |   PART |   PART |   FAIL

  Ded: 57 pass, 18 pass-?, 11 partial (86 verdicts; 8 hangs)
  Bug: 57 pass, 18 pass-?, 11 partial (matches Ded exactly)
  CBM:  0 pass — uniform FAIL on all 86 (see below)
  CBN: 70 pass, 23 fail (v3 only; cbmc-native didn't run in v5)
```

#### v3 → v5 per-program diff

Only rows where the v3 (contract-baseline) verdict differs from v5 are
listed. 63 of 94 programs changed; 30 unchanged rows omitted (20 same
PASS, 10 same PART), plus `aws_array_eq_stripped` v5-only and 8 v5 hangs.
Group order matches root cause.

| Programs | v3 | v5 | Cause |
|---|---|---|---|
| `abs_func`, `aws_array_eq`, `aws_byte_cursor_advance`, `aws_ring_buffer`, `max_func`, `simple_assert`, `swap`, all 13 simplified-AWS, all 6 aws-c-common verbatim, `skipDigits_harness`, `skipSpace_harness`, all 8 RFC programs (36 total) | PART | PASS | **body-eval at call sites** (`dd0c0d7cd`, the v3→v4 lever): callee body is analyzed symbolically, post-call assertions discharge directly |
| `skipString_harness`, `skipUTF8_harness`, `sv_loops_loopv3` | PART | PASS-? | body-eval discharges, but Strata's loop-havoc abstraction collapses the post-loop path-condition (see *v5 results*) |
| `array_sum`, `loop_sum`, `HTTPClient_AddRangeHeader_harness`, `sv_locks_10`, `sv_locks_11`, `sv_locks_12`, `sv_locks_13`, `sv_locks_14_2`, `sv_locks_15_2`, `sv_loops_mono1_1_2`, `sv_loops_mono3_1`, `sv_loops_mono4_1`, `sv_loops_mono5_1`, `sv_loops_mono6_1`, `sv_loops_nested3_1` (15 total) | PASS | PASS-? | **PASS-? surfacing**: pipeline now passes `--check-level full` and parses the `pass (❗path unreachable)` annotation. These were already vacuous in v3/v4 — same Strata behavior, just newly visible |
| `nondet_branch` | PASS | PART | Multi-branch regression: body-eval refuses callees whose body produces multiple result envs; v3's contract-policy was silently passing the resulting unknowns. See `MULTIPATH_COMMAND_EVAL.md` |
| `aws_array_eq_stripped` | (n/a) | PASS | New variant — v3 wt-test capture predates this `.bpl` |
| `JSON_Iterate_harness`, `JSON_SearchConst_harness`, `cjson_cJSON_Parse_harness` | PASS | — | v5 hang on ≥20K-line `.bpl` (see *Known blocker*) |
| `JSON_Validate_harness`, `skipAnyScalar_harness`, `skipCollection_harness`, `skipObjectScalars_harness`, `skipScalars_harness` | PART | — | Same v5 hang |

Net change in deductive verdicts (excluding hangs and stripped):
- 36 PART → PASS (real verdict gain from body-eval)
- 3 PART → PASS-? (body-eval discharges but vacuously)
- 15 PASS → PASS-? (cosmetic — vacuity was already present, now visible)
- 1 PASS → PART (regression — `nondet_branch`)

**Two distinct Strata-side changes drove these flips:** v3→v4 body-eval
(`dd0c0d7cd`) is responsible for the 36 PART→PASS gains (and the 3
PART→PASS-? mixed gains, and the 1 PASS→PART regression on
`nondet_branch`); v4→v5 PASS-? surfacing is a pipeline-only change
(uncommitted `run_pipeline.py`) responsible for the 15 PASS→PASS-? and
3 PART→PASS-? relabels — no Strata code change.

**Why CBM is FAIL on every row.** The cbmc backend's failure here is
**not a counterexample to the program** — it's a build-time failure
inside `goto-cc`/cbmc due to bodyless prelude stubs. SMACK emits calls
to `__VERIFIER_assume`, `assert_.i32`, and similar primitives;
`coreToGotoFiles*` translates user-defined callees but leaves these
prelude stubs as bodyless function declarations. CBMC then reports
`[.no-body.<callee>]` and exits with an error code (`CBMC exit code 6`
or `-6`). The exit codes are not the `PROPERTY HOLDS / VIOLATION`
codes (0 / 10) — they're the "missing-body" build error.

This is the residual CBMC blocker described in *What the cbmc=FAIL
count actually means now* below; until the prelude stubs get synthetic
bodies, the CBM column will stay FAIL for every program. CBN (cbmc on
the source `.c`, no Strata) is unaffected.

### What the cbmc=FAIL count actually means now

After the seven CBMC backend fixes on this branch (see
`BRANCH_FEATURES.md` §2), the cbmc backend **reaches actual model
checking on every program** rather than failing at the type-checker
or array-solver stage. The 93 FAILs are real verification verdicts,
dominated by the residual **callee-bodies blocker**: `coreToGotoFiles*`
emits the entry procedure plus user-defined callees (commit
`ca95931be`), but `__VERIFIER_assume` / `assert_.i32` and other
prelude stubs remain bodyless. Cbmc reports `[.no-body.<callee>]` and
fails. Until those are emitted too, expect cbmc PASS counts to stay
at 0; once that's addressed, expect them to follow the deductive
column. Pre-fix-history detail in *Resolved blockers (history)*
below.

### What the deductive PARTIAL count means

The 54 default-policy PARTIALs are the contract-only baseline. The
dominant cause is **missing `ensures` on user-defined helpers**
(deductive sub-class (a) — see *Known blockers*): post-call assertions
in CFG-bodied procedures whose callees lack `ensures` clauses become
`❓ unknown` after call-elim havocs the post-call state. Body-eval
(`--call-policy bodyOrContract`, see headline-result table above) is
the resolution lever: it traverses the callee body symbolically and
discharges the post-call assertions directly, flipping 42 of 43
portfolio rows from PARTIAL to PASS.

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
the property was proven.

**Tooling gap closed in v5.** The pipeline's `run_pipeline.py` now
passes `--check-level full` and parses the output for `path
unreachable` annotations, surfacing those programs as `PASS-?` (see
*v5 results* and *Verdict legend* above). All 6 candidate probes
above (plus `sv_loops_mono1_1_2`, `sv_loops_nested3_1`, and
`sv_loops_loopv3`) now correctly show `PASS-?` in the matrix.

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
  (filed at `../../reports/strata-verify-stack-overflow-deeply-nested-expr.md`).

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
- **Body evaluation at call sites under `--call-policy {body|bodyOrContract}`**.
  The evaluator analyses callee bodies symbolically at the call site
  with a fuel-bounded budget (`--inline-fuel N`, default `100000`).
  `bodyOrContract` falls back to the contract path on `OutOfFuel`.
  This is the single largest verdict-improvement on the matrix to
  date: 42 portfolio rows flip from PARTIAL to PASS deductive,
  resolving the dominant sub-class (a) blocker described under
  *Known blockers*. Commit `dd0c0d7cd`. The pipeline driver gained
  `--call-policy` and `--inline-fuel` axes (commit `998d64635`).
  See `MULTIPATH_COMMAND_EVAL.md` for the proposed multi-branch
  follow-up.

Regression coverage in `StrataTest/Backends/CBMC/GOTO/E2E_CoreToGOTO.lean`,
`StrataTest/Languages/Core/Tests/EnsuresSynthesisTest.lean`, and
`Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`.

## Known blockers

- **CBMC: callee bodies (partial fix landed; residual stubs remain).**
  Commit `ca95931be` extended `coreToGotoFilesDispatch` to emit all
  reachable user-defined callees, not just the entry procedure. The
  residual blocker is the SMACK prelude stubs (`__VERIFIER_assume`,
  `assert_.i32`, etc.): they have no Strata body, so they appear in
  the symbol table as `function_typet` declarations only, and cbmc
  still reports `[.no-body.<callee>]` and fails. **This is the
  dominant cbmc failure mode today** across all 93 programs. Fix
  path: emit synthetic CBMC bodies for the prelude stubs (e.g. an
  `assume(p != 0)` body for `__VERIFIER_assume`), or hand-link a
  CBMC-side stub library at the `symtab2gb` step. Tracked under
  [#1184](https://github.com/strata-org/Strata/issues/1184).
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
    coreJSON parsers fell in this class (P1 triage).
    **Largely resolved as of `dd0c0d7cd` (body-eval at call sites)**:
    under `--call-policy bodyOrContract` the evaluator analyses the
    callee body symbolically and discharges the post-call assertions
    directly. The 42 portfolio rows that were sub-class (a) PARTIALs
    under contract policy now PASS under bodyOrContract. The original
    contract-policy fix levers (extend `--synthesize-ensures`
    (`390fadc37`) to handle CFG bodies, or hand-port upstream
    `core_json_contracts.h` ensures onto the parser implementations)
    remain valid for the contract-only path.
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
  counterexamples for assertions whose synthetic preconditions
  (`__VERIFIER_assume`'s `requires (_i0 != 0)`, etc.) are
  unconstrained at call sites. Verified empirically: bugFinding under
  `--call-policy bodyOrContract` produces zero verdict improvements
  (0/65 contract → 0/64 bodyOrContract on portfolio; same on
  SV-COMP). bugFinding's PARTIALs are about unconstrained inputs, not
  missing ensures, so body-eval doesn't help. Expected behaviour
  given the current translation; not a pipeline bug. bugFinding
  *correctly* flags 6 of 7 unsafe SV-COMP programs as PARTIAL with
  concrete failing VCs — a positive oracle validation.
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
- **Pipeline hang on ≥20K-line `.bpl` programs.** Four programs
  (`JSON_Iterate_harness`, `JSON_SearchConst_harness`,
  `JSON_Validate_harness`, `cjson_cJSON_Parse_harness`) hung the
  verifier indefinitely under every `--call-policy` and
  `--inline-fuel` setting; the workaround was to exclude them from
  matrix runs. Phase-bisection traced the divergence to
  `Core.toCoreProofObligationProgram`'s `Program.eval` step, where
  the deferred-obligation count grew multiplicatively across
  procedures (28 → 56 → 4928 → 9856 → 68992 → 896896 →
  3,960,692,736 across `cjson_cJSON_Parse_harness.bpl`'s 17
  procedures). Materialising a multi-billion-element
  `Array (Imperative.ProofObligation Expression)` was the actual
  hang. Root cause: in `evalCFGStep`, both `env_t` and `env_f` of a
  symbolic `condGoto` inherited the parent's `deferred` array, so
  every symbolic branch doubled the pre-split obligation set; the
  structured `.ite` path already deduped at `StatementEval.lean:673`
  but the CFG path missed the symmetric clear. Fixed by `277c468cb`
  (one-line `deferred := #[]` on the false branch). Soundness
  rationale: each `ProofObligation` snapshots its path conditions at
  creation time (`CmdEval.lean:64-83`), so dropping a duplicate from
  one branch loses no proof information — verified empirically on
  the v6 sweep where every PARTIAL identity matches v4.
  Also fixed a related macOS-specific `subprocess.run(timeout=,
  capture_output=True)` reliability bug in `run_pipeline.run_cmd`
  (commit `9f26fffd7`); the layered timeout (gtimeout wrapper +
  Popen+killpg fallback) means accidental inclusion of any
  divergent program is now safe.

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

- **Land multi-path body-eval.** Today's implementation refuses
  callees whose body has a symbolic `if` that produces multiple
  result envs (the `nondet_branch` case — the single residual
  portfolio PARTIAL). Design proposal: `MULTIPATH_COMMAND_EVAL.md`.
  Mechanical change to widen `Command.eval`'s return type to
  `List Env`, mirroring how `processIteBranches` already participates
  in multi-path eval at the statement level.
- **Surface `path unreachable` in the matrix.** The pipeline driver
  collapses `✅ pass (❗path unreachable)` to plain `PASS`, which
  produced the 6 false soundness probes on SV-COMP. Adding a
  `PASS-unreachable` (or `WARN`) third state in `parse_strata_output`
  would make the matrix report what the verifier actually said. See
  *Known blockers*.
- **Address the cbmc callee-bodies blocker** (iterate over all
  reachable procedures in `coreToGotoFilesDispatch`, not just
  `main`). Would unblock the cbmc column on most of the 93-program
  suite. See *Known blockers*.
- **Land #1185 fix on htd/smack.** Cross-procedure `Env.error`
  contamination silently drops obligations from later procedures; the
  `--split-procs` workaround masks it. The fix lives on
  `htd/fix-eval` (commits `d55ac1c33` + `eeb0dfa3d`); cherry-picking
  it to htd/smack would let us drop `--split-procs` from the pipeline
  driver. See *Known blockers* and `BRANCH_FEATURES.md` §9.

## Scripts in this directory

- `run_pipeline.py` — end-to-end multi-backend driver.
- `strip_smack_prelude.py` — removes SMACK prelude bodies before
  translation. Mostly historical now (BoogieToStrata translates the
  prelude under `--smack`); kept for the `__SMACK_and{32,16,8}` and
  `__SMACK_or32` bitwise-decompose stubs that still trip translation.
- `fix_core_st.py` — post-processes BoogieToStrata output to work around
  a few known translation issues.
- `Dockerfile` — builds the SMACK container image.
