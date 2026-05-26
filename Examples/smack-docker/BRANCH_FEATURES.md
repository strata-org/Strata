# `htd/smack` branch features vs `origin/main`

This document enumerates what the `htd/smack` branch carries that
`origin/main` does not, with at least one concrete example per
feature group. The branch is 156 commits ahead of `origin/main`;
this document focuses on the user-visible additions, not the merges
or refactors that are bookkeeping.

| Group | Item | Section |
|---|---|---|
| 1 | Pipeline infrastructure (`Examples/smack-docker/`) | [§1](#1-pipeline-infrastructure) |
| 2 | Strata CBMC backend fixes (`Strata/Backends/CBMC/GOTO/`) | [§2](#2-strata-cbmc-backend-fixes) |
| 3 | BoogieToStrata translator (`Tools/BoogieToStrata/`) | [§3](#3-boogietostrata-translator-features) |
| 4 | Benchmark suite (`Examples/smack-docker/programs/`) | [§4](#4-benchmark-suite-65-programs) |
| 5 | Cross-validation infrastructure (`tools/`, `CROSS_VALIDATION.md`) | [§5](#5-cross-validation-infrastructure) |
| 6 | Documentation (`README.md`, `STATUS.md`) | [§6](#6-documentation) |
| 7 | Regression coverage (`StrataTest/`) | [§7](#7-regression-coverage) |

---

## 1. Pipeline infrastructure

The `Examples/smack-docker/` directory is entirely new on this
branch — `origin/main` has nothing comparable. It implements the
end-to-end C → SMACK → BoogieToStrata → Strata Core → backends flow.

### Components

- **`run_pipeline.py`** — multi-backend driver, four backends:
  `deductive`, `bugFinding`, `cbmc` (Strata-lowered), `cbmc-native`
  (CBMC invoked directly on the source `.c` as a ground-truth
  control). `--split-procs` mode runs each procedure independently
  to sidestep cross-procedure error contamination
  ([issue #1185](https://github.com/strata-org/Strata/issues/1185)).
- **`strip_smack_prelude.py`** — preprocesses SMACK output by
  stripping prelude implementations BoogieToStrata can't translate
  (the bitwise-decompose `__SMACK_and{32,16,8}` and `__SMACK_or32`
  stubs).
- **`fix_core_st.py`** — post-processes BoogieToStrata output to
  work around translation issues.
- **`cbmc_native_flags.json`** — per-program flag overrides for
  `cbmc-native`. Default: `--bounds-check --pointer-check
  --unwind 10 --no-unwinding-assertions`. Programs with real loops
  (e.g. `loop_sum`) get bigger unwind bounds.
- **`programs/smack.h`** — minimal stub header so `cbmc-native` can
  preprocess harnesses that `#include "smack.h"`. Each
  `__VERIFIER_*` declaration is guarded by `#ifndef` so command-line
  `-D` macro overrides take precedence.
- **`Dockerfile`** — Finch-compatible (`--platform linux/amd64`)
  builder for the SMACK image.

### Example

```bash
cd Examples/smack-docker
finch build --platform linux/amd64 -t smack .
python3 run_pipeline.py --backends deductive,bugFinding,cbmc,cbmc-native
```

Produces a per-program verdict table:

```
Program       |  Strip |    B2S |    Fix |  deductive | bugFinding |    cbmc | cbmc-native
-------------------------------------------------------------------------------------------
simple_add    |     OK |     OK |     OK |       PASS |    PARTIAL |    FAIL |        PASS
loop_sum      |     OK |     OK |     OK |       PASS |    PARTIAL | TIMEOUT |        PASS
...
```

---

## 2. Strata CBMC backend fixes

Seven commits in `Strata/Backends/CBMC/GOTO/` that take SMACK-shaped
Strata Core programs through to a runnable `cbmc` invocation.
Listed in landing order:

### 2.1 Inout-parameter rename collision (`f265cda63`)

**Problem.** By Strata Core convention, every inout parameter
appears in both `Procedure.Header.inputs` and
`Procedure.Header.outputs` with the same identifier.
`procedureToGotoCtx` built the body-rewrite rename map by folding
inputs first, then outputs — the second fold overwrote the input
binding with `mkLocalSymbol pname x` (`pname::1::x`) instead of
keeping the formal-parameter binding `mkFormalSymbol pname x`
(`pname::x`). The result: every reference to an inout parameter
inside the body was renamed to a non-existent local.

**Fix.** Skip output rename entries when the same identifier is
already in inputs. Both structured and CFG paths patched.

**Files:** `Strata/Backends/CBMC/GOTO/CoreToCProverGOTO.lean`,
`CoreCFGToGOTOPipeline.lean`.

### 2.2 CFG dispatch (`74f0cc23a`)

**Problem.** `coreToGotoFiles` called `procedureToGotoCtx`
unconditionally, which errored on CFG bodies with `expected
structured body, got CFG`. SMACK output translates almost entirely
to CFG procedures (every body with a goto becomes one), so this
blocked the cbmc backend on every realistic input.

**Fix.** Dispatch on `Procedure.Body`: structured bodies through
`procedureToGotoCtx`, CFG bodies through `procedureToGotoCtxViaCFG`
(which already existed but was only wired into a smaller test
path).

**Files:** `Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean`.

### 2.3 Always-emit `guard` JSON field on ASSUME/ASSERT (`66e659656`)

**Problem.** `instructionToJson` omitted the `guard` field whenever
the guard expression was the constant `true`. Programs without
`assume true`/`assert true` worked because the field was always
emitted; programs with `assume true` (the SMACK output uses these
heavily as sourceloc anchors) had no `guard` field, and CBMC's
`symtab2gb` rejected the JSON.

**Fix.** Always emit `guard`, even when constant.

**Files:** `Strata/Backends/CBMC/GOTO/InstToJson.lean`.

### 2.4 Synthetic `__cprover_entry()` shim (`7e2b1fc25`)

**Problem.** CBMC accepts only standard C entry-point signatures
(`int main(void)`, `int main(int, char**)`, etc.). SMACK-translated
`main` takes parameters (memory maps `_M_*`, exception flags
`_exn`, return value `out r`) that don't match these shapes, so
cbmc rejected every binary with `function ... has unexpected
signature`.

**Fix.** Emit a synthetic `__cprover_entry()` function with
signature `void (*)()` that:
1. Declares local versions of each `main` parameter.
2. Initializes each with a `nondet_symbol_exprt` (after fix 2.7
   below) of the parameter's type.
3. Calls the real `main` with those locals.

The pipeline invokes cbmc with `--function __cprover_entry`.

**Files:** `Strata/Backends/CBMC/GOTO/DefaultSymbols.lean`,
`CoreToGOTOPipeline.lean`.

### 2.5 CFG block emission in reverse-postorder (`520f3f573`)

**Problem.** `coreCFGToGotoTransform` iterated blocks in
`cfg.blocks` order. SMACK emits basic blocks in source order
(e.g. `_bb0, _bb1, _bb3, _bb4, _bb6, _bb8, _bb10, _bb11, _bb13,
_bb14, _bb12, _bb9, _bb2, _bb7, _bb5`), which mixes branch arms.
When this listing was emitted as GOTO instructions, *forward* CFG
edges (e.g. `_bb1 → _bb12`) became *backward* GOTOs in the listing.
CBMC's loop detector classified these as back-edges and instrumented
them with unwinding-assertions, blowing the 120s timeout.

**Fix.** Reorder blocks via DFS reverse-postorder before emission.
After the reorder, every forward CFG edge `u → v` has
`locationNum(u) < locationNum(v)`; backward GOTOs in the listing
correspond exactly to real CFG cycles.

**Result.** 3 of 4 previously-timing-out cbmc verdicts (`abs_func`,
`max_func`, `nondet_branch`) flipped from TIMEOUT to a real
verdict. Only `loop_sum` (a real C `for` loop) remains a TIMEOUT.

**Files:** `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean`.

### 2.6 Canonicalize array-type emission (`7bff2d48e`)

**Problem.** Both `__cprover_entry`'s DECL instruction and `main`'s
parameter symtab record emit JSON for the same Strata `Map ref i8`
type. Both went through `tyToJson` which produced
`{"id":"array","sub":[{"id":"integer"}]}` without a `namedSub.size`
field. When `symtab2gb` deserialized the GOTO binary, it silently
added a default empty size expression to the DECL-site type but
not to the parameter-site type, producing two structurally non-equal
CBMC `array_typet` objects. CBMC's type checker compared
structurally and rejected the call:

```
function call: parameter "main::_M_0" type mismatch:
  got array { * size: { * type: } 0: integer }
  expected array 0: integer
```

This was the **dominant cbmc failure mode**: 38 of 65 programs in
the cross-validation matrix.

**Fix.** Add `namedSub.size = {id: "infinity", namedSub: {type:
integer}}` to the `Ty.Array` case in `tyToJson`. Both DECL- and
parameter-sites now emit size-qualified JSON; both deserialize to
structurally equal `array_typet` objects.

**Files:** `Strata/Backends/CBMC/GOTO/InstToJson.lean`.

### 2.7 Emit nondet array params as `nondet_symbol`, not `nondet` (`23926094f`)

**Problem.** After 2.6 unblocked the type-checker, programs with
`_M_*` array params reached cbmc's array solver, which then aborted
with:

```
Reason: unexpected array expression (collect_arrays): 'nondet'
```

CBMC's `arrayst::collect_arrays` (`solvers/flattening/arrays.cpp`)
accepts `ID_nondet_symbol` (a named, typed nondet stub) but rejects
bare `ID_nondet` for arrays. The Lean variant
`Expr.Identifier.Nullary.nondet` is documented in `Expr.lean:32` as
`nondet_symbol_exprt`, but `InstToJson.lean:121` was emitting
`"id": "nondet"`, lying about the node kind.

**Fix.** One-line change: `("id", "nondet")` →
`("id", "nondet_symbol")`.

**Result.** Cbmc now reaches actual model checking on the
(T-lowering) cluster. Failure detail shifted from internal SIGABRT
to real `Property violations found` on the third (callee-bodies)
blocker.

**Files:** `Strata/Backends/CBMC/GOTO/InstToJson.lean`.

### Cumulative impact of §2

The seven fixes form a cascade: each one exposes the next layer.

| Stage | Strata-CBMC verdict shape on the (T-lowering) cluster |
|---|---|
| Before any fixes | Pipeline silently aborts; cbmc not reached |
| After 2.1–2.4 | Cbmc invocation succeeds; type-mismatch error (rc=6) |
| After 2.6 | Type-checker passes; array-solver SIGABRT (rc=-6) |
| After 2.7 | Model checking runs; `Property violations found` on callee-bodies blocker |

---

## 3. BoogieToStrata translator features

Three features in `Tools/BoogieToStrata/Source/StrataGenerator.cs`
gating SMACK-specific behavior on `--smack`:

### 3.1 `--smack` CLI flag (`6b04d9399`, `0e54ff2bd`, `ac814e582`)

Adds an opt-in flag that turns on SMACK-specific accommodations:

- `InferModifies = true` (SMACK omits explicit `modifies` clauses
  on every procedure).
- The `assert_.<type>` requires injection (next item).

Off by default; strict Boogie input is unaffected.

### 3.2 `assert_.<type>` requires injection (under `--smack`)

**What.** SMACK encodes C `assert(EXPR)` as a call to
`assert_.iN(EXPR)` (a typed assert helper). To make the verifier
discharge a VC at each call site, BoogieToStrata injects a synthetic
`requires (_i0 != 0)` on bodyless `assert_.<type>` declarations.

**Example output for SMACK input `call assert_.i32(p);`:**

```strata
procedure assert_.i32(_i0 : i32)
spec {
  requires (_i0 != 0);
};
```

The call-elimination pass then generates a VC at each call site
checking `EXPR != 0`.

### 3.3 `__VERIFIER_assume` `free ensures` synthesis (`1b2231f99`)

**What.** SMACK encodes C `assume(EXPR)` as a call to
`__VERIFIER_assume(EXPR)`. To propagate the assumption to caller
path conditions, BoogieToStrata injects a synthetic `free ensures
(_i0 != 0)` on bodyless `__VERIFIER_assume` declarations.

`free` means the procedure body has no obligation to prove it; the
caller may assume it. Mirrors the `assert_` pattern with dual
polarity.

### 3.4 `__VERIFIER_assert` requires injection (`b3e606bb6`)

**What.** SMACK lowers C `assert(EXPR)` to a branch where the
failure arm calls `__VERIFIER_assert(0)`. Generalises the existing
`assert_.<type>` injection (3.2) to also fire on `__VERIFIER_assert`
declarations:

```strata
procedure __VERIFIER_assert(_M_0, _M_1, _exn, _exnv, _CurrAddr,
                            _i0 : i32)
spec {
  requires (_i0 != 0);
};
```

Since the failure arm passes the literal `0`, the requires becomes
`0 != 0` which is unsatisfiable, forcing the verifier to prove the
arm is unreachable — i.e. the assertion holds.

---

## 4. Benchmark suite: 65 programs

The `Examples/smack-docker/programs/` directory grew from 0 (none
of this exists on `origin/main`) to 65 programs across four import
batches plus hand-written originals.

### Composition

| Group | Programs | Source | Example |
|---|---:|---|---|
| Original benchmark | 12 | Hand-written | `abs_func.c`, `loop_sum.c`, `simple_add.c`, `nondet_branch.c` |
| Simplified AWS C Common | 13 | Hand-written, in style of `aws_array_eq.c` | `aws_byte_buf_append.c`, `aws_linked_list_push.c`, `aws_hash_string.c` |
| aws-c-common verbatim | 6 | Imported from `verification/cbmc/proofs/`, function bodies inlined from upstream `math.inl` | `aws_add_size_checked_harness.c`, `aws_is_power_of_two_harness.c` |
| FreeRTOS coreJSON verbatim | 12 | Imported from upstream `test/cbmc/proofs/`, full `core_json.c` vendored | `JSON_Validate_harness.c`, `skipSpace_harness.c`, `skipDigits_harness.c` |
| FreeRTOS coreMQTT/coreHTTP/coreSNTP | 10 | Same pattern, vendored upstream sources | `MQTT_Init_harness.c`, `HTTPClient_strerror_harness.c` |
| Standalone parsers | 4 | Hand-written harnesses | `jsmn_jsmn_parse_harness.c`, `cjson_cJSON_Parse_harness.c`, `picohttpparser_phr_parse_request_harness.c` |
| RFC reference impls | 8 | Public-domain refs + edge-case harnesses | `utf8_validate_overlong_harness.c` (Bjoern Höhrmann's DFA), `base64_decode_padding_only_harness.c`, `percent_decode_nul_harness.c` |
| **Total** | **65** | | |

### Example: `aws_add_size_checked_harness.c`

A verbatim CBMC harness from `awslabs/aws-c-common`, with the
function under test inlined from upstream `math.inl` and a SMACK
adapter prelude:

```c
// Imported verbatim from awslabs/aws-c-common
//   verification/cbmc/proofs/aws_add_size_checked/aws_add_size_checked_harness.c
// Function bodies inlined from include/aws/common/math.inl

#include "smack.h"
#include <stdint.h>
// ... adapter prelude shimming CBMC -> SMACK primitives ...

#define __CPROVER_assume(x)   __VERIFIER_assume(x)
#define nondet_uint64_t()     ((uint64_t)__VERIFIER_nondet_long())
#define AWS_OP_SUCCESS        0

// Function under test, verbatim from upstream:
AWS_STATIC_IMPL int aws_add_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    if ((b > 0) && (a > (UINT64_MAX - b)))
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    *r = a + b;
    return AWS_OP_SUCCESS;
}

// Harness body, folded into main():
int main(void) {
    uint64_t a = nondet_uint64_t();
    uint64_t b = nondet_uint64_t();
    uint64_t r = nondet_uint64_t();
    int rval = aws_add_u64_checked(a, b, &r);
    if (!rval) {
        assert(r == a + b);
    } else {
        assert((b > 0) && (a > (UINT64_MAX - b)));
    }
    return 0;
}
```

### Example: `utf8_validate_overlong_harness.c`

RFC 3629 explicitly rejects overlong UTF-8 encodings of ASCII bytes
(e.g. `0xC0 0xAF` for `/`). The harness exercises this:

```c
int main(void) {
    uint8_t buf[2] = {0xC0, 0xAF};
    int valid = validate_utf8(buf, 2);
    assert(valid == 0);
    return 0;
}
```

`validate_utf8` is Bjoern Höhrmann's DFA decoder (public domain),
inlined verbatim.

---

## 5. Cross-validation infrastructure

### 5.1 `tools/disagreement_matrix.py`

Reads `run_pipeline.py` output and emits a markdown verdict matrix.
Auto-tags rows where Strata-CBMC and `cbmc-native` disagree as
**(T-lowering)** — a disagreement between two paths through the
same underlying tool isolates the bug to Strata's lowering chain.

Example output:

```
| Program                    | deductive | bugFinding | cbmc | cbmc-native | Divergence       |
|---|---|---|---|---|---|
| array_sum                  | PASS      | PARTIAL    | FAIL | PASS        | **(T-lowering)** |
| simple_add                 | PASS      | PARTIAL    | FAIL | PASS        | **(T-lowering)** |
| HTTPClient_strerror_harness| PASS      | PARTIAL    | FAIL | PASS        | **(T-lowering)** |
```

### 5.2 `Examples/smack-docker/CROSS_VALIDATION.md`

The cross-validation writeup (228 lines, two updates so far).
Covers:
1. Pipeline architecture (three Strata-IR backends + native CBMC
   as ground-truth control).
2. The 65-program 4-backend matrix.
3. Per-divergence triage with **(P)** program defect / **(T)**
   translator-or-backend bug / **(S)** spec/contract gap tags.
4. Cumulative impact of the five fixes that landed during the
   screening.

The screening identified **5 distinct Strata defects** in one
session, four of which are fixed in this branch.

---

## 6. Documentation

### `Examples/smack-docker/README.md`

Pipeline doc with current results table, prerequisites, regenerating
.bpl from .c, running the pipeline, known blockers, what-this-branch-
ships, future-work pointers (s2n-tls / coreMQTT as next harness
sources), and per-script descriptions.

### `Tools/BoogieToStrata/Docs/STATUS.md`

Translator-level status: shipped features (CFG emission with gotos,
CFG procedure locals, name-collision fixes, type-synonym chain
resolution, SMACK `assert_` handling, `--smack` flag, ...), test
fixtures, known issues with cross-references to upstream issues.

### Filed but not committed

Three GitHub issue drafts in the repo root (uncommitted, intended
for opening upstream):

- `strata-verify-stack-overflow-deeply-nested-expr.md` — `strata
  verify` SIGABRT on deeply nested `if-then-else`. Verified on
  origin/main (HEAD: `349b1cf49`); reproduces at depth ≈ 4100.
  Suspected location: `Translate.translateExpr` partial def
  recursion with no fuel.
- `cbmc-inout-rename-collision.md` — original triage that led to
  fix 2.1.
- `cbmc-timeouts-and-stale-expects-report.md` — RPO emission triage
  that led to fix 2.5.
- `verifier-assume-synthesis-report.md` — investigation that led to
  feature 3.3.

---

## 7. Regression coverage

New tests in `StrataTest/Backends/CBMC/GOTO/`:

- `E2E_CFGPipeline.lean` — end-to-end CFG-bodied procedure
  translation through `procedureToGotoCtxViaCFG`.
- `E2E_CoreToGOTO.lean` — extended with the RPO emission test
  (`E2E_CFGRPOReorder`): a 4-block diamond CFG with `join`
  deliberately listed before its predecessors. Pre-fix produces
  backward GOTOs from `branch_*` to `join`; post-fix produces
  none. Asserts the count of backward GOTOs is 0.
- `LambdaToCProverGOTO.lean` — type-emission tests covering
  `Map ref i8 → array` with the size-qualified shape from fix 2.6.

`Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`
— `--smack` marker support: each `.bpl` test fixture may carry a
`{:smack}` annotation in its first 5 lines to opt into the
SMACK-specific accommodations under test. A regression test pins
the off-by-default behavior of `--smack`, and an extended
`SmackAssertDuplicateSpec` test covers the requires-already-present
case.

---

## Summary table

| Metric | origin/main | htd/smack |
|---|---:|---:|
| Pipeline programs (`Examples/smack-docker/programs/*.c`) | 0 | 65 |
| Strata CBMC backend bugs fixed | 0 | 7 |
| BoogieToStrata SMACK-specific features | 0 | 4 (`--smack` flag, `assert_.<type>` requires, `__VERIFIER_assume` ensures, `__VERIFIER_assert` requires) |
| Cross-validation backends | 0 | 4 (deductive, bugFinding, Strata-CBMC, cbmc-native) |
| Strata defects identified by cross-validation | 0 | 5 (4 fixed; 1 stack-overflow filed) |
| Cross-validation matrix | none | 64-program 4-backend |

**Verdict on the 64-program suite (latest run, post all fixes):**

|  | PASS | PARTIAL/FAIL | TIMEOUT |
|---|---:|---:|---:|
| Strata deductive | 33 | 30 | 1 |
| Strata bugFinding | 0 | 62 | 2 |
| Strata-CBMC | 0 | 62 | 2 |
| CBMC-native | 43 | 21 | 0 |

The deductive PASS count *dropped* from 47 (pre-fix) to 33
(post-fix) — a positive change. The 14-row delta is exactly the
(S) → real-VC transition: previously vacuous PASSes (no functional
contracts, no obligations) became real verification obligations
the verifier mostly discharges (e.g. `90 pass, 1 fail`).
