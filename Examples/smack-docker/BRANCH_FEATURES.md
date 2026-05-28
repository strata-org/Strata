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
| 4 | Strata Core / Transform features (`Strata/Languages/Core/`, `Strata/Transform/`) | [§4](#4-strata-core--transform-features) |
| 5 | Benchmark suite (`Examples/smack-docker/programs/`) | [§5](#5-benchmark-suite-94-programs) |
| 6 | Cross-validation infrastructure (`tools/`, `CROSS_VALIDATION.md`) | [§6](#6-cross-validation-infrastructure) |
| 7 | Documentation (`README.md`, `STATUS.md`) | [§7](#7-documentation) |
| 8 | Regression coverage (`StrataTest/`) | [§8](#8-regression-coverage) |
| 9 | Bugs surfaced (with filing & merge status) | [§9](#9-bugs) |

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

Eight commits in `Strata/Backends/CBMC/GOTO/` that take SMACK-shaped
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

### 2.8 Emit all callee procedure bodies (`ca95931be`)

**Problem.** `coreToGotoFilesDispatch` emitted only the entry
procedure (`main`) into the GOTO output. Every callee — user-defined
helpers, SMACK prelude stubs, `__VERIFIER_assert`, `_initialize`,
etc. — appeared as bodyless declarations in the symtab. Cbmc reached
the call and reported `[.no-body.<callee>] no body for callee
<callee>: FAILURE`, blocking every program with non-trivial calls.

**Fix.** After emitting the entry procedure, iterate all
`Core.Procedure` declarations in the program; for each non-abstract,
non-entry procedure, call `procedureToGotoCtxDispatch` +
`emitProcWithLifted` and splice its GOTO body into the output.
Bodyless procedures (`isAbstract = true`) stay as symtab declarations
only. `Core.Function` items (Boogie mathematical functions) are
intentionally excluded — they're already registered as
`mathematical_function`-typed symbols via `fnAppSymbols`, and adding
GOTO bodies for them would crash CBMC's `to_code_type` assertion.

**Result.** User-defined callees (and lifted Boogie functions) now
have GOTO bodies in the output. The residual `[.no-body.<callee>]`
blocker is now narrowed to the SMACK prelude stubs
(`__VERIFIER_assume`, `assert_.i32`, etc.) which have no Strata
body to translate — so they appear as bodyless symtab declarations
and CBMC still reports them as missing. Two additional failure
shapes also surface: an `_exnv` argument-typing bug (call to
`__SMACK_static_init` passes `_exnv : int` where position 1 expects
`_exn : bool`), and the pre-existing array-bounds crash on
memory-map programs. As a consequence, all 93 portfolio programs
still report cbmc=FAIL today; tracked under
[#1184](https://github.com/strata-org/Strata/issues/1184).

**Files:** `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean`.

### Cumulative impact of §2

The eight fixes form a cascade: each one exposes the next layer.

| Stage | Strata-CBMC verdict shape on the (T-lowering) cluster |
|---|---|
| Before any fixes | Pipeline silently aborts; cbmc not reached |
| After 2.1–2.4 | Cbmc invocation succeeds; type-mismatch error (rc=6) |
| After 2.6 | Type-checker passes; array-solver SIGABRT (rc=-6) |
| After 2.7 | Model checking runs; `Property violations found` on callee-bodies blocker |
| After 2.8 | User-defined callees emitted; `[.no-body.X]` narrowed to SMACK prelude stubs (`__VERIFIER_assume`, `assert_.i32`, ...). Two additional surface failures: `_exnv` argument-typing bug, array-bounds crash on memory-map programs. All 93 portfolio rows still cbmc=FAIL today. |

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

## 4. Strata Core / Transform features

Two commits that strengthen the Strata-side verifier path itself,
distinct from the CBMC backend (§2) and the BoogieToStrata translator
(§3).

### 4.1 Sound `ensures` synthesis pass (`390fadc37`)

**What.** Adds a Strata-side analysis under the `--synthesize-ensures`
flag (off by default) that infers `ensures` clauses for procedures
whose bodies match a sound linear pattern. For each output-only
parameter, the pass forward-substitutes through intermediate locals
to a closed expression over input parameters and emits `free ensures
(out == expr)`.

**Soundness.** Three checks gate emission:

1. `collectLinearCmds` rejects bodies with branches/loops.
2. `buildSubstMap` rejects bodies with user-procedure calls or havoc
   (`.set _ .nondet _`) that could break determinism mid-body.
3. `onlyInputFvars` rejects synthesised expressions that mention any
   variable not declared as a procedure input.

Together these guarantee the synthesised ensures holds for any input
satisfying the procedure's preconditions. The `Free` flag means
callers benefit; the body itself isn't checked against the synthesised
clause.

**Concrete example.** `Examples/smack-docker/programs/simple_assert.c`:

```c
int add(int a, int b) { return a + b; }
int main(void) {
  int r = add(3, 4);
  assert(r == 7);
}
```

Without the flag: `deductive=PARTIAL` (1 pass, 1 fail; the call-elim
pass havocs `r` because `add` has no `ensures`, and `r == 7` becomes
unprovable).

With `--synthesize-ensures`: the pass derives
`ensures (_r == _add_i32(_i0, _i1))` for `add`. Call-elim substitutes
through, and `r == 7` discharges. `deductive=PASS` (3 goals, all pass
— including the synthesised ensures and the original assertion).

**Files:** `Strata/Languages/Core/Transform/EnsuresSynthesis.lean`
(new); `Strata/Languages/Core/Options.lean`,
`Strata/Languages/Core/Verifier.lean`, `StrataMain.lean` (modified);
`StrataTest/Languages/Core/Tests/EnsuresSynthesisTest.lean` (new).

### 4.2 Apply CallElim to CFG-bodied procedures (`42ff8a4b8`)

**Problem.** `runProgram` in `Strata/Transform/CoreTransform.lean`
previously skipped CFG bodies with the comment `Skip CFG bodies;
transforms are statement-level`. CallElim is the main consumer of
`runProgram`. Skipping CFG bodies meant call sites inside any
CFG-bodied procedure (which is most SMACK-translated procedures,
since any procedure with a `goto` becomes one) had no `requires`-VCs
generated for their callees. The deductive verifier then silently
passed those call sites, producing **vacuous PASS verdicts** on
programs whose only failing obligation lived behind such a call.

**Fix.** Extend `runProgram`'s CFG branch to walk each block's
command list, applying `f` to each command and replacing it with
the result. A new helper `runCmdsRec` handles the Statement-to-Command
shape mismatch (CFG blocks store `List Command`; `f` returns
`List Statement`). Replacement Statements that are non-flat
(`block`, `ite`, `loop`, etc.) bail out and leave the original
command unchanged — these can't fit inside a basic block. In practice
CallElim only emits flat Statement sequences, so this is exhaustive.

**Verified on `Examples/smack-docker/programs/skipSpace_harness.bpl`
under `--split-procs`:**

Pre-fix: `deductive=PASS`, all 18 VCs are
`__VERIFIER_assume_ensures_0` (the harness's preconditions). The 3
post-call `assert(...)` calls produce no VCs.

Post-fix: `deductive=PARTIAL`, 1 pass + 3 fail. The 3 failing VCs
are `callElimAssert___VERIFIER_assert_requires_0_*` obligations at
each post-call `assert(...)` site. They report `unknown` (the
upstream `skipSpace` function has no `ensures`, so the verifier
havocs all state and can't reason about post-call invariants). This
is the correct, expected outcome — real obligations now reach the
solver.

**Severity.** This was a real soundness gap. All 9 contract-ported
coreJSON harnesses (skipSpace, skipDigits, JSON_Validate, skipString,
skipObjectScalars, skipScalars, skipUTF8, skipAnyScalar,
skipCollection) were silently passing deductive on vacuous obligations
until this fix. The cumulative impact on the matrix is the largest of
any single fix in the project so far.

**Files:** `Strata/Transform/CoreTransform.lean`.

### 4.3 Body evaluation at call sites (`dd0c0d7cd`)

Adds a `--call-policy {contract|body|bodyOrContract}` option that
lets the deductive evaluator analyse the callee's body at the call
site, bounded by `--inline-fuel N` (default `100000`). On
`OutOfFuel`, `bodyOrContract` falls back to the existing contract
path so verdicts are never worse than today's `contract` policy
(which remains the default).

**Why.** With contract-only reasoning, every call is replaced by
`asserts(pre); havoc(lhs); assume(ensures)`. When the callee's
`ensures` is missing or weak — the dominant case for SMACK-translated
user-defined helpers — the post-call lhs becomes a fresh symbolic
variable with no useful constraints, and any subsequent assertion
involving it can't be discharged. This was the dominant deductive
sub-class (a) PARTIAL cause across the matrix.

**How.** `Command.inlineCallBody` (the new evaluator-time handler)
pushes a fresh scope binding callee formals to caller arg expressions
and outputs to fresh fvars, runs the body via `Statement.eval`
(structured) or `evalCalleeCFG` (CFG), reads output values back from
the scope, pops the scope, and binds the caller's lhs to the
body-derived expressions. Shared call-setup helpers (`computeTypeSubst`,
`mkFormalArgSubst`, `mkReturnSubst`, `emitPreconditionAsserts`) were
extracted from `inlineCallContract` so both handlers discharge
preconditions identically.

`callElimPipelinePhase` is conditional on `callPolicy = .Contract`;
under `Body` / `BodyOrContract` it's skipped so `.call` commands
survive into the evaluator, where `Command.handleCall` dispatches per
call.

**Impact.** Single largest verdict-improvement on the matrix to date:
**42 of 43 portfolio rows flip from PARTIAL to PASS deductive** under
`bodyOrContract`. The combined 93-program suite goes from 39 PASS / 54
PARTIAL (contract baseline) to 82 PASS / 11 PARTIAL.

**Multi-branch limitation.** When a callee body contains a symbolic
`if` that produces multiple result envs with divergent variable
bindings, the current implementation refuses with an explicit error
rather than perform an unsound merge. `bodyOrContract` falls back to
contract in that case. The single residual portfolio PARTIAL
(`nondet_branch`) is exactly this case. A design proposal lives at
`Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md` — making
`Command.eval` and friends return `List Env` so multi-path body-eval
flows through `evalAuxGo`'s active-path machinery.

**CLI / pipeline.** `strata verify --call-policy bodyOrContract
--inline-fuel N`. The smack-docker driver gained matching axes
(commit `998d64635`): `python3 run_pipeline.py --call-policy
bodyOrContract`.

**Files:** `Strata/Languages/Core/StatementEval.lean` (new
`Command.inlineCallBody`, `Command.handleCall`, `evalCalleeCFG`,
shared helpers), `Strata/Languages/Core/ProcedureEval.lean`
(`Procedure.eval` gains a `fuel` parameter; threads via `Env.fuel`),
`Strata/Languages/Core/Env.lean` (`Env.fuel`, `Env.callPolicy`),
`Strata/Languages/Core/Options.lean` (`CallPolicy` enum,
`VerifyOptions.callPolicy`, `VerifyOptions.inlineFuel`),
`Strata/Languages/Core/Verifier.lean` (conditional
`callElimPipelinePhase`), `StrataMain.lean` (CLI flags),
`Strata/Languages/Core/Core.lean` (verifier env seeding),
`StrataTest/Languages/Core/Tests/InlineCallBodyTests.lean` (regression
tests).

---

## 5. Benchmark suite: 94 programs

The `Examples/smack-docker/programs/` directory grew from 0 (none
of this exists on `origin/main`) to 94 programs across five import
batches plus hand-written originals.

### Composition

| Group | Programs | Source | Example |
|---|---:|---|---|
| Original benchmark | 12 | Hand-written | `abs_func.c`, `loop_sum.c`, `simple_add.c`, `nondet_branch.c` |
| Simplified AWS C Common | 13 | Hand-written, in style of `aws_array_eq.c` | `aws_byte_buf_append.c`, `aws_linked_list_push.c`, `aws_hash_string.c` |
| aws-c-common verbatim | 6 | Imported from `verification/cbmc/proofs/`, function bodies inlined from upstream `math.inl` | `aws_add_size_checked_harness.c`, `aws_is_power_of_two_harness.c` |
| FreeRTOS coreJSON verbatim | 12 | Imported from upstream `test/cbmc/proofs/`, full `core_json.c` vendored; 9 carry contract ports (see below) | `JSON_Validate_harness.c`, `skipSpace_harness.c`, `skipDigits_harness.c` |
| FreeRTOS coreMQTT/coreHTTP/coreSNTP | 10 | Same pattern, vendored upstream sources | `MQTT_Init_harness.c`, `HTTPClient_strerror_harness.c` |
| Standalone parsers | 4 | Hand-written harnesses | `jsmn_jsmn_parse_harness.c`, `cjson_cJSON_Parse_harness.c`, `picohttpparser_phr_parse_request_harness.c` |
| RFC reference impls | 8 | Public-domain refs + edge-case harnesses | `utf8_validate_overlong_harness.c` (Bjoern Höhrmann's DFA), `base64_decode_padding_only_harness.c`, `percent_decode_nul_harness.c` |
| SV-COMP ReachSafety | 29 | Imported from `sosy-lab/sv-benchmarks` (commit `eb8fbd513`) with verdict oracle in `svcomp_verdicts.json`; 22 safe, 7 unsafe across `c/locks/`, `c/loops-crafted-1/`, `c/reducercommutativity/` | `sv_locks_10.c`, `sv_loops_mono3_1.c`, `sv_max_sep.c` |
| **Total** | **94** | | |

### Contract ports on coreJSON harnesses

Nine of the 12 coreJSON harnesses carry **upstream-derived contracts**
ported into their `main()` bodies — `__VERIFIER_assume` preconditions
and `assert(...)` postconditions ported from FreeRTOS/coreJSON's
`core_json_contracts.h`:

- Commit `495e09c87`: `skipSpace`, `skipDigits`, `JSON_Validate`,
  `skipString`.
- Commit `5475c6710`: `skipObjectScalars`, `skipScalars`, `skipUTF8`,
  `skipAnyScalar`, `skipCollection`.

The remaining 3 (`skipEscape_harness` and the two SearchConst/Iterate
ones) keep their original vacuous shape.

Pre-port: vacuous PASS (no obligations). Post-port: real obligations
land at the deductive verifier (after fix §4.2 above) — the contracts
are the source of the postcondition assertions whose VCs the matrix
now reports.

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

## 6. Cross-validation infrastructure

### 6.1 `tools/disagreement_matrix.py`

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

### 6.2 `Examples/smack-docker/CROSS_VALIDATION.md`

The cross-validation writeup. Covers:
1. Pipeline architecture (three Strata-IR backends + native CBMC
   as ground-truth control).
2. The 94-program 4-backend matrix (64 portfolio + 29 SV-COMP, plus
   `picohttpparser` excluded due to known cbmc-native OOM).
3. Per-divergence triage with **(P)** program defect / **(T)**
   translator-or-backend bug / **(S)** spec/contract gap tags.
4. Iterative-update narrative as fixes landed and the verdict
   landscape evolved.

The cross-validation screening surfaced (or confirmed) **20 distinct
defects/issues** across the Strata-CBMC GOTO backend, BoogieToStrata,
Strata Core / Transform, the DDM type-checker, the verifier runtime,
and pipeline-driver display gaps. 15 are fixed on this branch; the
full ledger with filing & merge status lives in §9 below. The SV-COMP
oracle integration (29 programs with ground-truth safe/unsafe labels)
confirmed zero soundness violations: the six initial `unsafe ∧
deductive=PASS` candidates were all matrix-display artifacts (the
verifier emits `path unreachable` qualifiers that `run_pipeline.py`
collapses to PASS).

---

## 7. Documentation

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

Four GitHub issue drafts in the repo root (uncommitted, intended
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

## 8. Regression coverage

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

New tests in `StrataTest/Languages/Core/Tests/`:

- `InlineCallBodyTests.lean` — six tests for the body-eval feature
  (§4.3): structured callee under `.Body` (assertion reduces to
  `true`), structured callee under `.Contract` (assertion deferred
  against havoc'd fresh fvar), CFG callee under each policy, looping
  CFG under `.Body` low-fuel (surfaces `OutOfFuel`), looping CFG
  under `.BodyOrContract` low-fuel (falls back to contract).
- `EnsuresSynthesisTest.lean` — covers the `--synthesize-ensures`
  pre-pass (§4.1): three soundness checks (linear-body shape,
  postcondition implication, no user calls).

`Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`
— `--smack` marker support: each `.bpl` test fixture may carry a
`{:smack}` annotation in its first 5 lines to opt into the
SMACK-specific accommodations under test. A regression test pins
the off-by-default behavior of `--smack`, and an extended
`SmackAssertDuplicateSpec` test covers the requires-already-present
case.

---

## 9. Bugs

Bugs surfaced (or confirmed) by this branch's cross-validation work,
with filing and merge status. **Keep this section up to date** as
issues land upstream; the headline is that *every* CBMC backend,
BoogieToStrata, and Core-transform fix is currently `htd/smack`-only —
none has reached `main` yet.

Legend:
- **Filed?** issue # if filed on the upstream tracker; "—" if not
- **htd/smack** "✓" if a fix commit is on this branch; "—" if not
- **main / main2?** which upstream branch the fix has merged into; "—" if not yet

### 9.1 Strata-CBMC GOTO backend (8)

All surfaced via the cross-validation matrix (`Strata/Backends/CBMC/GOTO/`).

| # | Bug | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 1 | Inout-param rename collision in `procedureToGotoCtx` — inouts re-bound to nonexistent local symbol; blocked every CBMC translation with inout call sites | [#1198](https://github.com/strata-org/Strata/issues/1198) (open) | ✓ `f265cda63` | — |
| 2 | Missing `__cprover_entry` shim — SMACK-translated `main` has memory-map params; CBMC rejected with "no entry point" rc=6 | — | ✓ `7e2b1fc25` | — |
| 3 | `guard` JSON field elided when condition is `true` — `symtab2gb` rejected; ASSUME/ASSERT couldn't round-trip | — | ✓ `66e659656` | — |
| 4 | CFG blocks emitted in non-RPO order → spurious back-edges — CBMC's loop detector flagged 8 fake loops in `nondet_branch`, triggering unwinding-assertion timeouts | — | ✓ `520f3f573` | — |
| 5 | Array-type-emission asymmetry in `tyToJson` — DECL-site vs parameter-site produced structurally unequal CBMC array types; rc=6 type-mismatch on every program with `_M_*` memory-map params (38 of 65 rows in original portfolio) | — | ✓ `7bff2d48e` | — |
| 6 | Nondet array params emitted as `nondet` instead of `nondet_symbol` — CBMC's array-constraint collector aborted: `unexpected array expression (collect_arrays): 'nondet'` | — | ✓ `23926094f` | — |
| 7 | CFG-bodied procedures errored "expected structured body" in `procedureToGotoCtx` — CFG-bodied `main` couldn't be translated at all | — | ✓ `74f0cc23a` | — |
| 8 | Callee bodies not emitted — only the entry procedure body was translated; CBMC reported `[.no-body.<callee>]` on every call. **Partial fix landed (`ca95931be`); residual blocker remains: `__VERIFIER_assume` / `assert_.i32` still bodyless after the partial fix, so all 93 programs still report cbmc=FAIL.** | [#1184](https://github.com/strata-org/Strata/issues/1184) (open; related: missing multi-return support) | ✓ partial `ca95931be` | — |

Sibling open issue [#1186](https://github.com/strata-org/Strata/issues/1186) (Asymmetric translator handling of nondet `init` produces a precision mismatch with CBMC) — surfaced during this investigation but not patched on this branch.

### 9.2 BoogieToStrata translator (3)

| # | Bug | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 9 | `__VERIFIER_assume` had no spec under `--smack` — call-elim eliminated the assumption; `assume(p)` from C source vanished | [#1148](https://github.com/strata-org/Strata/issues/1148) (closed; tracking) | ✓ `1b2231f99` (cherry-picked from PR 1149) | — (PR 1149 not merged into main) |
| 10 | `__VERIFIER_assert` had no `requires` spec — `assert(EXPR)` from C source compiled into a vacuous call; no obligation reached the verifier | — | ✓ `b3e606bb6` | — |
| 11 | `assert_.<type>` requires-injection unconditional — old PR 1149 injected `requires` regardless of source language. Gated on `--smack` | [#1148](https://github.com/strata-org/Strata/issues/1148) (closed; tracking) | ✓ `0e54ff2bd`, `ac814e582` | — (PR 1149) |

Sibling open issue [#1184](https://github.com/strata-org/Strata/issues/1184) (CBMC backend missing multi-return support, error silently swallowed) — surfaced during the same investigation but not patched on this branch.

### 9.3 Strata Core / Transform (3)

| # | Bug | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 12 | `runProgram` skipped CFG bodies — call sites inside any CFG-bodied procedure had no `requires`-VCs generated; the verifier silently passed those call sites with vacuous PASS verdicts. **Largest single soundness improvement of the project so far.** | — (commit message documents) | ✓ `42ff8a4b8` | — |
| 13 | Contract-only call evaluation — every `.call` was replaced by `havoc(lhs); assume(ensures)`, losing all body-derived information. Caused the dominant deductive sub-class (a) PARTIALs (54 of 93). Resolved by the body-eval feature. | — (motivation captured in spec) | ✓ `dd0c0d7cd` (body-eval feature) | — |
| 14 | Cross-procedure `Env.error` contamination — when one procedure errors (CFG fuel exhaustion, etc.), `fixupError` doesn't clear `Env.error`; subsequent procedures short-circuit and emit zero obligations. **Confirmed today on `htd/smack`**: `aws_array_eq` reports `All 4 goals passed` end-to-end but `--procedures main` shows `0 goals passed, 3 failed`. The `--split-procs` workaround masks this, not fixes it. | [#1185](https://github.com/strata-org/Strata/issues/1185) (open) | — | — (fix lives on `htd/fix-eval` as `d55ac1c33` + `eeb0dfa3d` + `ecf402211`, not yet on either main or htd/smack) |

### 9.4 Strata DDM / parser / type-checker (2)

| # | Bug | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 15 | Transitive type-synonym chain not resolved for comparison/arithmetic operators — `<=`, `<`, `>=`, `>`, `+`, `-`, `*`, `div`, `mod` panicked when operands had a synonym-of-`int` type (e.g. `ref := i64 := int`) | [#1148](https://github.com/strata-org/Strata/issues/1148) (closed; tracking) | ✓ `e94635f8a` | — |
| 16 | Type checker fails on nondet goto with undeclared `$__nondet_N` | [#1162](https://github.com/strata-org/Strata/issues/1162) (open; resolved on `htd/smack` per BoogieToStrata STATUS.md) | ✓ (referenced by translator change in `Tools/BoogieToStrata/`) | — |

### 9.5 Strata `verify` runtime (1, filed but not patched)

| # | Bug | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 17 | Stack overflow / SIGABRT on deeply-nested expressions — `Translate.translateExpr` is `partial def` with no fuel; reproduces at depth ≈ 4100 on `origin/main` HEAD. Manifested as `skipEscape_harness` SIGABRT in the deductive verifier. | drafted as `strata-verify-stack-overflow-deeply-nested-expr.md` (uncommitted, intended for upstream filing) | — | — |

### 9.6 Pipeline-driver / matrix-display gaps (3 — not Strata bugs)

| # | Issue | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 18 | `run_pipeline.py` collapses `path unreachable` PASSes — six SV-COMP unsafe programs initially looked like soundness probes (`unsafe ∧ deductive=PASS`); each is actually `pass (path unreachable)`. Matrix-display gap, not soundness bug. | — | — | — |
| 19 | bugFinding partials dominated by `__VERIFIER_assume`-only failures — bugFinding under `bodyOrContract` produces zero verdict improvements (verified on full portfolio: 0/65 contract, 0/64 bodyOrContract). bugFinding's PARTIALs are about unconstrained inputs, not missing ensures. | — | — | — |
| 20 | Multi-branch body-eval refused as soundness guard — `Command.inlineCallBody` errors when a callee body produces multiple result envs. The single residual portfolio PARTIAL (`nondet_branch`) is this case. Design proposal exists for fork-and-continue (return `List Env`). | — | partial guard in `dd0c0d7cd`; design doc `Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md` | — |

### Summary stats

- **20 distinct bugs/issues** surfaced (or confirmed) on this branch.
- **15 fixed** with commits on `htd/smack`.
- **2 fixed elsewhere** (#1185 fix lives on `htd/fix-eval`; not on `htd/smack` or `main`).
- **3 not yet patched** (#1184, #1186, draft `strata-verify-stack-overflow`).
- **0 fixes have landed on `main` or `main2`** — every CBMC-backend, BoogieToStrata, and Core-transform fix is still `htd/smack`-only.

### Filed-issue index

- **Open and unresolved on main:** #1184, #1185, #1186, #1198, #1162.
- **Closed (tracking-issue):** #1148 (BoogieToStrata blockers — its sub-issues are addressed by branch fixes).
- **Drafted but unfiled:** `strata-verify-stack-overflow-deeply-nested-expr.md`, `cbmc-inout-rename-collision.md` (predates the actual #1198 filing), `cbmc-timeouts-and-stale-expects-report.md`, `verifier-assume-synthesis-report.md`.

### Path to upstream

Every fix on this branch is currently `htd/smack`-unique. None has reached `main` yet. Upstream-landing dependencies:

1. The **8 CBMC GOTO backend fixes** depend on `htd/unstructured-procedure`'s CFG-Procedure work (in flight).
2. The **BoogieToStrata fixes** are tied to PR #1149.
3. The **Core-transform fixes** (`42ff8a4b8`, `dd0c0d7cd`) depend on CFG-eval which is in `htd/unstructured-procedure`.
4. The **#1185 fix** (cross-procedure `Env.error`) lives on `htd/fix-eval` — most independent of all; could land directly on `main` and be back-merged.

The branch is a substantial body of fix work. Most of it is upstream-able once the underlying PRs (`htd/unstructured-procedure`, #1149) merge.

---

## Summary table

| Metric | origin/main | htd/smack |
|---|---:|---:|
| Pipeline programs (`Examples/smack-docker/programs/*.c`) | 0 | 94 |
| Strata CBMC backend bugs fixed | 0 | 8 |
| Strata Core / Transform fixes | 0 | 2 (sound ensures-synthesis pass, CFG-bodied CallElim) |
| BoogieToStrata SMACK-specific features | 0 | 4 (`--smack` flag, `assert_.<type>` requires, `__VERIFIER_assume` ensures, `__VERIFIER_assert` requires) |
| Contract-ported coreJSON harnesses | 0 | 9 |
| Cross-validation backends | 0 | 4 (deductive, bugFinding, Strata-CBMC, cbmc-native) |
| Strata defects identified by cross-validation | 0 | 5 (4 fixed; 1 stack-overflow filed) |
| Cross-validation matrix | none | 93-program 4-backend (64 portfolio + 29 SV-COMP) |

**Verdict on the combined 93-program suite (`--split-procs` mode):**

|  | PASS | not-PASS | TIMEOUT |
|---|---:|---:|---:|
| Strata deductive | 39 | 54 | 0 |
| Strata bugFinding | 0 | 93 | 0 |
| Strata-CBMC | 0 | 93 | 0 |
| CBMC-native | 70 | 23 | 0 |

The 93 = 64 portfolio (`wt-test/pipeline-portfolio-v3.txt`) + 29
SV-COMP (`wt-test/pipeline-svcomp.txt`); `picohttpparser` is excluded
due to known cbmc-native OOM. The deductive PASS count dropped from
33 (v2) to 21 (v3) on the portfolio after the CFG-CallElim fix
(`42ff8a4b8`) replaced previously-vacuous PASSes with real PARTIAL
verdicts; on SV-COMP the deductive backend PASSes 18 of 29 directly,
since SV-COMP programs lack the user-defined helpers that drive the
portfolio's sub-class (a) `❓ unknown` failures. The dominant cause
of remaining PARTIAL verdicts is translator-side conservatism
(missing `ensures` on upstream parser callees), not program defects.
See `CROSS_VALIDATION.md` Updates 3 and 4 for the full breakdown.

Run history of the verdict matrix lives in
`Examples/smack-docker/README.md` (this is a feature ledger, not a
results log).
