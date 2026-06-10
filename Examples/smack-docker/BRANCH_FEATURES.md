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

Commits that strengthen the Strata-side verifier path itself,
distinct from the CBMC backend (§2) and the BoogieToStrata translator
(§3).

### 4.1 Apply CallElim to CFG-bodied procedures (`42ff8a4b8`)

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

### 4.2 Body evaluation at call sites (`dd0c0d7cd`)

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

### 4.3 CFG `condGoto` deferred-obligation dedup (`277c468cb`)

**Problem.** In `evalCFGStep`'s symbolic-`condGoto` arm, both
`env_t` and `env_f` were constructed by record-update on the same
parent `env'` and inherited `env'.deferred` wholesale. Each
symbolic branch therefore doubled the pre-split obligation set;
`mergeResults` then concatenated the terminal envs' `deferred`
arrays without further dedup, propagating duplicates into the
next procedure's eval. On SMACK-translated programs with many
sequential symbolic branches (cJSON, JSON_*, skip_*) this
multiplied the deferred count without bound. Across the 17
procedures of `cjson_cJSON_Parse_harness.bpl` the count grew
**28 → 56 → 4,928 → 9,856 → 68,992 → 896,896 → 3,960,692,736**,
and `parse_string` (the next procedure) hung trying to fork its
own paths off a 4-billion-element array. This was the actual
hang on every program ≥20K lines: not stack overflow, not z3,
not "thousands-deep ITE chain" — `Array (Imperative.ProofObligation
Expression)` allocation.

**Fix.** One-line change in `Strata/Languages/Core/ProcedureEval.lean`'s
symbolic `condGoto` arm: clear `deferred` on the false branch
(`env_f.deferred := #[]`), mirroring the existing dedup pattern at
`Strata/Languages/Core/StatementEval.lean:673` for structured
`.ite`. Soundness: each `ProofObligation` snapshots its
`assumptions` (path conditions) at creation time
(`Strata/DL/Imperative/CmdEval.lean:64-83`), so each obligation is
self-contained — the verifier proves `assumptions ⊨ predicate`
without consulting the env's current state. Dropping a duplicate
from one branch removes a redundant proof obligation that the
sibling branch still carries; the set of distinct obligations is
unchanged. `env.deferred` is otherwise write-only during eval
(verified by grep: only post-eval consumers at `Core.lean:168`
and `ProcedureEval.lean:60` read it).

**Result.** `cjson_cJSON_Parse_harness.bpl`, previously hanging
indefinitely under every flag combination, now PASSes deductive
verification. `JSON_Iterate_harness`, `JSON_Validate_harness`,
`JSON_SearchConst_harness`, `skipAnyScalar_harness`,
`skipCollection_harness`, `skipObjectScalars_harness`,
`skipScalars_harness` likewise unblocked. The full 94-program sweep
under `--split-procs --call-policy bodyOrContract --inline-fuel 100
--check-level full` (the v6 row in the run history) produces 68 PASS
/ 15 PASS-? / 11 PARTIAL / 0 FAIL / 0 TIMEOUT — identical PARTIAL
identities to the v4 baseline (no soundness regression; full
empirical confirmation that the dropped obligations were duplicates).
Three v5-PASS-? programs (`HTTPClient_AddRangeHeader_harness`,
`skipString_harness`, `skipUTF8_harness`) graduate to clean PASS in
v6 — the dedup removes duplicate accumulated path-conditions that
had been collapsing into vacuous discharges.

**Files:** `Strata/Languages/Core/ProcedureEval.lean` (the fix),
`StrataTest/Languages/Core/Tests/ProcedureEvalCFGTests.lean`
(regression test — pre-split assert before symbolic `condGoto`
asserts the merged deferred contains the obligation exactly once,
not twice).

**Related: subprocess timeout reliability fix in
`Examples/smack-docker/run_pipeline.py` (`9f26fffd7`).** `run_cmd`
previously used `subprocess.run(timeout=, capture_output=True)`,
which on macOS Python 3.11 with CPU-bound output-silent children
fires SIGKILL but blocks indefinitely in `proc.communicate()`'s
`os.read()` against a never-written pipe — the entire pipeline
matrix would hang on the first divergent program. Replaced with a
layered design: gtimeout/timeout wrapper (verified at module load
by a `gtimeout 0.5 sleep 10` self-test), with a Python `Popen` +
`start_new_session=True` + `os.killpg(SIGKILL)` fallback. Tests in
`Examples/smack-docker/test_run_cmd.py`. With this in place,
accidental inclusion of any divergent program now produces a
clean TIMEOUT verdict at the per-program 120s budget rather than
hanging the whole run.

### 4.4 Iterative walker family for long flat-list programs (4 commits)

**Problem.** A `prog.decls : List Decl` of tens of thousands of
elements (e.g. 100K trivial axioms — the canonical sce1 reproducer
from `reports/stack-and-hang-conjectures-report.md` issue 1) caused
`strata verify` to SIGABRT with `Stack overflow detected. Aborting.`
Pre-fix bisection pinpointed `transformDecls` (`Strata/Transform/PrecondElim.lean`)
as the dominant culprit at N≈30K-50K, with `TermCheck.transformDecls`
and `translateCoreDecls` overflowing at higher N. `Program.typeCheck`
was also non-tail-recursive on long decl lists. Additionally,
`runProgram` had an O(N²) replacement pattern using `List.set`.

**Fix.** Four commits, cherry-picked from `htd/smack-tco-experiment`:

1. **`fix(verify): iterativize translateCoreDecls and Program.typeCheck`**
   (`a3fb64376` → cherry-picked as `95abbe567`). Rewrites
   `translateCoreDecls` from `where go` recursion to a `for`-loop
   with reverse-accumulation. Adds `Program.typeCheckIter` alongside
   the original `typeCheck`/`go` so `ProgramWF.lean` proofs survive
   by `induction decls` over the original shape; switches three
   call sites in `Core.lean`, `CoreToCProverGOTO.lean`,
   `CoreToGOTOPipeline.lean` to `typeCheckIter`.
2. **`refactor(transform): iterativize TermCheck.transformDecls`**
   (`f3f409c66` → cherry-picked as `7b1018e81`). Splits per-decl
   logic into `processOneDecl`, drives with a for-loop building the
   result in reverse and reversing once at the end.
3. **`refactor(transform): iterativize PrecondElim.transformDecls`**
   (`869d59f30` → cherry-picked as `73c17b1bd`). Same pattern as
   TermCheck. The empirical hot walker for sce1 — pre-fix this one
   was the dominant SIGABRT source at N≈30K-50K.
4. **`perf(transform): O(N) runProgram walker`** (`438052e86` →
   cherry-picked as `fab1575f8`). Rewrites `runProgram` in
   `Strata/Transform/CoreTransform.lean` to use index-tracked
   replacement instead of `List.set`-based search-and-replace, going
   from O(N²) to O(N).

   **Follow-up fix (`1dfa61e1f`).** The cherry-picked O(N) refactor
   regressed `StrataTest/Transform/ProcedureInlining.lean:515`: the
   refactor deferred `currentProgram` state updates to end-of-walk,
   but `ProcedureInlining.inlineCallCmd` reads `currentProgram`
   mid-walk to look up callee bodies and updates the cached
   call-graph after each inline (line 297). With the deferred
   update, the cached and freshly-computed call-graphs diverged. The
   `CoreTransformState.currentProgram` contract docstring (lines
   106-109) is explicit: "currentProgram will store the latest
   versions of finished procedures." Fix: snapshot
   `acc.toList ++ tail` into `currentProgram` after each rewritten
   decl, where `tail` is the unprocessed suffix of `p.decls` rotated
   forward in lockstep with the loop. This restores the
   finished-prefix + unprocessed-suffix view the contract requires
   without paying O(N²) on every iteration — the snapshot is only
   O(N) when a decl is actually rewritten, matching the per-mutation
   cost the original pre-`fab1575f8` code paid. Caught by `lake test
   -- --exclude Languages.Python` post-cherry-pick; the other
   test failures observed (`CFGParseTests`,
   `Examples.Loops`, `ProcedureEvalCFGTests:127,140`) are
   pre-existing API drifts confirmed on the parent commit
   `c46c75e41`, not regressions.

**Result.** sce1 reaches a verdict at any reasonable N:
- N=30K: PASS in 7s (pre-fix: PASS in 7s — threshold not yet hit)
- N=50K: PASS in 23s (pre-fix: SIGABRT in 12s)
- N=100K: PASS in 38s (pre-fix: SIGABRT)
- N=200K: PASS in 144s (pre-fix: untested; presumed SIGABRT)
- N=500K: TIMEOUT at 10min, no SIGABRT (CPU-bound; performance
  ceiling, not a stack bug)

The 94-program SMACK portfolio under `--call-policy bodyOrContract
--inline-fuel 100 --check-level full --split-procs` is unchanged
from the pre-cherry-pick v6 baseline (68 PASS / 15 PASS-? / 11
PARTIAL). PARTIAL identities match exactly — no soundness regressions.

**Diagnostic recipe.** Pre-fix bisection used a one-line
`[phase-start]` log on the pipeline loop in `Verifier.lean:1177`,
gated on `--profile`, plus per-element `dbg_trace` inside the
suspect `transformDecls`. The instrumentation is described in
[`reports/stack-and-hang-conjectures-report.md`](../../reports/stack-and-hang-conjectures-report.md)
§5.

**Files:** `Strata/Languages/Core/DDMTransform/Translate.lean`
(translateCoreDecls), `Strata/Languages/Core/ProgramType.lean`
(typeCheckIter, typeCheckOne), `Strata/Languages/Core/Core.lean`
+ `Strata/Backends/CBMC/GOTO/CoreToCProverGOTO.lean` +
`Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean` (call-site
switches), `Strata/Transform/TerminationCheck.lean`,
`Strata/Transform/PrecondElim.lean`, `Strata/Transform/CoreTransform.lean`.
Net: 6 Lean files modified, +441 / -71 lines.

### 4.5 Balanced ITE-tree in obligation-program builder (`494cf1147`)

**Problem.** `Core.toCoreProofObligationProgram` combined per-obligation
statement blocks via a left-deep `foldl` of `Stmt.ite .nondet`,
producing AST depth proportional to the obligation count. The `foldl`
itself completes (it's TCO), but the *output AST* has depth = N. The
first downstream consumer that recurses structurally on `Stmt.ite`
arms (`ANFEncoder.anfEncodeBody` walking then-branch then else-branch)
overflows the OS C stack at moderate N. On `EQ_2aa5bx1uwko_out.bpl`
(smallest medium SO repro from the EQ portfolio), N = 2,857,392 →
SIGABRT at default 8 MB stack in ~15s; raising the stack 8× to 64 MB
defers but doesn't prevent the crash (~226s elapsed instead of 15s).

**Localization (4 probes, 2026-06-04..05).** dbg_trace counter
instrumentation pinned the depth-driver to the foldl-built ITE tree,
not to the eval-side recursion that initial triage suspected. Probe
3 measured `[ITE-FORK]=0` events fired before SIGABRT, falsifying the
"processIteBranches fork-explosion" hypothesis. Probe 4 traced
`[FOLD-DEFERRED] blocks=2857392` immediately preceding `[ENCODE-VC]
anfEncodeBody entered` and the SIGABRT, identifying `Core.lean:185-189`
as the depth-driver and `ANFEncoder.lean:197+` as the trigger site.

**Fix.** Replace the foldl with `balancedNondetIte`, a balanced-
bisection helper producing AST depth O(log N) ≈ 22 for N = 2.86M.
Preserves per-obligation path-condition isolation:
`ObligationExtraction.extractGo` still resets `pc` to the parent's
value when entering each `ite .nondet` arm, so siblings cannot leak
`assume` constraints into each other's path conditions. Flattening
the blocks to a single `List Stmt` (Option A in the probe-4 report)
would have been simpler but breaks pc isolation; balancing (Option B)
preserves the semantics of every existing consumer.

```lean
def balancedNondetIte (blocks : List (List Statement)) : List Statement :=
  match blocks with
  | [] => []
  | [b] => b
  | b₀ :: b₁ :: rest =>
    let bs := b₀ :: b₁ :: rest
    let mid := bs.length / 2
    [Imperative.Stmt.ite .nondet
      (balancedNondetIte (bs.take mid))
      (balancedNondetIte (bs.drop mid))
      .empty]
  termination_by blocks.length
```

**Result.** All 7 known SO reproducers from the EQ portfolio
(`EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe`, `EQ_2aa5bx1uwko`,
`EQ_wfgmxv3m3tx`, `EQ_sertrlracdg`, `EQ_0xaksnfuqqv`) cleared on
`htd/so-fix`: zero rc=134, zero "Stack overflow detected" stderr.
All 7 now hit the post-SO long-running SMT regime within
`gtimeout=90s` (rc=124) — acceptable behavior; SMT timeout is not a
verifier crash. 94-program SMACK matrix bit-identical PASS+PARTIAL
file sets vs the v6 baseline (68/11/0); 6 PASS-? → TIMEOUT shifts on
`sv_locks_*` are pre-documented probe variance, not fix-induced.

**Files:** `Strata/Languages/Core/Core.lean` (+29 / −5). Merged into
`htd/smack` as `346f55083`. Probe lineage at
`reports/so-localization-probe4-2026-06-05.md`.

### 4.6 Multi-`Env` return signature for `Command.eval` (`5648bdf62`)

Widened `Command.eval`, `Command.handleCall`, `Command.inlineCallContract`,
and `Command.inlineCallBody` from `Command × Env` to `Command × List Env`,
removing the single-env squeeze in `inlineCallBody` (the `.Misc` guard at
old commit `fa82fe42b`). Per-path envs now flow upward through `evalAuxGo`'s
active-path machinery and each path's assertions are evaluated independently;
`.BodyOrContract` falls back only on `OutOfFuel` / `.Misc`, so a multi-path
callee body is no longer a failure mode.

**Soundness, not throughput.** On the current 94-program SMACK matrix the
change is verdict-neutral (byte-identical 68 PASS / 15 PASS-? / 11 PARTIAL
under `--call-policy bodyOrContract --split-procs`): the one program the
design predicted would lift (`nondet_branch`) turns out to be a top-level
CFG case (`evalCFGStep`), not the callee fan-out the design assumed. The
value is removing the soundness gap — helper procedures whose body has a
symbolic `if` producing multiple result envs are now evaluated per-path
instead of squeezed to one. This supersedes the "Multi-branch body-eval
refused as soundness guard" framing in §9.6 #20.

**Regression test.** `StrataTest/Languages/Core/Tests/InlineCallBodyTests.lean`
Tests 7-9 (CFG-bodied callee with symbolic `condGoto`): reverting the eval
changes makes Tests 7 and 9 fail (`expected 2 envs, got 1`).

**Files:** merged into `htd/smack` at `5648bdf62`. Design:
`Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md`. A smack-docker matrix
demonstration (a `caller → helper(symbolic if) → assert` program) is
deferred — it needs SMACK to regenerate `.bpl` from a new `.c`, and SMACK
runs only inside the sandbox-blocked Docker image.

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
land at the deductive verifier (after fix §4.1 above) — the contracts
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

- `../../reports/strata-verify-stack-overflow-deeply-nested-expr.md` — `strata
  verify` SIGABRT on deeply nested `if-then-else`. Verified on
  origin/main (HEAD: `349b1cf49`); reproduces at depth ≈ 4100.
  Suspected location: `Translate.translateExpr` partial def
  recursion with no fuel.
- `../../reports/cbmc-inout-rename-collision.md` — original triage that led to
  fix 2.1.
- `../../reports/cbmc-timeouts-and-stale-expects-report.md` — RPO emission triage
  that led to fix 2.5.
- `../../reports/verifier-assume-synthesis-report.md` — investigation that led to
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
  (§4.2): structured callee under `.Body` (assertion reduces to
  `true`), structured callee under `.Contract` (assertion deferred
  against havoc'd fresh fvar), CFG callee under each policy, looping
  CFG under `.Body` low-fuel (surfaces `OutOfFuel`), looping CFG
  under `.BodyOrContract` low-fuel (falls back to contract).

### Multi-`Env` regression fixture: `EQ_vtepk5bv3ld_out.bpl`

A deterministic forward-witness for the multi-`Env` eval change (§4.6).
`REVE.triangularMod.Neq.SameV`, medium bucket. Pre-multi-`Env`, this file
stack-overflowed under `--call-policy contract` and timed out under
`--call-policy bodyOrContract`; post-multi-`Env` it passes both cleanly
(280 goals on contract, 1516 on bodyOrContract). Use to confirm multi-`Env`
hasn't been silently reverted: post-change produces `All 1516 goals passed`;
reverting eval to the pre-multi-`Env` squeeze makes contract policy
stack-overflow again. (Regenerating it requires the SMACK Docker image;
the `.bpl` is in the EQ corpus, not committed to `programs/`.)

`Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`
— `--smack` marker support: each `.bpl` test fixture may carry a
`{:smack}` annotation in its first 5 lines to opt into the
SMACK-specific accommodations under test. A regression test pins
the off-by-default behavior of `--smack`, and an extended
`SmackAssertDuplicateSpec` test covers the requires-already-present
case.

### CFGForm test surface

`StrataTest/Languages/Core/Examples/CFGForm/` mirrors each leaf in `StrataTest/Languages/Core/Examples/` through the `_CFGFormHelper.lean` shim (`verifyCFG = toCFGForm + Core.verify`). 40 `.lean` leaves × 102 `verifyCFG` blocks total. Post-cherry-pick of `437d38683` (PR #1342 / F1+F4 fix): **31/40 leaves green**, **81/102 blocks green** (≈79.4% verdict-preserving against the structured-form golden). 9 red leaves: `Cover` (F3 + #27 verdict-set divergence), `FunctionPreconditions_Part3` (F2 funcDecl drop, #26), `FunctionPreconditions_Part4` (loop-invariant OOM, #29), `ProcedureCall` (F3 cosmetic, #28), `RecursiveProcIte` (was F1, now F3 cosmetic — both arms ✅ post-fix), `SafeMap` (F3, #28), `SelectiveVerification` (F3, #28), `TypeDeclStmt` (F2 typeDecl drop, #26), `UnreachableAssert` (F3 cosmetic, #28). FunctionPreconditions monolithic leaf was hand-split into Part1/Part2/Part3/Part4 to avoid the OOM-killed (exit 137) failure mode — Part1+Part2 (9 blocks) now green; Part3 fails fast on F2; Part4 isolates `loopGuardPrecondPgm` and still hangs (workflow wpqfi3man investigating).

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

### 9.3 Strata Core / Transform (9)

| # | Bug | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 12 | `runProgram` skipped CFG bodies — call sites inside any CFG-bodied procedure had no `requires`-VCs generated; the verifier silently passed those call sites with vacuous PASS verdicts. **Largest single soundness improvement of the project so far.** | — (commit message documents) | ✓ `42ff8a4b8` | — |
| 13 | Contract-only call evaluation — every `.call` was replaced by `havoc(lhs); assume(ensures)`, losing all body-derived information. Caused the dominant deductive sub-class (a) PARTIALs (54 of 93). Resolved by the body-eval feature. | — (motivation captured in spec) | ✓ `dd0c0d7cd` (body-eval feature) | — |
| 14 | Cross-procedure `Env.error` contamination — when one procedure errors (CFG fuel exhaustion, etc.), `fixupError` doesn't clear `Env.error`; subsequent procedures short-circuit and emit zero obligations. **Confirmed today on `htd/smack`**: `aws_array_eq` reports `All 4 goals passed` end-to-end but `--procedures main` shows `0 goals passed, 3 failed`. The `--split-procs` workaround masks this, not fixes it. | [#1185](https://github.com/strata-org/Strata/issues/1185) (open) | — | — (fix lives on `htd/fix-eval` as `d55ac1c33` + `eeb0dfa3d` + `ecf402211`, not yet on either main or htd/smack) |
| 21 | CFG `condGoto` deferred-obligation duplication — both `env_t` and `env_f` of a symbolic-condition CFG branch inherited the parent's `deferred` array; every symbolic branch doubled the pre-split obligation set, growing multiplicatively across procedures (3.96B obligations on `cjson_cJSON_Parse_harness.bpl` after 7 procedures). Materializing the array hung `Program.eval` on every `.bpl` ≥20K lines, regardless of `--call-policy` or `--inline-fuel`. **Note: this supersedes Conjecture A in `reports/stack-and-hang-conjectures-report.md`, which attributed the hang to a depth-O(N) ITE chain in `oblProgram` — the actual mechanism is width-O(2^K) array growth in `deferred` *before* the ITE chain is constructed.** | [#1316](https://github.com/strata-org/Strata/issues/1316) (open) + PR [#1317](https://github.com/strata-org/Strata/pull/1317) targeting `htd/unstructured-procedure` | ✓ `8f019818f` (cherry-picked from `277c468cb` on `htd/smack-timeout-fix`) | — |
| 23 | `Core.toCoreProofObligationProgram` builds a left-deep `Stmt.ite .nondet` tree by `foldl` over the deferred-obligations list, producing AST depth = N (the obligation count). `ANFEncoder.anfEncodeBody`, the first downstream non-TCO consumer, walks then-branch then else-branch structurally and overflows the OS C stack. **Affects all 7 SO reproducers from the EQ portfolio** (`EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe`, `EQ_2aa5bx1uwko`, `EQ_wfgmxv3m3tx`, `EQ_sertrlracdg`, `EQ_0xaksnfuqqv`); on `EQ_2aa5bx1uwko` N = 2,857,392 obligations → 2.86M-deep ITE → SIGABRT in ~15s under default 8 MB stack, ~226s under raised 64 MB stack (depth grows with N regardless of stack budget). Probe-localized via 4 dbg_trace probes over 2026-06-04..05; original "processIteBranches fork-explosion" hypothesis was empirically falsified at probe 3 (`[ITE-FORK]=0`). Independent of `--call-policy`/`--inline-fuel`/SMT subprocess. **Fix: `balancedNondetIte` (depth O(log N) ≈ 22 instead of N) preserving per-obligation pc isolation that ObligationExtraction relies on.** Validation: 7/7 SO reproducers cleared (zero rc=134); 94-program SMACK matrix bit-identical PASS+PARTIAL file sets (68/11/0). **Probe-1 follow-up (2026-06-05):** end-to-end re-run of all 7 SO reproducers under realistic flag set (`--check-mode deductive --check-level minimal --call-policy bodyOrContract --inline-fuel 100`) at 120s wall budget — 7/7 hit 120s wall (rc=124) with zero-byte stdout/stderr. Translation succeeded (rc=0, 16-21s); verifier was still working silently when the wall clock killed it. Fix is **crash-suppressor only** for these 7 reproducers — SIGABRT eliminated, but end-to-end correctness on these particular files is not demonstrated; the crashes have been turned into silent timeouts. Follow-up under `--profile`, `--no-solve`, or 300-600s budget would discriminate "stuck in transform" from "stuck in solver." | not filed yet — bug requires `--call-policy bodyOrContract` which exists only on the htd/smack feature line (commit `dd0c0d7cd`); should ship alongside body-eval merge to main/main2 | ✓ `494cf1147` merged via `346f55083` | — |
| 25 | `Imperative.stmtsToCFG` `flushCmds` short-circuited unconditionally on `accum.isEmpty`, silently dropping any `tr?` override (e.g. `condGoto`). The `.ite` arm calls `flushCmds` with `.some condGoto`, so a fresh `if` arriving on an empty accum lost its conditional and the generated CFG referenced an undefined target label. The `.block` arm also returned the wrong entry on the relabeling branch, orphaning the wrapping accumulated block. Surfaced by the `verifyCFG` harness in `StrataTest/Languages/Core/Examples/CFGForm/` on 5 blocks: `RecursiveProcIte` (n_gt_100_postcond / n_le_100_postcond), `BinaryTreeSize/LenAppend`, `BinaryTreeSize/SizeIsLen`, `Cover/Test`, `MapBranching/testmap`. Fix patches both `flushCmds` (match on `tr?`, emit transfer-only block on empty accum with `.some tr`) and the `.block` relabeling branch (return `accumEntry` instead of `l`). Validated by re-running each leaf with `lake env lean`: RecursiveProcIte and MapBranching now produce ✅ pass on both arms with no `Entry label "ite_1" not found` errors. **Branch locality:** `flushCmds` itself lives in `Strata/Transform/StructuredToUnstructured.lean` (shared with main), but the `verifyCFG` harness exposing the bug is htd/smack-only. | upstream PR [#1342](https://github.com/strata-org/Strata/pull/1342) | ✓ `437d38683` (cherry-pick of PR #1342; **pushed to origin/htd/smack 2026-06-09**, `origin/htd/smack`@`8908eb668`) | — |
| 26 | `Imperative.stmtsToCFG` (in `Strata/Transform/StructuredToUnstructured.lean:72-77`) silently drops `.typeDecl _ _ :: rest` and `.funcDecl _ _ :: rest` Stmts from procedure bodies. Both arms recurse `stmtsToBlocks k rest exitConts accum` with the declaration thrown away; the source carries the comment *"Not yet supported, so just continue with `rest`."* Subsequent statements still reference the declared types/functions, but they are no longer in scope after the rewrite, so the type-checker rejects the post-rewrite program. **This is a soundness violation** — the rewrite produces a program with strictly different verdict from the original. Surfaced by the CFGForm harness on 5 blocks: `TypeDeclStmt` (`typeDeclStmt1`, `typeDeclStmt3`, `typeDeclStmt4`, `shadowTopLevelType`) trip the `.typeDecl` arm and emit `❌ Type checking error. Type T is not an instance of a previously registered type!`; `FunctionPreconditions_Part3/funcDeclPgm` (1 block) trips the `.funcDecl` arm with `addPositive` declared inline inside the procedure body, emitting `Cannot infer the type of this operation: addPositive`. Recommended fix per `reports/cfgform-9-mismatch-analysis-2026-06-08.md`: refuse to convert (option 1) — add a precondition check in `stmtsToCFG` that fails with a clear error rather than silently dropping. Aligned with the structured-to-unstructured proof's `simpleShape` predicate which already excludes these cases. | not filed yet — should be filed alongside the F1+F4 cherry-pick or as a follow-up | — | — |
| 27 | `evalCFGBlocks` at `Strata/Languages/Core/ProcedureEval.lean:133-148` prunes obligations from blocks whose entry path conditions are unsatisfiable: on `condGoto` with a derivably-false branch condition (e.g. `if (x < 0)` under `assume (x >= 0)`), the worklist driver effectively skips the unreachable block, so obligations inside it are never collected. The structured form `Statement.eval` instead emits all obligations with unreachable-path tags (`✅ pass (❗path unreachable)` for asserts, `❌ fail (❗path unreachable)` for covers). **Verdict-set divergence, not just a verdict-value divergence**: the CFG form drops the obligation set entirely, so users lose the unreachable-cover diagnostic. Surfaced by `Cover/reachCheckMixedPgm` (CFG drops 2 unreachable obligations: `unreach_assert` ✅ pass-unreachable and `unreach_cover` ❌ fail-unreachable, while the verdicts on the reachable obligations match). The closely-shaped `Cover/Test` program (`if (false)` literal-false branch with labels `unreachable_cover1`/`unreachable_cover2`/`unreachable_assert`) exhibits the same pruning class with 3 dropped obligations. **Triage open**: either (a) treat as cosmetic and accept CFG-form pruning + regolden, or (b) require `evalCFGBlocks` to track and emit unreachable-path obligations like `Statement.eval` does. **Branch locality:** htd/smack-only — `evalCFGBlocks` does not exist on main. | not filed yet | — | — |
| 28 | **F3 cosmetic CFG-vs-structured path-condition asymmetry (verdict-preserving).** Two compounding factors: (a) `StringGenState.gen` counter trajectory differs because the structured form runs through path-eval which generates fresh names along its merge path, while the CFG form generates fresh names per branch in straight-line eval — both deterministic but produce different counter values for the same logical obligation. (b) Path-condition assumption shape differs: structured-form ite emits `<label_ite_cond_<true|false>: cond>: <conditional-shadowed obligation>` while CFG-form `condGoto` at `Strata/Languages/Core/ProcedureEval.lean:113-114` emits `<cfgBranch_<true|false>: cond>: <direct path condition>`. Most diagnostic example: `UnreachableAssert` structured emits `Obligation: x == if z == false then x else y` while CFG emits `Obligation: x == y` — same logical content, simpler under CFG semantics. Affected blocks (5): `UnreachableAssert`, `RecursiveProcIte`, `ProcedureCall`, `SafeMap`, `SelectiveVerification` — all verify ✅ pass on both forms (verdict-preserving). **Recommended action:** regolden the CFGForm fixtures against CFG output with a short comment explaining the path-condition asymmetry; ~30 LoC of golden updates. Long-term option: verdict-only digest wrapper. **Branch locality:** htd/smack-only — `evalCFGStep` / `evalCFGBlocks` / `evalCFGBody` (`ProcedureEval.lean:85-160`) is htd/smack-feature; main has only structured eval. | not a bug, not filed | regolden pending | — |

### 9.4 Strata DDM / parser / type-checker (3)

| # | Bug | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 15 | Transitive type-synonym chain not resolved for comparison/arithmetic operators — `<=`, `<`, `>=`, `>`, `+`, `-`, `*`, `div`, `mod` panicked when operands had a synonym-of-`int` type (e.g. `ref := i64 := int`) | [#1148](https://github.com/strata-org/Strata/issues/1148) (closed; tracking) | ✓ `e94635f8a` | — |
| 16 | Type checker fails on nondet goto with undeclared `$__nondet_N`. **InferModifies cross-reference (2026-06-09):** `reports/inferModifies-investigation-2026-06-09.md` confirms an `InferModifies` pass cannot architecturally close lean4 #1331 — the affected procedures already correctly do not modify the offending globals; the fix has to be in the typecheck rule itself (`ProcedureType.lean:100-105` extends `mkOld` bindings beyond inout params) or in widen-modifies-by-decree on the translator side per BACKLOG.md #1331 entry. The 56 ELAB_FAILs (28%) and ~17 latent ELAB_FAILs in TIMEOUT (mem-capped EQ-200 sweep, 2026-06-06) all share this root cause. | [#1162](https://github.com/strata-org/Strata/issues/1162) (open; resolved on `htd/smack` per BoogieToStrata STATUS.md) | ✓ (referenced by translator change in `Tools/BoogieToStrata/`) | — |
| 24 | `Strata/DDM/Util/Decimal.lean` emitted decimal literals in scientific notation (`s!"{m}e{e}"`) when the exponent fell outside `[-5, 5]`. SMT-LIB does not accept scientific-notation literals; both default-options z3 4.16 and cvc5 1.3.3 reject `1e-15` as a parse / unknown-symbol error. Surfaced on `EQ_0exak45poxy_out.bpl` (`tsafe.normAngle.Neq.SameV`) as 261 spurious obligation FAILs all reading `Symbol 'e-15' not declared as a variable`. Affects any benchmark with scientific-notation floating-point constants — observed across `tsafe.*`, `bess.*`, and a subset of REVE families. **Was confounding both vacuous-PASS measurements (Probe 3 inflated PARTIAL counts on tsafe normAngle pair) and witness extraction (Tier 1 A3 — required hand-rewriting the literal in 0exak/s541 SMT2 inputs to get a default-z3 verdict).** Fix: drop the `[-5, 5]` exponent bounds and the scientific-notation fallback; always emit decimal-form literals SMT-LIB accepts. Validation (10-file before/after sample): 5/10 files improved (4 PARTIAL/TIMEOUT-with-e-noise → PASS, 1 TIMEOUT-with-e-noise → clean TIMEOUT), 0/10 regressed. | drafted at `strata-decimal-e15-emission-bug.md` (repo root), **not yet pushed/filed** — fix landed on side branch `htd/decimal-e15-fix` at `6f5e74fa6` (worktree `/Users/htd/Documents/Strata-decimal-e15-fix`); not yet merged into htd/smack | ✓ side-branch `6f5e74fa6` (not on htd/smack mainline yet) | — |

### 9.5 Strata `verify` runtime (3 — #17 open, #22 fixed via cherry-pick, #29 open)

| # | Bug | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 17 | Stack overflow / SIGABRT on deeply-nested expressions — reproduces at depth ≈ 4100 on `origin/main` HEAD. Manifested as `skipEscape_harness` SIGABRT in the deductive verifier. **Diagnosis corrected (2026-06-02):** original report cited `Translate.translateExpr` (Core translation). Empirical bisection localised the actual walker to **`elabExpr` cycle in `StrataDDM/StrataDDM/Elab/Core.lean:1694`** (DDM elaboration, *before* `Translate.lean` runs). Trampolining `translateExpr` was attempted and verified to have zero effect; a paren-strip experiment (`reports/elabexpr-paren-strip-experiment.md`) confirmed `elabExpr` is the dominant frame consumer. Worklist rewrite of the `elabExpr`/`runSyntaxElaborator`/`elabSyntaxArg` cycle estimated 8-12h. | drafted as `reports/strata-verify-stack-overflow-deeply-nested-expr.md` (intended for upstream filing) | — | — |
| 22 | Stack overflow / SIGABRT on long flat-list `prog.decls` (~30K-100K axioms) — `transformDecls` in `Strata/Transform/PrecondElim.lean` walked decls via direct list-recursion; `TermCheck.transformDecls` and `translateCoreDecls` overflowed at higher N. **Diagnosis corrected (2026-06-02):** original report cited `programToCST.mapM` (formatter path); the actual walkers are in `PrecondElim`, `TermCheck`, `translateCoreDecls`, plus `Program.typeCheck` (transformation + type-check pipeline). **Boundary scan (2026-06-02):** sce1 reaches a verdict at N=100K (38s) and N=200K (144s) post-fix; at N=500K strata is CPU-bound and times out at 10min without SIGABRT — performance ceiling, not a stack bug. The "residual walker" follow-up flagged in the experiment SUMMARY is not load-bearing. | report at `reports/stack-and-hang-conjectures-report.md` issue (1) section + `reports/issue-1-unblocking-2026-06-02.md` | ✓ `95abbe567`, `7b1018e81`, `73c17b1bd`, `fab1575f8` (cherry-picked from `htd/smack-tco-experiment` commits `a3fb64376`, `f3f409c66`, `869d59f30`, `438052e86`); follow-up `1dfa61e1f` restores mid-walk `currentProgram` visibility for ProcedureInlining's call-graph cache | — |
| 29 | `evalCFGBlocks` loop-with-invariant OOM on `FunctionPreconditions_Part4/loopGuardPrecondPgm`. **Root cause confirmed (census workflow `wqlj6z95v`, 2026-06-09):** `evalCFGBlocks` (`Strata/Languages/Core/ProcedureEval.lean:133-149`) is a **fuel-only worklist with no visited-set / fixpoint / back-edge awareness**, and `evalCFGStep` (`:106-130`) forks *both* successors on a symbolic `condGoto`, so it literally **unrolls** the reducible loop back-edge (`StructuredToUnstructured.lean:132` decrease block `.goto lentry`) until fuel runs out — heap grows one `Env` per pseudo-iteration. The structured path doesn't OOM because `LoopElim` runs an acyclic havoc-and-cut on `.loop` Stmts (`LoopElim.lean:125-203`); the CFG path never does (`:249` passes `.cfg` bodies through unchanged). **NOT an irreducibility problem** — census found 0 irreducible CFGs across all 3,767 procedures in the three corpora. Original monolithic `FunctionPreconditions.lean` leaf hit OOM (exit 137) at 147s; hand-split into Part1-4 (Part1+Part2 unblocked 9 blocks; Part3 fails fast on F2 funcDecl drop; Part4 isolates `loopGuardPrecondPgm` and still hangs). **Recommended fix: a CFG-level loop-elim pre-pass** (recover the loop contract from the header `condGoto`'s `specLoopInvariant`/`specDecreases` metadata at `StructuredToUnstructured.lean:146-151`, splice `LoopElim`'s acyclic recipe to remove the back-edge before `evalCFGBody`); verification path only, not the CBMC/GOTO path. See `reports/irreducible-cfg-census-2026-06-09.md` + BACKLOG.md. **Branch locality:** htd/smack-only — main has no `.cfg` body shape so `evalCFGBlocks` does not exist there. | not filed yet | — | — |

### 9.6 Pipeline-driver / matrix-display gaps (3 — not Strata bugs)

| # | Issue | Filed? | htd/smack | main/main2? |
|---|---|---|---|---|
| 18 | `run_pipeline.py` collapses `path unreachable` PASSes — six SV-COMP unsafe programs initially looked like soundness probes (`unsafe ∧ deductive=PASS`); each is actually `pass (path unreachable)`. Matrix-display gap, not soundness bug. | — | **fixed** — `run_pipeline.py` now emits `--check-level full` and surfaces vacuous discharges as `PASS-?` (uncommitted run_pipeline.py changes) | — |
| 19 | bugFinding partials dominated by `__VERIFIER_assume`-only failures — bugFinding under `bodyOrContract` produces zero verdict improvements (verified on full portfolio: 0/65 contract, 0/64 bodyOrContract). bugFinding's PARTIALs are about unconstrained inputs, not missing ensures. | — | — | — |
| 20 | Multi-branch body-eval refused as soundness guard — `Command.inlineCallBody` errors when a callee body produces multiple result envs. The single residual portfolio PARTIAL (`nondet_branch`) is this case. Design proposal exists for fork-and-continue (return `List Env`). | — | partial guard in `dd0c0d7cd`; design doc `Examples/smack-docker/MULTIPATH_COMMAND_EVAL.md` | — |

### Summary stats

- **29 distinct bugs/issues** surfaced (or confirmed) on this branch (24 → 29: +#25 F1+F4 `flushCmds` empty-accum dispatch drop fixed at `437d38683`; +#26 F2 `.typeDecl`/`.funcDecl` silent drop in `stmtsToCFG`; +#27 `evalCFGBlocks` unreachable-arm obligation pruning on `Cover/reachCheckMixedPgm`; +#28 cosmetic CFG-vs-structured path-condition asymmetry; +#29 `evalCFGBlocks` loop-with-invariant OOM on `FunctionPreconditions_Part4`).
- **20 fixed on htd/smack** (was 19; #25 lands locally at `437d38683`, **not yet pushed to origin**).
- **1 fixed on side branch, draft-ready** (#24 SMT2 e-15 emission fixed on `htd/decimal-e15-fix` at `6f5e74fa6`; issue draft at `strata-decimal-e15-emission-bug.md`; not yet pushed, filed, or merged into htd/smack).
- **1 fixed elsewhere** (#14 fix lives on `htd/fix-eval`; not on `htd/smack` or `main`).
- **6 not yet patched** (#1184, #1186, #17 deeply-nested-expr `elabExpr` rewrite, #26 F2 silent drop, #27 unreachable-arm pruning triage, #29 evalCFGBlocks loop OOM under wpqfi3man).
- **1 filed upstream from htd/smack** (#1331, BoogieToStrata `old(<unmodified-global>)` typecheck rejection; reproduces on `origin/main2@4e4ceb9d1`; `InferModifies` ruled out architecturally per `reports/inferModifies-investigation-2026-06-09.md`).
- **0 fixes have landed on `main` or `main2`** — every CBMC-backend, BoogieToStrata, and Core-transform fix is still `htd/smack`-only.

### Filed-issue index

- **Open and unresolved on main:** #1184, #1185, #1186, #1198, #1162.
- **Closed (tracking-issue):** #1148 (BoogieToStrata blockers — its sub-issues are addressed by branch fixes).
- **Drafted but unfiled:** `../../reports/issue-2-elabexpr-overflow-upstream-filing.md` (issue 2; self-contained upstream-filing artifact ready), `../../reports/cbmc-inout-rename-collision.md` (predates the actual #1198 filing), `../../reports/cbmc-timeouts-and-stale-expects-report.md`, `../../reports/verifier-assume-synthesis-report.md`. Older issue-2 drafts (`strata-verify-stack-overflow-deeply-nested-expr.md`, `elabexpr-paren-strip-experiment.md`) are retained as triage history; superseded by the upstream-filing artifact. The `reports/INDEX.md` page is the canonical entry point.

### Path to upstream

Every fix on this branch is currently `htd/smack`-unique. None has reached `main` yet. Upstream-landing dependencies:

1. The **8 CBMC GOTO backend fixes** depend on `htd/unstructured-procedure`'s CFG-Procedure work (in flight).
2. The **BoogieToStrata fixes** are tied to PR #1149.
3. The **Core-transform fixes** (`42ff8a4b8`, `dd0c0d7cd`) depend on CFG-eval which is in `htd/unstructured-procedure`.
4. The **#14 fix** (cross-procedure `Env.error`) lives on `htd/fix-eval` — most independent of all; could land directly on `main` and be back-merged.
5. The **#21 fix** (CFG `condGoto` deferred-dedup, commit `277c468cb`) is on `htd/smack`; can land upstream directly with no dependency.
6. The **#22 fix** (long flat-list overflow) is on `htd/smack` (cherry-picks `95abbe567`, `7b1018e81`, `73c17b1bd`, `fab1575f8`). 94-program SMACK matrix matches v6 baseline exactly post-cherry-pick (no soundness regressions). Independent of upstream PRs; can land directly on main.
7. The **#17 fix** (deeply-nested-expr `elabExpr` rewrite) is not yet attempted; estimated 8-12h on a critical mutual block in `StrataDDM`.

The branch is a substantial body of fix work. Most of it is upstream-able once the underlying PRs (`htd/unstructured-procedure`, #1149) merge.

---

## Summary table

| Metric | origin/main | htd/smack |
|---|---:|---:|
| Pipeline programs (`Examples/smack-docker/programs/*.c`) | 0 | 94 |
| Strata CBMC backend bugs fixed | 0 | 8 |
| Strata Core / Transform fixes | 0 | 3 (CFG-bodied CallElim, body-eval at call sites, CFG `condGoto` deferred-dedup) |
| BoogieToStrata SMACK-specific features | 0 | 4 (`--smack` flag, `assert_.<type>` requires, `__VERIFIER_assume` ensures, `__VERIFIER_assert` requires) |
| Contract-ported coreJSON harnesses | 0 | 9 |
| Cross-validation backends | 0 | 4 (deductive, bugFinding, Strata-CBMC, cbmc-native) |
| Strata defects identified by cross-validation | 0 | 5 (4 fixed; 1 stack-overflow filed) |
| Cross-validation matrix | none | 94-program 4-backend (64 portfolio + 29 SV-COMP + picohttpparser); v6 deductive: 68 PASS / 15 PASS-? / 11 PARTIAL under `--call-policy bodyOrContract --inline-fuel 100 --check-level full --split-procs` |

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
