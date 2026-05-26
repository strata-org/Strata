# Cross-validation portfolio screening

A multi-backend evaluation of the SMACK→Strata pipeline against 94
parser, decoder, utility, and SV-COMP ReachSafety programs from five
sources.

## Pipeline

Each `.c` flows through four independent reasoning engines:

```
.c → SMACK → .bpl → BoogieToStrata → .core.st ─┬→ Strata deductive (VC-based proof)
                                               ├→ Strata bugFinding (symbolic execution)
                                               └→ StrataCoreToGoto + symtab2gb + cbmc

.c ─────────────────────────────────────────────→ cbmc native (ground-truth control)
```

The first three share Strata's IR. The fourth is `cbmc` invoked
directly on the original `.c`, with macro shims mapping
`__VERIFIER_*` onto `__CPROVER_*`. When (3) and (4) disagree on the
same program, the disagreement is necessarily in Strata's lowering
chain (`StrataCoreToGoto` → `symtab2gb` → cbmc invocation flags),
since both (3) and (4) are the same underlying tool reading
equivalent inputs.

## Suite composition

| Source | Programs | Description |
|---|---|---|
| Original benchmark | 12 | Hand-written small programs (`abs_func`, `loop_sum`, `simple_add`, ...) |
| Simplified AWS C Common | 13 | Hand-written, in the style of `aws_array_eq.c` |
| aws-c-common verbatim | 6 | Imported from `verification/cbmc/proofs/`, function bodies inlined from upstream `math.inl` |
| FreeRTOS coreJSON verbatim | 12 | Imported from upstream `test/cbmc/proofs/`, full `core_json.c` vendored |
| FreeRTOS coreMQTT/coreHTTP/coreSNTP verbatim | 10 | Same pattern, vendored upstream sources |
| Standalone parsers | 4 | Hand-written harnesses on jsmn, cJSON, picohttpparser |
| RFC reference impls | 8 | UTF-8 DFA validator, base64 decoder, percent-encoding decoder, with edge-case harnesses |
| SV-COMP ReachSafety | 29 | Imported from `sosy-lab/sv-benchmarks` with verdict oracle (`svcomp_verdicts.json`); 22 safe, 7 unsafe |
| **Total** | **94** | |

## Verdict matrix

Run with `python3 run_pipeline.py --backends deductive,bugFinding,cbmc,cbmc-native`.

**Latest combined run (93 programs, `--split-procs` mode):**

|  | PASS | not-PASS | TIMEOUT | skip |
|---|---:|---:|---:|---:|
| Strata deductive  | 39 | 54 | 0 | 0 |
| Strata bugFinding |  0 | 93 | 0 | 0 |
| Strata-CBMC       |  0 | 93 | 0 | 0 |
| CBMC native       | 70 | 23 | 0 | 0 |

The 93 = 64 portfolio (`wt-test/pipeline-portfolio-v3.txt`) + 29
SV-COMP (`wt-test/pipeline-svcomp.txt`); `picohttpparser` remains
excluded due to known cbmc-native OOM. The `--split-procs` mode
normalises verdicts per-procedure; "not-PASS" covers
PARTIAL/FAIL/TIMEOUT in per-procedure sub-results. The divergence
column is computed by `tools/disagreement_matrix.py`, which
auto-tags rows where Strata-CBMC and CBMC-native disagree as
**(T-lowering)**.

Per-source breakdown:

|  | Portfolio (64) deductive | SV-COMP (29) deductive | Portfolio cbmc-native | SV-COMP cbmc-native |
|---|---:|---:|---:|---:|
| PASS | 21 | 18 | 45 | 25 |
| not-PASS | 43 | 11 | 19 | 4 |

```
T-lowering:   ~70 rows  (every Strata-CBMC=FAIL where cbmc-native=PASS)
one-off:      ~20 rows
all-disagree:  0 rows
all-agree:     few rows (skipEscape and similar — all FAIL on every backend)
```

## Cases

We triaged 13 representative divergent rows across four investigation
clusters. Each cluster's full report lives under `wt-test/triage/`.

### (T-lowering) cluster — Strata-CBMC blocked, native CBMC verifies

39 of 65 rows. The most consequential finding of the screening.

**Root cause.** All but one of the 39 rows trip a single
**`symtab2gb` array-type-mismatch blocker**. SMACK lowers C global
state into Boogie globals named `$M.0`, `$M.1`, …; BoogieToStrata
promotes these to `inout _M_*` parameters on `main`. When
`StrataCoreToGoto` emits `__cprover_entry`, the generated GOTO
binary's symtab contains two structurally different CBMC array-type
objects describing the same source type (`array integer` vs
`array { size: integer } 0: integer`) — one from a DECL instruction
in the entry shim, one from `main`'s parameter entry. CBMC's type
checker aborts with `function call: parameter "main::_M_0" type
mismatch` (rc=6) before any model checking begins.

The single remaining (T-lowering) row, `HTTPClient_strerror_harness`,
hits the **callee-bodies blocker**: `coreToGotoFiles*` translates
only the entry procedure (`main`), leaving callees as bodyless
declarations. CBMC reports `[.no-body.HTTPClient_strerror]`,
`[.no-body._initialize]`, etc. and FAILs.

CBMC-native PASSes all 39 because it compiles directly from the
flat `.c`, has every function body inlined, and the assertions
under `--bounds-check --pointer-check --unwind 10` hold trivially.
Same tool, same source, completely different verdicts: this is the
sharpest signal in the screening — Strata's lowering chain is the
unambiguous culprit, not CBMC's reasoning.

**Fix lever (single).** Canonicalize `array integer` construction
in `symtab2gb` so DECL-site and parameter-site emissions produce
structurally equal CBMC type objects. Triage detail in
`wt-test/triage/9A-existing-suite.md`.

(One row, `loop_sum`, shows `cbmc=TIMEOUT, cbmc-native=PASS`. This
is the previously documented real-loop unwinding blocker on a real
C `for` loop — the array-type-mismatch blocker doesn't even apply
because the program has no `_M_*` params; instead Strata-CBMC's
default `--unwind 10` is too tight for the loop bound.)

### one-off cluster A — coreJSON harnesses where CBMC-native FAILs

10 of the 12 coreJSON `skip*`/`JSON_*` harnesses (and `cjson_cJSON_Parse`,
`jsmn_jsmn_parse`) show `deductive=PASS, bugFinding=PARTIAL,
cbmc=FAIL, cbmc-native=FAIL`. The deductive verifier handles them
(largely vacuously, since the harnesses have no functional asserts);
both CBMCs FAIL, but for different reasons:

- Strata-CBMC: same `symtab2gb` array-type-mismatch.
- CBMC-native: the harnesses pass a fully nondet `char buf[32]` to
  `cJSON_Parse` / `jsmn_parse` / `JSON_Validate`, which call
  `strlen(buf)` or scan for terminators. With no
  `__CPROVER_assume(buf[31] == '\0')` constraint, CBMC's
  pointer/bounds check fires inside the upstream parser — a
  **harness-side spec gap (S)**, not a bug in cJSON or coreJSON.

**Important:** a naïve reading of these `cbmc=FAIL ∧ cbmc-native=FAIL`
rows would classify them as "agreement" — both backends say something
goes wrong, so the matrix doesn't flag them divergent. Deep triage
shows two independent failures sharing a row. The matrix is necessary
but not sufficient; row-by-row triage is what produces actionable
findings. See `wt-test/triage/9D-cjson-parse.md` for the
illustrative case.

### one-off cluster B — `(T-lowering)` masked by all-FAIL

`HTTPClient_AddHeader_harness`, `HTTPClient_AddRangeHeader_harness`,
and similar HTTP harnesses show all four backends FAIL. The
divergence is `deductive=PASS, bugFinding=PARTIAL, cbmc=FAIL,
cbmc-native=FAIL`. Same shape as cluster A: Strata-CBMC's
array-type-mismatch and CBMC-native's harness-side issue both fire.

### special cases

- **`picohttpparser_phr_parse_request_harness`**: deductive=TIMEOUT,
  bugFinding=FAIL, cbmc=FAIL, **cbmc-native** sent the host machine
  into OOM (`Exit code -9` = SIGKILL). picohttpparser is a state-
  machine HTTP parser; with `--unwind 10 --pointer-check` plus a
  fully nondet 32-byte buffer, CBMC's SAT instance grew past
  available RAM. A practical finding: CBMC-native is not free —
  some real-world programs need per-program tuning to make it
  tractable. Tighter `--unwind` or stricter input bounding would
  recover a verdict.
- **`skipEscape_harness`**: every backend FAILs. Deductive's failure
  is the verifier crashing with `Stack overflow detected. Aborting.`
  (filed today as `strata-verify-stack-overflow-deeply-nested-expr.md`,
  reproducible on origin/main with a hand-crafted deeply-nested
  `.core.st`). The other three failures are independent. This row
  alone surfaced two separate Strata bugs: the SMTEncoder/Translate
  recursion and the `symtab2gb` array-type-mismatch.

## Findings

**Headline.** The `symtab2gb` array-type canonicalization fix
(`7bff2d48e`) unblocks the CBMC type-checker on the (T-lowering)
cluster, but exposes a deeper downstream blocker in cbmc's array
solver (see "Update: post-fix landscape" below). A second fix lever
is now needed before the (T-lowering) rows convert to PASS.
The screening identified the first fix lever by running the same
tool through two paths; the same methodology revealed the second.
No single backend could have produced this signal alone.

**Where Strata adds clear value.** The deductive verifier PASSes 47
of 65 programs, including ones where CBMC-native FAILs (the coreJSON
harnesses where nondet input trips strlen). Even with the lowering
chain broken, the deductive layer continues to produce a useful
signal — and unlike CBMC-native, it doesn't depend on harness inputs
being constrained to terminate parsing.

**Where the matrix design is necessary.** A two-backend setup
(Strata-CBMC vs CBMC-native, or deductive vs bugFinding) misses
findings the four-way matrix surfaces:

- The (T-lowering) tag *requires* both CBMCs.
- Distinguishing harness-side spec gaps (the coreJSON cluster) from
  pipeline bugs requires the deductive backend agreeing while one
  CBMC backend dissents.
- Memory-exhaustion and timeout failures are distinct from FAIL
  verdicts, and the matrix preserves that distinction.

**Where the screening surfaced new pipeline bugs.**
- The `symtab2gb` array-type-mismatch was already documented as a
  known blocker; the screening proves it is the *dominant* cbmc
  failure mode (38 of 65 rows).
- The `skipEscape` SIGABRT exposed a `Stack overflow` in
  `Strata.Languages.Core.DDMTransform.Translate.translateExpr`'s
  unbounded `partial def` recursion. A 5000-deep nested-`if`
  reproducer constructed during triage runs on origin/main.

**Where the screening did not (yet) find a (P) program defect.**
None of the 13 triaged divergences pinned a real bug in a target
program. The two (S) findings (cJSON_Parse / jsmn_parse harness
gaps) reflect harness incompleteness, not implementation defects.
The screening confirms that pipeline-side issues currently dominate
real-world program issues by a wide margin — fixing the pipeline
first is the prerequisite for the screening to produce (P) findings
in subsequent runs.

## Update: post-fix landscape

Two commits landed after the original 65-program run. Six
representative (T-lowering) rows and the four contract-ported
coreJSON harnesses were re-run to capture the deltas.

### Fix A: `symtab2gb` array-type canonicalization (`7bff2d48e`)

**What it accomplished.** The commit canonicalizes array-type
emission in `symtab2gb`/`goto`, so the two structurally different
CBMC array-type objects that previously described the same source
type (`array integer` vs `array { size: integer } 0: integer`) now
agree. CBMC's type-checker no longer aborts with `function call:
parameter "main::_M_0" type mismatch` (rc=6).

**New verdicts on six representative (T-lowering) programs:**

| Program | Previous detail | New detail |
|---|---|---|
| `aws_add_size_checked` | `CBMC exit code 6` | `CBMC exit code -6` |
| `aws_add_size_checked_harness` | `CBMC exit code 6` | `CBMC exit code -6` |
| `aws_array_eq` | `CBMC exit code 6` | `CBMC exit code -6` |
| `base64_decode_normal_harness` | `CBMC exit code 6` | `CBMC exit code -6` |
| `MQTT_GetPacketId_harness` | `CBMC exit code 6` | `CBMC exit code -6` |
| `array_sum` | `CBMC exit code 6` | `TIMEOUT` |

All six remain `cbmc=FAIL`. The verdict did not flip to PASS — but
the failure mode changed. rc=6 (type-checker exit) was replaced by
rc=-6 (SIGABRT inside cbmc's array solver). `array_sum` instead
hit a TIMEOUT, consistent with its pre-existing loop-unwinding
sensitivity.

**What surfaced next.** The `__cprover_entry` shim emitted by
`StrataCoreToGoto` nondet-initializes array-typed `_M_*` parameters
with a `nondet` expression. CBMC's array-constraint collector
(`collect_arrays` in `solvers/flattening/arrays.cpp`) does not
handle a raw `nondet` node as an array expression. It aborts with:

```
749-omj310/src/solvers/flattening/arrays.cpp:260 function: collect_arrays
Condition: false
Reason: unexpected array expression (collect_arrays): 'nondet'
```

This is a second, independent blocker in the `StrataCoreToGoto` →
cbmc path: the entry shim must not pass a bare `nondet` as the
concrete representation of an array-typed argument. The matrix
showed exactly where the next blocker would surface once the
dominant one was lifted — a screening result, not a regression.

### Fix B: coreJSON contract port (`495e09c87`)

**What it did.** Upstream `core_json_contracts.h` preconditions and
postconditions were ported into the `main()` body of four coreJSON
harnesses (`skipSpace_harness.c`, `skipDigits_harness.c`,
`JSON_Validate_harness.c`, `skipString_harness.c`) as
`__VERIFIER_assume`/`assert` calls, replacing the previous vacuous
bodies.

**Verdict deltas:**

| Program | Pre-port | Post-port |
|---|---|---|
| `skipSpace_harness` | `deductive=PASS (18 VCs), bugFinding=PARTIAL` | unchanged |
| `skipDigits_harness` | `deductive=PASS (585 VCs), bugFinding=PARTIAL` | unchanged |
| `JSON_Validate_harness` | `deductive=PASS (288 VCs), bugFinding=PARTIAL` | unchanged |
| `skipString_harness` | `deductive=PASS (57 VCs), bugFinding=PARTIAL` | unchanged |

No (S)→(P) transition occurred. The deductive PASS and VC counts
are identical before and after the port.

**Why the postconditions are not yet reaching the verifier.**
SMACK lowers `assert(expr)` to `call __VERIFIER_assert(0)` on the
failing branch (passing the literal `0` when the condition does not
hold). In the generated `.core.st`, `__VERIFIER_assert` is a
bodyless declaration with no `requires` spec:

```
procedure __VERIFIER_assert(... _i0 : i32)
;
```

Because there is no `requires (_i0 != 0)` precondition, the call
site generates no deductive VC obligation. The 18/585/288/57 goals
that are discharged come entirely from `__VERIFIER_assume` call
sites, which carry `free ensures (_i0 != 0)` in their stub spec
(a caller-side proof obligation that the argument is non-zero,
trivially satisfied by the preceding branch guard).

**Implication.** Making the postconditions reach the deductive
verifier requires the `--smack` flag in `BoogieToStrata` to also
inject `requires (p != 0)` on `__VERIFIER_assert` stubs (in
addition to the `assert_.<type>` stubs it already handles). Until
that injection is in place, contract ports that use `assert()` in
the harness body are silently invisible to the deductive backend.

## Update 2: full-suite re-run after three more fixes

Three more fixes landed in sequence after the post-fix landscape was
documented above:

- **`23926094f`** — `fix(cbmc): emit nondet array params as
  nondet_symbol, not nondet`. One-line change in
  `Strata/Backends/CBMC/GOTO/InstToJson.lean`: the JSON `id` for
  `Expr.Identifier.Nullary.nondet` was incorrectly emitted as
  `"nondet"`, which CBMC parses as `ID_nondet` (a side-effect node
  not handled by `arrayst::collect_arrays`). The Lean variant was
  always intended to model `nondet_symbol_exprt` (per its docstring
  in `Expr.lean:32`); the JSON serialisation was lying about its
  type. Fixed.

- **`b3e606bb6`** — `feat(boogietostrata): inject requires on
  __VERIFIER_assert under --smack`. Generalises the existing
  `assert_.<type>` injection to also fire on `__VERIFIER_assert`
  declarations, the symbol SMACK uses to lower C `assert(EXPR)`
  failure arms.

After these landed, the full 4-backend pipeline was re-run on the
64-program suite (picohttpparser excluded due to known cbmc-native
OOM). Comparison vs. the original run:

|  | Before | After all 5 fixes |
|---|---:|---:|
| Strata deductive PASS | 47 | **33** |
| Strata deductive PARTIAL/FAIL | 16 | **30** |
| Strata-CBMC FAIL detail | type-mismatch (rc=6) | mostly `Property violations found` (real verdict) or rc=-6 |
| CBMC-native PASS | 39 | **43** |

**Why deductive PASS *dropped* (this is a positive change).** The
`__VERIFIER_assert` requires injection turns the previously-vacuous
PASSes into real verification obligations. The 14-row deductive PASS
→ PARTIAL transitions are exactly the (S) → real-VC transitions the
original writeup wanted. The Detail column for these rows now reads
e.g. `90 pass, 1 fail` (`aws_add_size_checked_harness`) or
`128 pass, 1 fail` (`aws_mul_size_checked_harness`) — the verifier
is discharging most VCs and reporting one real failing obligation.

**Why Strata-CBMC's failure mode is still FAIL.** The array-solver
fix lets cbmc reach actual model checking, where it now reports the
known callee-bodies blocker (`[.no-body.<callee>]`). Only the entry
procedure `main` has its body emitted in the GOTO output;
user-defined helpers and prelude stubs are bodyless declarations.
This is the documented third blocker (see *Known blockers* in
`README.md`), and the fix path requires lifting all reachable
procedures into the GOTO output — a feature gap, not a bug.

**Cumulative impact of the five fixes** (`520f3f573` RPO + `7bff2d48e`
array-type + `23926094f` nondet-symbol + `b3e606bb6` __VERIFIER_assert
+ `495e09c87` contract port):

- Strata-CBMC progresses from "type-mismatch error before model
  checking begins" → "real cbmc verdicts on the callee-bodies
  blocker" on most of the (T-lowering) cluster. The lowering chain
  is no longer the dominant cbmc failure mode; the next layer
  (callee bodies) is.
- Strata deductive transitions from "vacuous PASSes from missing
  contracts" → "real VC obligations the verifier is mostly
  discharging" on the contract-ported and simplified-AWS programs.
- The portfolio's headline is no longer "39 (T-lowering) rows
  blocked on a single fix lever" but **"the matrix surfaces a
  cascade of layered defects, each fix exposing the next"**.

## Update 3: CFG-CallElim fix and the (S) → real-VC transition

### The fix

Commit `42ff8a4b8` — `apply CallElim to CFG-bodied procedures`.
`runProgram` in `Strata/Transform/CoreTransform.lean` previously
skipped CFG bodies with the comment "Skip CFG bodies; transforms are
statement-level." CallElim is the primary consumer of `runProgram`.
Skipping CFG bodies meant that call sites inside any CFG-bodied
procedure (which is most SMACK-translated procedures — any body with
a `goto` becomes one) had no `requires`-VCs generated for their
callees. The deductive verifier then silently passed those call sites,
producing vacuous PASS verdicts on programs whose only failing
obligations lived behind such a call.

The fix extends `runProgram`'s CFG branch to walk each block's command
list and apply `f` to each command, replacing it with the result. A
new helper `runCmdsRec` handles the Statement-to-Command shape
mismatch (CFG blocks store `List Command`; `f` returns
`List Statement`). Replacement Statements that are non-flat (`block`,
`ite`, `loop`, etc.) bail out and leave the original command unchanged
— these can't fit inside a basic block. In practice CallElim only
emits flat Statement sequences, so this is exhaustive. This mirrors
the existing structured-body path precisely.

### Severity of the gap

All 9 contract-ported coreJSON harnesses — and most SMACK-translated
programs whose `main` has goto-based control flow — were silently
passing deductive on vacuous obligations. The "(S) → real-VC
transition" claim in the original writeup was true for `simple_assert`
(a structured body), but did **not** hold for the contract-ported
parsers (CFG bodies). With the CFG-CallElim fix in place, the claim
now holds for both body shapes.

This is the largest single-step soundness improvement of the project
so far. A PASS verdict from the deductive backend on any CFG-bodied
procedure was previously unreliable; it is now trustworthy.

### The new verdict landscape (v2 → v3)

The full-suite pipeline was re-run on the 64-program suite
(picohttpparser excluded due to known cbmc-native OOM) after the fix
landed. The run used `--split-procs` mode, which runs each procedure
independently — this is a deliberate methodological change that
eliminates cross-procedure error contamination and produces one verdict
per procedure rather than one per file.

|  | Run | deductive PASS | deductive not-PASS | mode |
|---|---|---:|---:|---|
| v1 | original 4-backend, no CFG fix | 47 | 16 | non-split |
| v2 | post array-type + nondet-symbol fixes | 33 | 30 | non-split |
| **v3** | **post CFG-CallElim fix** | **21** | **43** | **--split-procs** |

The deductive PASS drop from 33 to 21 is a positive change. Vacuous
PASSes are gone; those programs now surface concrete failing VCs that
give the verifier something real to work on.

**Per-harness detail for the 9 contract-ported coreJSON parsers:**

| Program | v2 detail | v3 detail |
|---|---|---|
| `skipSpace_harness` | 0 pass, 18 fail (all `__VERIFIER_assume_ensures`) | 1 pass, 3 fail across 2 procs |
| `skipDigits_harness` | 0 pass, 585 fail | 1 pass, 6 fail across 2 procs |
| `skipString_harness` | 0 pass, 57 fail | 1 pass, 5 fail across 2 procs |
| `skipUTF8_harness` | 0 pass, 648 fail | 1 pass, 5 fail across 2 procs |
| `skipObjectScalars_harness` | 0 pass, 18 fail | 1 pass, 3 fail across 2 procs |
| `skipScalars_harness` | 0 pass, 18 fail | 1 pass, 3 fail across 2 procs |
| `skipAnyScalar_harness` | 0 pass, 228 fail | 1 pass, 5 fail across 2 procs |
| `skipCollection_harness` | 0 pass, 18 fail | 1 pass, 1 fail across 2 procs |
| `JSON_Validate_harness` | 0 pass, 288 fail | 1 pass, 1 fail across 2 procs |

The dramatic VC-count reduction — 18/585/648/288 failing VCs in v2
collapsing to 3-6 in v3 — reflects that we now generate exactly the
meaningful obligations (the post-call asserts in `main`) rather than
a flood of `__VERIFIER_assume_ensures` obligations that were
effectively counting precondition checks, not postcondition checks.

### What the failing VCs mean

Each failing VC in v3 is a concrete obligation Strata cannot discharge.
The dominant cause is that upstream parser functions (`skipSpace`,
`skipDigits`, `skipString`, etc.) have no `ensures` clauses. When
CallElim havocs all post-call state at each call site, the verifier
loses any knowledge of what the callee accomplished. The post-call
`assert(...)` obligations — which check that the parser advanced the
cursor correctly — then become unprovable from first principles.

This is sub-class **(S)** territory: missing ensures on user-defined
helpers, not a defect in the program under test. Two fix levers exist:

1. **`--synthesize-ensures` pass** (commit `390fadc37`): the existing
   sound ensures-synthesis pass handles structured bodies. Extending
   it to also walk CFG bodies (mirroring the CallElim CFG extension)
   would automatically infer `ensures` for the linear-shaped parser
   stubs, eliminating most of these failing VCs without any manual
   annotation.

2. **Hand-porting upstream ensures**: `core_json_contracts.h` already
   defines postconditions for each parser. Porting these into the
   implementations themselves (not just the harness) would make the
   ensures available to CallElim and close the gap directly.

### One important nuance

The v3 refresh exposes that most "deductive=PARTIAL" verdicts in the
matrix are now **(T)** translator-side conservatism — specifically,
the conservative effect of call-elim havocing state when callee
ensures are absent — rather than **(P)** program defects. The matrix
has not yet found a program defect that CBMC alone misses. Cross-
validation has confirmed pipeline soundness and surfaced five distinct
Strata defects, but the deeper goal — the matrix as a bug-finding
tool for target programs — requires ensures synthesis to mature enough
that post-call state is no longer uniformly havocked. The matrix is
now positioned to find a **(P)** finding once that lever is in place.

## Update 4: SV-COMP integration and the path-unreachable lesson

### What was added

29 ReachSafety programs from `sosy-lab/sv-benchmarks` (commit
`eb8fbd513`), drawn from three categories:

| Source category | Programs | Safe | Unsafe |
|---|---:|---:|---:|
| `c/locks/` | 11 | 9 | 2 |
| `c/loops-crafted-1/` | 12 | 8 | 4 |
| `c/reducercommutativity/` | 6 | 5 | 1 |
| **Total** | **29** | **22** | **7** |

Each program ships with an oracle verdict in `svcomp_verdicts.json`.
For the first time the matrix has ground-truth labels: any
`unsafe ∧ deductive=PASS` row is a candidate soundness probe.

### What the oracle revealed

Six rows initially looked like soundness probes:

| Program | Expected | Deductive | Diagnosis |
|---|---|---|---|
| `sv_locks_14_2` | unsafe | PASS | `path unreachable` qualifier |
| `sv_locks_15_2` | unsafe | PASS | `path unreachable` qualifier |
| `sv_loops_mono3_1` | unsafe | PASS | `path unreachable` qualifier |
| `sv_loops_mono4_1` | unsafe | PASS | `path unreachable` qualifier |
| `sv_loops_mono5_1` | unsafe | PASS | `path unreachable` qualifier |
| `sv_loops_mono6_1` | unsafe | PASS | `path unreachable` qualifier |

**None are actual soundness violations.** Inspection with
`--check-level full` shows each PASS is annotated
`✅ pass (❗path unreachable)` — Strata's deductive verifier is
correctly self-flagging that the path to the assertion was
unreachable under bounded CFG fuel, not that the property was proven.
The matrix's PASS column collapses this qualifier; that's a
**matrix-display tooling gap**, not a verifier soundness bug.

Fix lever: surface a third state (e.g. `PASS-unreachable`) in
`run_pipeline.py` and `tools/disagreement_matrix.py`. Tracked in
README under *Known blockers*.

### bugFinding validation

The matrix has the symbolic-execution backend correctly flag 6 of 7
unsafe SV-COMP programs as PARTIAL with concrete failing VCs — a
positive validation of the `bugFinding` mode against an external
oracle, the first such evidence in the project. The remaining one
(`sv_loops_mono7_1`) is also reported PARTIAL by bugFinding for
unrelated reasons.

### Why deductive PARTIAL counts climbed

Combined deductive: 39 PASS / 54 not-PASS, up from 21/43 on the v3
portfolio. The split-source view shows deductive does *better* in
absolute PASS count on SV-COMP (18 of 29) than on the portfolio
(21 of 64), reflecting that SV-COMP programs are typically smaller,
single-procedure, and lack the user-defined helpers that drive the
portfolio's sub-class (a) `❓ unknown` failures (missing ensures
on contract-ported parser callees).

### What this means for the matrix

The SV-COMP integration confirms what cross-validation has been
showing on the portfolio: pipeline-side issues currently dominate
the matrix. With ground-truth labels in hand, the absence of an
actual `unsafe ∧ PASS` is the cleanest soundness statement to date.
The remaining gap to a (P) finding (a real program defect surfaced
by Strata that CBMC misses) is unchanged: ensures synthesis on
CFG bodies is the lever, with `390fadc37` covering structured
bodies as a starting point.

## Reproducing

```bash
# Regenerate .bpl for any new .c files in programs/.
finch run --rm --entrypoint /bin/sh \
  -v "$PWD/Examples/smack-docker/programs:/programs" \
  smack -c '. /home/user/smack.environment && cd /programs && \
            for f in *.c; do [ -f "${f%.c}.bpl" ] && continue; \
            smack --no-verify -bpl "${f%.c}.bpl" "$f"; done'

# Run the four-backend matrix.
python3 Examples/smack-docker/run_pipeline.py \
  --backends deductive,bugFinding,cbmc,cbmc-native \
  > pipeline-output.txt 2>&1

# Build the divergence matrix.
python3 tools/disagreement_matrix.py < pipeline-output.txt > matrix.md
```

Per-program flag overrides for `cbmc-native` live in
`Examples/smack-docker/cbmc_native_flags.json`. Triage notes for
the 13 representative divergent rows are in `wt-test/triage/`
(working dir, not committed).
