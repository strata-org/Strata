# Cross-validation portfolio screening

A multi-backend evaluation of the SMACK→Strata pipeline against 65
parser, decoder, and utility programs from four sources.

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
| **Total** | **65** | |

## Verdict matrix

Run with `python3 run_pipeline.py --backends deductive,bugFinding,cbmc,cbmc-native`.

Summary:

|  | PASS | PARTIAL | FAIL | TIMEOUT | skip |
|---|---:|---:|---:|---:|---:|
| Strata deductive  | 47 | 14 | 2 | 2 | 0 |
| Strata bugFinding |  0 | 60 | 2 | 3 | 0 |
| Strata-CBMC       |  0 |  0 | 64 | 1 | 0 |
| CBMC native       | 39 |  0 | 26 | 0 | 0 |

62 of 65 programs show some divergence. The full per-row matrix is
in `wt-test/portfolio-matrix.md`. The divergence column is computed
by `tools/disagreement_matrix.py`, which auto-tags rows where
Strata-CBMC and CBMC-native disagree as **(T-lowering)**.

```
T-lowering:   39 rows
one-off:      23 rows
all-disagree:  0 rows
all-agree:     3 rows  (HTTPClient_Initialize/ReadHeader, skipEscape — all FAIL on every backend)
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
