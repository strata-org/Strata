# Design: Split-Solve-Reconcile for Cloud-Based SMT Solving

## Motivation

Strata's verification pipeline is bottlenecked by SMT solving, which can take
seconds to minutes per query. For large programs, the total wall-clock time is
dominated by sequential solver invocations. Cloud-based solving enables massive
parallelism — all queries can be dispatched simultaneously — but requires
decoupling the pipeline into three phases:

1. **Generate** — run the Strata pipeline up to SMT file creation
2. **Solve** — dispatch SMT queries to cloud solvers (external to Strata)
3. **Reconcile** — read solver results and produce the final verification report

The generation phase (parse, transform, symbolic eval, SMT encoding) can itself
be expensive, so the reconcile phase must **not** re-run the pipeline. Instead,
the generate phase embeds all metadata needed for reconciliation directly in the
`.smt2` files.

## Design

### Key Decision: Manifest-Free Reconciliation

Rather than emitting a separate `manifest.json` file alongside the `.smt2`
files, all obligation metadata is embedded directly in each `.smt2` file using
standard SMT-LIB `set-info` directives. This eliminates a separate serialization
format, keeps each `.smt2` file self-contained, and avoids synchronization issues
between manifest and SMT files.

### Phase 1: Generate (`--no-solve`)

When `--no-solve --vc-directory <dir>` is used, Strata runs the full pipeline
(parse, transform, symbolic eval, SMT encoding) and writes `.smt2` files to the
VC directory. Each `.smt2` file includes `set-info` directives that capture the
obligation metadata the reconcile phase needs.

#### Embedded `set-info` Directives

| Directive | Description |
|-----------|-------------|
| `(set-info :file "<path>")` | Source file path for the obligation. |
| `(set-info :start N)` | Start offset of the source location range. |
| `(set-info :stop N)` | End offset of the source location range. |
| `(set-info :final-message "<msg>")` | Obligation label/message (e.g., `"assert_precondition_0"`). |
| `(set-info :property "<type>")` | Property type: `"assert"`, `"cover"`, `"divisionByZero"`, `"arithmeticOverflow"`. |
| `(set-info :resolved-sat "<verdict>")` | Evaluator-resolved satisfiability result (`"sat"`, `"unsat"`, `"unknown"`). Present only when the evaluator already decided this check. |
| `(set-info :resolved-val "<verdict>")` | Evaluator-resolved validity result. Present only when the evaluator already decided this check. |
| `(set-info :sat-message "<msg>")` | Presence indicates a satisfiability check was requested. |
| `(set-info :unsat-message "<msg>")` | Presence indicates a validity check was requested. |

These directives are emitted by `encodeCore` in `Verifier.lean` at the end of
the SMT encoding, after the `check-sat` commands. They are comments from the
solver's perspective (solvers ignore unknown `set-info` keys) but are parsed by
the reconcile phase.

#### Evaluator-Resolved Obligations

Some obligations are trivially resolved by the evaluator (e.g., `assert true`
→ valid). These still produce `.smt2` files (since the SMT encoding runs
regardless), but the `resolved-sat` / `resolved-val` directives record the
evaluator's verdict. The reconcile phase uses these stored results directly
instead of relying on the solver output.

### Phase 2: Solve (external)

The user runs each `.smt2` file through a solver (locally, in the cloud, etc.)
and captures the solver's stdout into a corresponding `.result` file:

```
vcs/
  assert_precondition_0_0.smt2
  assert_precondition_0_0.result    ← solver stdout
  loop_invariant_1_1.smt2
  loop_invariant_1_1.result
  ...
```

The `.result` file contains exactly what the solver prints to stdout — verdict
lines (`sat`/`unsat`/`unknown`) followed by optional model output from
`(get-value ...)` commands. This is the same format Strata already parses.

If a `.result` file is missing, the reconcile phase treats the obligation as
`unknown`.

### Phase 3: Reconcile (`strata reconcile`)

```bash
lake exe strata reconcile --vc-directory ./vcs/ [--check-mode deductive] [--check-level minimal] [--sarif]
```

This command:
1. Scans the VC directory for `.smt2` files
2. For each `.smt2` file:
   - Parses `set-info` directives to extract obligation metadata (`SMT2Meta`)
   - Determines which checks were requested (satisfiability, validity)
   - If evaluator-resolved: uses the stored verdict directly
   - Otherwise: reads the corresponding `.result` file and parses solver output
3. Builds a `VCResult` using `buildVCResult` (the same function used by the
   integrated verifier), applying outcome masking
4. Merges results by assertion (`mergeByAssertion`)
5. Produces the final report (text or SARIF)

---

## Reconcile Algorithm

```
function reconcileDirectory(vcDir, options):
  results = []
  for each .smt2 file in vcDir (sorted by name):
    smt2Content = readFile(smt2File)
    meta = parseSMT2Meta(smt2Content)  // extract set-info directives

    // Determine which checks were requested
    satisfiabilityCheck = meta.hasSatCheck || meta.resolvedSat.isSome
    validityCheck = meta.hasValCheck || meta.resolvedVal.isSome

    // Get evaluator-resolved results (if any)
    peSat? = meta.resolvedSat.map(smtResultOfString)
    peVal? = meta.resolvedVal.map(smtResultOfString)

    // Read solver output (if .result file exists)
    resultFile = smt2File.replaceSuffix(".smt2", ".result")
    if resultFile.exists:
      solverOutput = readFile(resultFile)
      (solverSat, solverVal) = parseResultFile(solverOutput,
        satisfiabilityCheck && peSat?.isNone,
        validityCheck && peVal?.isNone)
    else:
      (solverSat, solverVal) = (unknown, unknown)

    // Evaluator results take precedence over solver results
    satResult = peSat?.getD(solverSat)
    valResult = peVal?.getD(solverVal)

    // Reconstruct obligation from metadata
    obligation = ProofObligation(meta.label, meta.property, meta.fileRange)

    // Build classified VCResult (same function as integrated verifier)
    result = buildVCResult(obligation, satResult, valResult,
      satisfiabilityCheck, validityCheck, phases=[], options)
    results.push(result)

  return mergeByAssertion(results)
```

---

## Implementation

### `buildVCResult` — Shared Classification Logic

The `buildVCResult` function in `Verifier.lean` is the single source of truth
for turning raw `(satResult, valResult)` into a classified `VCResult`. It:

1. Applies phase validation (`adjustForPhases`) — demotes unvalidated sat
   results to unknown
2. Builds the solver log
3. Constructs the raw `VCOutcome`
4. Applies `maskOutcome` based on which checks were requested
5. Returns the final `VCResult`

Both the integrated verifier (`getObligationResult`) and the reconcile path
(`reconcileFromSMT2`) call this function, ensuring consistent classification.

### `Reconcile.lean` — Reconcile Module

- `parseSMT2Meta`: Parses `set-info` directives from `.smt2` file content into
  an `SMT2Meta` structure.
- `parseResultFile`: Parses a `.result` file's verdict lines into
  `(satResult, valResult)`, respecting which checks were requested.
- `reconcileFromSMT2`: Combines parsed metadata and solver output into a
  `VCResult`.
- `reconcileDirectory`: Orchestrates the full reconcile over a directory.

### `StrataMain.lean` — CLI Command

The `reconcileCommand` accepts:
- `--vc-directory` (required) — directory containing `.smt2` and `.result` files
- `--check-mode` — verification mode (deductive, bugFinding, etc.)
- `--check-level` — check level (minimal, minimalVerbose, full)
- `--sarif` — emit SARIF output
- `--verbose` / `--quiet` — output verbosity

### `Verifier.lean` — Metadata Emission

`encodeCore` is extended with `property`, `resolvedSat`, and `resolvedVal`
parameters. These are threaded through `dischargeObligation` →
`getObligationResult` → `verifySingleEnv`. The evaluator-resolved results
(`peSatResult?`, `peValResult?`) are passed from `verifySingleEnv` where they
are already computed.

### Helper Scripts

- `Scripts/ssr_py.sh` — End-to-end SSR workflow for Python files (generate →
  solve → reconcile) with parallel solving via `xargs -P`.
- `StrataTest/Languages/Python/run_py_ssr_test.sh` — Integration test that
  validates SSR output matches direct verification for all Python test files.

---

## Design Decisions

**Why embed metadata in `.smt2` files instead of a separate manifest?**
A separate manifest introduces synchronization concerns (manifest and `.smt2`
files can get out of sync), requires a custom JSON schema with serialization/
deserialization code, and makes each `.smt2` file dependent on an external file
for interpretation. Embedding metadata via `set-info` keeps each file
self-contained, uses a standard SMT-LIB mechanism, and is ignored by solvers.

**Why not re-run the pipeline during reconcile?**
The symbolic evaluation step (path explosion, expression simplification) can be
expensive for large programs. The embedded metadata avoids re-running it.

**Why allow `checkMode`/`checkLevel` override in reconcile?**
These only affect how outcomes are classified and displayed (pass/fail/warning).
The underlying SMT results are mode-independent. This lets users re-classify
results without re-solving — e.g., switch from deductive to bug-finding mode.

**Why pass empty `phases` in reconcile?**
The reconcile path calls `buildVCResult` with `phases = []` because phase
validation (which demotes sat results to unknown for unvalidated abstractions)
cannot be reconstructed from the `.smt2` metadata alone. This is acceptable
because the current phase validators are all stubs that return `false`. When
real validators are implemented, this will need revisiting.

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Phase validators get real implementations | Reconcile cannot apply phase validation | Extend `set-info` metadata or add a lightweight sidecar file for phase decisions |
| SMT file naming collisions | Two obligations produce the same filename | Already handled: counter suffix (`_{N}`) ensures uniqueness |
| Solver produces unexpected output format | Result parsing fails | Reuse existing verdict parsing; report clear errors for unparseable results |
| User changes source between generate and reconcile | Source locations in `set-info` are stale | Document that generate and reconcile must use the same source |
| Missing `.result` files | Obligations classified as unknown | Graceful degradation: treat missing results as `unknown` rather than failing |

---

## Future Extensions

- **Source hash validation:** Embed a hash of the input file in `set-info`.
  The reconcile phase can warn if the source has changed.
- **Incremental re-solving:** If only some obligations change after a source
  edit, re-generate only the affected SMT files and reuse cached results for
  unchanged obligations.
- **Rich model display:** Currently the reconcile path does not reconstruct
  solver models (variable mappings are not embedded). A future extension could
  embed variable map metadata to enable model display during reconcile.
- **Phase validation serialization:** When validators get real implementations,
  embed phase validation decisions in `set-info` directives so the reconcile
  phase can apply them.
- **Parallel local solving:** Use the directory listing to drive parallel local
  solver invocations (multiple cvc5 processes), as a simpler alternative to
  cloud solving.
