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
the generate phase serializes a manifest containing all metadata needed for
reconciliation.

## Current State

Strata already has `--no-solve --vc-directory <dir>` which runs the full
pipeline and writes `.smt2` files without invoking the solver. What's missing:

- No manifest is emitted alongside the SMT files
- No entry point to read solver results and produce the final report

## Design

### Phase 1: Generate (enhanced `--no-solve`)

When `--no-solve --vc-directory <dir>` is used, Strata will additionally write
a **manifest file** (`manifest.json`) to the VC directory. The manifest captures
everything the reconcile phase needs.

### Phase 2: Solve (external)

The user runs each `.smt2` file through a solver (locally, in the cloud, etc.)
and captures the solver's stdout into a corresponding `.result` file:

```
vcs/
  manifest.json
  assert_precondition_0_0.smt2
  assert_precondition_0_0.result    ← solver stdout
  loop_invariant_1_1.smt2
  loop_invariant_1_1.result
  ...
```

The `.result` file contains exactly what the solver prints to stdout — verdict
lines (`sat`/`unsat`/`unknown`) followed by optional model output from
`(get-value ...)` commands. This is the same format Strata already parses.

### Phase 3: Reconcile (new `strata reconcile` command)

```bash
lake exe strata reconcile --vc-directory ./vcs/ [--check-mode deductive] [--check-level minimal] [--sarif]
```

This command:
1. Reads `manifest.json`
2. For each obligation in the manifest:
   - If resolved by the evaluator: uses the stored result directly
   - Otherwise: reads the corresponding `.result` file, parses the solver
     output using the variable mappings from the manifest
3. Applies phase validation (demote/promote sat results)
4. Masks outcomes based on check mode/level
5. Merges results by assertion (`mergeByAssertion`)
6. Produces the final report (text or SARIF)

---

## Manifest Format

The manifest is a JSON file with the following structure:

```json
{
  "version": 1,
  "options": {
    "checkMode": "deductive",
    "checkLevel": "minimal",
    "verbose": "quiet"
  },
  "obligations": [
    {
      "label": "assert_precondition_0",
      "property": "assert",
      "smtFile": "assert_precondition_0_0.smt2",
      "satisfiabilityCheck": true,
      "validityCheck": true,
      "resolvedBySim": null,
      "sourceLocation": {
        "file": "Examples/SimpleProc.core.st",
        "start": { "line": 10, "column": 4 },
        "stop": { "line": 10, "column": 20 }
      },
      "relatedLocations": [],
      "passWhenUnreachable": true,
      "hasFullCheck": false,
      "variableMap": [
        { "var": "x", "type": "Int", "smtId": "$__f.0" },
        { "var": "y", "type": "Bool", "smtId": "$__f.1" }
      ],
      "constructorNames": ["Nil", "Cons"],
      "phaseValidation": [
        { "phase": "CallElim", "validates": true },
        { "phase": "LoopElim", "validates": false }
      ]
    },
    {
      "label": "trivial_true_1",
      "property": "assert",
      "smtFile": null,
      "resolvedBySim": {
        "satisfiability": "unsat",
        "validity": "unsat"
      },
      "sourceLocation": {
        "file": "Examples/SimpleProc.core.st",
        "start": { "line": 5, "column": 4 },
        "stop": { "line": 5, "column": 15 }
      },
      "relatedLocations": [],
      "passWhenUnreachable": true,
      "hasFullCheck": false,
      "variableMap": [],
      "constructorNames": [],
      "phaseValidation": []
    }
  ]
}
```

### Field Descriptions

**`version`**: Manifest format version. Allows future evolution.

**`options`**: Verification settings used during generation. The reconcile
command can override `checkMode` and `checkLevel` (since these only affect
classification/rendering), but other options are informational.

**`obligations`**: Array of proof obligations, one per VC.

Per obligation:

| Field | Type | Description |
|-------|------|-------------|
| `label` | string | Obligation label (e.g., `"assert_precondition_0"`). Used for display and grouping. |
| `property` | string | Property type: `"assert"`, `"cover"`, `"assume"`, `"invariant"`. Determines classification behavior. |
| `smtFile` | string? | Filename of the `.smt2` file (relative to VC directory). `null` if resolved by evaluator. |
| `satisfiabilityCheck` | bool | Whether the satisfiability check (`P ∧ Q`) was requested. |
| `validityCheck` | bool | Whether the validity check (`P ∧ ¬Q`) was requested. |
| `resolvedBySim` | object? | If the evaluator resolved this without the solver, contains `{ "satisfiability": "sat"/"unsat"/"unknown", "validity": "sat"/"unsat"/"unknown" }`. `null` if solver is needed. |
| `sourceLocation` | object? | File, start, stop from obligation metadata. Used by `vcResultGroupKey` for merging. |
| `relatedLocations` | array | Related file ranges (from inlining). Also used for grouping. |
| `passWhenUnreachable` | bool | From `PropertyType.passWhenUnreachable`. Affects unreachable-path classification. |
| `hasFullCheck` | bool | Whether the obligation has a `fullCheck` annotation. |
| `variableMap` | array | Maps program variables to SMT identifiers. Each entry: `{ "var": name, "type": type_string, "smtId": smt_name }`. Used by `processModel` to interpret solver models. |
| `constructorNames` | array | Datatype constructor names from `SMT.Context`. Used by `convertModel` to distinguish constructors from variables in models. |
| `phaseValidation` | array | Per-phase validation decisions. Each entry: `{ "phase": name, "validates": bool }`. `validates: true` means the phase applies `modelToValidate` to this obligation (currently always rejects). `validates: false` means `modelPreserving`. |

### Design Decisions

**Why serialize phase validation decisions instead of closures?**
The `AbstractedPhase` validators are Lean closures that cannot be serialized.
However, the decision of whether a phase validates a given obligation is
deterministic — it depends only on the obligation's label prefixes. We serialize
the *decision* (`validates: true/false`) rather than the logic. The reconcile
phase reconstructs validators from these flags.

Currently all validators return `false` (TODO stubs), so `validates: true`
means "demote sat to unknown". When real validators are implemented, this
design will need revisiting — either by serializing enough context for
validation, or by making the reconcile phase call into the validator code.

**Why not re-run the pipeline?**
The symbolic evaluation step (path explosion, expression simplification) can be
expensive for large programs. The manifest avoids re-running it entirely.

**Why allow `checkMode`/`checkLevel` override in reconcile?**
These only affect how outcomes are classified and displayed (pass/fail/warning).
The underlying SMT results are mode-independent. This lets users re-classify
results without re-solving — e.g., switch from deductive to bug-finding mode.

**Why store `resolvedBySim` in the manifest?**
Some obligations are trivially resolved by the evaluator (e.g., `assert true`
→ valid, `assert false` → invalid). These never produce SMT files. The
reconcile phase must include them in the final report.

---

## Reconcile Algorithm

```
function reconcile(manifest, vcDir, overrideOptions):
  options = manifest.options merged with overrideOptions

  results = []
  for obligation in manifest.obligations:
    if obligation.resolvedBySim != null:
      // Evaluator already resolved this
      satResult = parseResult(obligation.resolvedBySim.satisfiability)
      valResult = parseResult(obligation.resolvedBySim.validity)
    else:
      // Read solver output
      resultFile = vcDir / (obligation.smtFile.replaceSuffix(".smt2", ".result"))
      solverStdout = readFile(resultFile)
      (satResult, valResult) = parseSolverOutput(
        solverStdout,
        obligation.variableMap,
        obligation.satisfiabilityCheck,
        obligation.validityCheck
      )

    // Phase validation: demote/promote sat results
    for phase in obligation.phaseValidation:
      if phase.validates:
        satResult = demoteIfSat(satResult)  // sat → unknown
        valResult = demoteIfSat(valResult)

    // Build outcome
    outcome = VCOutcome(satResult, valResult)
    outcome = maskOutcome(outcome,
      obligation.satisfiabilityCheck, obligation.validityCheck)

    // Build VCResult with obligation metadata
    result = VCResult(obligation, outcome, options)
    results.push(result)

  // Merge results from different paths to the same assertion
  return mergeByAssertion(results)
```

---

## Implementation Plan

### Task 1: Define Manifest Data Types

**File:** `Strata/Languages/Core/Manifest.lean` (new)

Define Lean structures for the manifest with `ToJson`/`FromJson` instances:

- `ManifestVersion` — version constant
- `ManifestOptions` — subset of `VerifyOptions` (checkMode, checkLevel, verbose)
- `ManifestVariableEntry` — `{ var, type, smtId }`
- `ManifestPhaseEntry` — `{ phase, validates }`
- `ManifestSourceLocation` — `{ file, start, stop }`
- `ManifestObligation` — all per-obligation fields from the table above
- `Manifest` — `{ version, options, obligations }`

Derive or manually implement `ToJson`/`FromJson` for each. Follow the pattern
in `Strata/Util/Sarif.lean` which already uses `deriving ToJson, FromJson`.

**Estimated size:** ~150 lines

### Task 2: Emit Manifest During `--no-solve`

**Files:**
- `Strata/Languages/Core/Manifest.lean` — add `buildManifest` function
- `Strata/Languages/Core/Verifier.lean` — modify `verifySingleEnv` and `verify`

In `verifySingleEnv`, when `skipSolver` is true, collect manifest entries
instead of (or in addition to) building `VCResult`s:

- For evaluator-resolved obligations: record `resolvedBySim` with the result
- For solver-needed obligations: after SMT encoding (which already happens to
  write the file), extract:
  - Variable map from `EncoderState.ufs` and the typed variable list
  - Constructor names from `SMT.Context.getConstructorNames`
  - Phase validation decisions by evaluating `phase.getValidation obligation`
    for each phase

In `verify`, after all environments are processed, serialize the collected
manifest entries to `manifest.json` in the VC directory.

**Key insight:** The SMT encoding step (`ProofObligation.toSMTTerms`) already
runs during `--no-solve` because it's needed to write the `.smt2` file. The
manifest extraction piggybacks on this — it reads `EncoderState` and
`SMT.Context` which are already computed.

**Estimated size:** ~100 lines of new code, ~30 lines of modifications

### Task 3: Implement Result File Parsing

**File:** `Strata/Languages/Core/Manifest.lean` (extend)

Add a function to parse a `.result` file using the variable map from the
manifest. This reuses the existing `solverResult` / `parseVerdict` logic from
`SMTUtils.lean` but with the variable map reconstructed from the manifest
instead of from `EncoderState`.

Specifically:
- Build a synthetic `EncoderState` with just the `ufs` map populated from
  `ManifestVariableEntry` data
- Build a typed variable list from the manifest
- Call the existing `solverResult` function

Alternatively, write a simpler parser that only extracts verdicts and raw model
key-value pairs, since the full `processModel` pipeline may be overkill when
the variable map is already explicit.

**Design choice:** Start with the simpler approach (verdict + raw model
parsing). Model display in the reconcile phase will show SMT-level variable
names. If users need Core-level variable names, upgrade to the full
`processModel` path later.

**Estimated size:** ~80 lines

### Task 4: Implement Phase Validation Reconstruction

**File:** `Strata/Languages/Core/Manifest.lean` (extend)

Build `AbstractedPhase`-equivalent logic from `ManifestPhaseEntry` data:

```lean
def reconstructPhaseValidation (entries : Array ManifestPhaseEntry)
    : List AbstractedPhase :=
  entries.toList.map fun entry =>
    { name := entry.phase
      getValidation := fun _ =>
        if entry.validates then
          .modelToValidate (fun _ => false)  -- matches current TODO behavior
        else .modelPreserving }
```

This is straightforward because the current validators all return `false`.

**Estimated size:** ~20 lines

### Task 5: Implement the Reconcile Function

**File:** `Strata/Languages/Core/Reconcile.lean` (new)

Core reconciliation logic:

```lean
def reconcile (manifest : Manifest) (vcDir : System.FilePath)
    (overrideOptions : Option ReconcileOptions := none)
    : IO (Except String VCResults)
```

This function:
1. Iterates over `manifest.obligations`
2. For each obligation, either uses `resolvedBySim` or reads the `.result` file
3. Applies phase validation
4. Applies `maskOutcome`
5. Builds `VCResult` with reconstructed obligation metadata
6. Calls `mergeByAssertion` on the collected results

The function reuses existing types (`VCOutcome`, `VCResult`, `VCResults`,
`SMT.Result`) and functions (`maskOutcome`, `VCResults.mergeByAssertion`).

**Estimated size:** ~120 lines

### Task 6: Add `strata reconcile` CLI Command

**File:** `StrataMain.lean`

Add a new `reconcileCommand : Command`:

```
strata reconcile --vc-directory <dir> [--check-mode <mode>] [--check-level <level>]
                 [--sarif] [--verbose] [--quiet]
```

Flags:
- `--vc-directory` (required) — directory containing `manifest.json` and
  `.result` files
- `--check-mode` — override the check mode from the manifest
- `--check-level` — override the check level from the manifest
- `--sarif` — output in SARIF format
- `--verbose` / `--quiet` — output verbosity

The command:
1. Reads and parses `manifest.json`
2. Validates that all expected `.result` files exist (for non-evaluator-resolved
   obligations)
3. Calls `reconcile`
4. Formats and prints results (reusing existing `VCResult` formatting or SARIF
   output)
5. Exits with appropriate exit code (0 for pass, 2 for failures found)

Register the command in `commandMap`.

**Estimated size:** ~80 lines

### Task 7: Tests

**Files:**
- `StrataTest/Languages/Core/ManifestTest.lean` (new)
- `StrataTest/Languages/Core/ReconcileTest.lean` (new)

Tests:

1. **Manifest round-trip:** Build a `Manifest`, serialize to JSON, deserialize,
   verify equality.

2. **Manifest emission:** Run `verify` with `skipSolver = true` on a test
   program, verify the manifest file is written and contains expected
   obligations.

3. **Reconcile with known results:** Create a manifest and `.result` files by
   hand, run `reconcile`, verify the output matches expected classification.

4. **End-to-end:** Run `verify --no-solve` on a test program, then run the
   solver on the generated files, then run `reconcile`, and compare with
   direct `verify` output.

5. **Evaluator-resolved obligations:** Verify that obligations resolved by the
   evaluator (e.g., `assert true`) appear correctly in both the manifest and
   the reconciled output.

6. **Phase validation:** Verify that obligations going through CallElim/LoopElim
   have their sat results correctly demoted to unknown.

7. **mergeByAssertion:** Verify that obligations from different paths to the
   same assertion are correctly merged.

**Estimated size:** ~200 lines

### Task 8: Documentation

**Files:**
- `docs/CloudSolving.md` (new) — user-facing guide
- Update `README.md` — mention the split-solve-reconcile workflow

Document:
- The three-phase workflow with examples
- `.result` file format (solver stdout)
- Manifest format reference
- How to override check mode/level during reconcile
- Limitations (model display, phase validator evolution)

**Estimated size:** ~100 lines

---

## Task Dependency Graph

```
Task 1: Manifest types
  ├─→ Task 2: Emit manifest (depends on 1)
  ├─→ Task 3: Result file parsing (depends on 1)
  └─→ Task 4: Phase validation reconstruction (depends on 1)
        │
        ├─→ Task 5: Reconcile function (depends on 1, 3, 4)
        │     │
        │     └─→ Task 6: CLI command (depends on 5)
        │           │
        │           └─→ Task 7: Tests (depends on 2, 6)
        │                 │
        │                 └─→ Task 8: Documentation (depends on 7)
        │
        └─→ Task 2 (also depends on 4 for phaseValidation entries)
```

Tasks 2, 3, and 4 can proceed in parallel after Task 1 is complete.

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Manifest format changes as Strata evolves | Old manifests become incompatible | Version field enables migration; reconcile rejects unknown versions with clear error |
| Phase validators get real implementations | `validates: true/false` is no longer sufficient | Extend manifest with validator context, or require re-generation |
| SMT file naming collisions | Two obligations produce the same filename | Already handled: counter suffix (`_{N}`) ensures uniqueness |
| Large manifests for programs with many VCs | Slow JSON parsing | JSON is fine for thousands of entries; revisit if hitting tens of thousands |
| Solver produces unexpected output format | Result parsing fails | Reuse existing `solverResult` parser which already handles edge cases; report clear errors for unparseable results |
| User changes source between generate and reconcile | Manifest metadata (source locations) is stale | Document that generate and reconcile must use the same source; add source file hash to manifest for detection |

---

## Future Extensions

- **Source hash validation:** Store a hash of the input file in the manifest.
  The reconcile phase can warn if the source has changed.
- **Incremental re-solving:** If only some obligations change after a source
  edit, re-generate only the affected SMT files and reuse cached results for
  unchanged obligations.
- **Rich model display:** Upgrade from SMT-level variable names to Core-level
  names by serializing enough of the `EncoderState` for full `processModel`
  reconstruction.
- **Phase validator serialization:** When validators get real implementations,
  serialize the obligation context they need (e.g., the pre-transformation
  program fragment) so they can run during reconcile without the full pipeline.
- **Parallel local solving:** Use the manifest to drive parallel local solver
  invocations (multiple cvc5 processes), as a simpler alternative to cloud
  solving.
