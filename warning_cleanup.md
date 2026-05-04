# Warning / Error Reporting Cleanup Plan

## Current State

Three separate error/warning types exist in the Python pipeline:

1. **`WarningKind` + `SpecError`** (`Specs/Error.lean`) -- Accumulated warnings
   from PySpec parsing and PySpec-to-Laurel translation. `WarningKind` is a
   `{phase, category}` string pair; `SpecError` bundles it with file, location,
   and message. Collected via `StateT` arrays.

2. **`TranslationError`** (`PythonToLaurel.lean:138`) -- First-failure inductive
   for user Python-to-Laurel translation. Variants: `unsupportedConstruct`,
   `typeError`, `nameError`, `internalError`, `userPythonError`. Propagated via
   `Except`. Stays separate (not part of this migration).

3. **`PipelineError`** (`PySpecPipeline.lean:394`) -- Public-facing error from
   `pythonAndSpecToLaurel`. Maps `TranslationError` variants into three buckets:
   `userCode`, `knownLimitation`, `internal`. Stays as-is.

## Goals

- Create `Strata.Languages.Python.PipelineMessages` as a unified module for
  categorized pipeline diagnostics (replacing `Specs/Error.lean`).
- Add an **impact** tag to each message kind distinguishing internal errors vs
  warnings vs known limitations vs user code issues.
- Change `pythonAndSpecToLaurel` to return a result type (with accumulated
  warnings) instead of printing to stderr, so callers control output.
- Convert ad-hoc stderr warnings in `PySpecPipeline.lean` (invalid module name,
  overload-resolve warnings, missing auto-resolved pyspec) into structured
  `PipelineMessage` entries.
- Extract JSON summary and stderr printing into standalone utility functions.
- Delete `Specs/Error.lean` when done.
- Scope: PySpec warnings only (not PythonToLaurel `TranslationError`).

## Proposed Types

```lean
-- Strata/Languages/Python/PipelineMessages.lean

/-- A pipeline phase that produced a message. -/
structure Phase where
  name : String
  deriving BEq, DecidableEq, Hashable, Ord, Repr

namespace Phase
def pySpecParsing : Phase := { name := "pySpecParsing" }
def pySpecToLaurel : Phase := { name := "pySpecToLaurel" }
def overloadResolution : Phase := { name := "overloadResolution" }
def moduleResolution : Phase := { name := "moduleResolution" }
end Phase

/-- How severe / actionable is this message? -/
inductive MessageImpact where
  /-- An unexpected failure that prevented some output from being generated
      (e.g., a malformed overload entry that was skipped). -/
  | internalError
  /-- An unexpected condition that did not prevent output, but may indicate
      a tool bug worth investigating. -/
  | internalWarning
  /-- A known, documented limitation that may cause specs to be incomplete
      or imprecise. -/
  | knownLimitation
  /-- An issue detected in the user's Python source code. -/
  | userCodeIssue
  deriving BEq, DecidableEq, Hashable, Ord, Repr

/-- A categorized message kind with phase, category, and impact. -/
structure MessageKind where
  phase : Phase
  category : String
  impact : MessageImpact
  deriving BEq, DecidableEq, Hashable, Ord, Repr

/-- A located, categorized pipeline message (warning or error). -/
structure PipelineMessage where
  file : System.FilePath
  loc : SourceRange
  kind : MessageKind
  message : String
```

## Migration Steps

### Step 1: Create `PipelineMessages.lean` with new types

Create `Strata/Languages/Python/PipelineMessages.lean` defining `Phase`,
`MessageImpact`, `MessageKind`, and `PipelineMessage`. Define `Phase`
constants for all phases (`pySpecParsing`, `pySpecToLaurel`,
`overloadResolution`, `moduleResolution`). Include the `LT` instance, a
`ToString` for `MessageImpact`, and JSON helpers. Port all existing
`WarningKind` constants as `MessageKind` constants with their `impact`
classification and typed `Phase` values.

Add new `MessageKind` constants for the ad-hoc warnings that will be
structured in later steps:

```lean
namespace MessageKind
-- Module resolution phase
def invalidModuleName : MessageKind :=
  { phase := .moduleResolution, category := "invalidModuleName",
    impact := .internalWarning }
def missingAutoResolvedPySpec : MessageKind :=
  { phase := .moduleResolution, category := "missingAutoResolvedPySpec",
    impact := .knownLimitation }

-- Overload resolution phase
def overloadResolveWarning : MessageKind :=
  { phase := .overloadResolution, category := "resolveWarning",
    impact := .internalWarning }
def overloadParamNameDisagreement : MessageKind :=
  { phase := .pySpecToLaurel, category := "overloadParamNameDisagreement",
    impact := .internalError }
end MessageKind
```

### Step 2: Migrate all consumers directly to new API

Update all files that currently use `WarningKind` / `SpecError`:

- **`Specs/ToLaurel.lean`**: Change `ToLaurelState.errors` from
  `Array SpecError` to `Array PipelineMessage`. Update `reportError` to
  construct `PipelineMessage` with `MessageKind`. Update all call sites
  (`.unsupportedUnion` -> `.unsupportedUnion`, etc. -- names stay the same,
  just the type changes). Fix `pushOverloadEntry` (see below).
- **`Specs.lean`**: Change `PySpecState.errors` and `PySpecState.warnings` from
  `Array SpecError` to `Array PipelineMessage`. Update `specError` /
  `specWarning` in `PySpecMClass`.
- **`PySpecPipeline.lean`**: Change `PySpecLaurelResult.pyspecWarnings` from
  `Array Python.Specs.SpecError` to `Array PipelineMessage`.

Delete `Specs/Error.lean` and remove it from `Specs.lean` imports.

### Step 2b: Fix `FunctionOverloads.paramName` and `pushOverloadEntry`

`FunctionOverloads.paramName` has been changed from `Option String` (with
default `none`) to `String` (required). This removes the `Inhabited` instance
since there's no sensible default. Downstream changes:

- **`OverloadTable.lean`**: `FunctionOverloads.findDispatchArg` no longer
  needs `.bind` on `paramName` — it's always present. Already updated.
- **`Specs/ToLaurel.lean`** `pushOverloadEntry`: Rewritten to split the
  first-entry case (create new `FunctionOverloads` with `paramName`) from the
  subsequent-entry case (check for disagreement, then insert into existing
  entries). The current WIP has a few fixups needed:
  - `paramName := some paramName` should be `paramName := paramName` (no
    longer `Option`).
  - `existing.paramName.any (· != paramName)` should be
    `existing.paramName != paramName` (no longer `Option`).
  - `existing.paramName <|> some paramName` in the `modify` should be
    `existing.paramName` (first-wins; value is already set).
  - `existing.paramName.get!` in the message can be just
    `existing.paramName`.
  - `reportError sorry sorry` needs the real kind and location:
    `reportError .overloadParamNameDisagreement default` (using `default`
    for `SourceRange` since overload entries don't carry location — or we
    could thread the function's `loc` through from `extractOverloadEntry`).
  - Remove "Warning: " prefix from the message string (the reporting
    infrastructure handles severity).
- **`PySpecPipeline.lean`**: `resolveModuleEntry` return type was changed
  from `EIO String` to `BaseIO`. This is fine — `BaseIO` lifts
  transparently into `EIO String` in `resolveAndBuildLaurelPrelude`, so the
  `throw` calls at lines 253 and 276 continue to work unchanged. Once
  ad-hoc warnings are structured in Step 3, `resolveModuleEntry` can return
  warnings via its result type instead of printing to stderr.


### Step 3: Structure ad-hoc warnings

Convert the three ad-hoc stderr warnings in `PySpecPipeline.lean` into
`PipelineMessage` entries accumulated in the result:

- **`resolveModuleEntry` (line 222-224)**: Instead of `eprintln`, return a
  `PipelineMessage` with kind `.invalidModuleName`. The caller
  (`resolveAndBuildLaurelPrelude`) accumulates it.
- **`resolveAndBuildLaurelPrelude` (line 257-259)**: The overload-resolve
  warnings from `IdentifyOverloads.ResolveState.warnings` are currently
  `Array String`. Convert each to a `PipelineMessage` with kind
  `.overloadResolveWarning`.
- **`resolveAndBuildLaurelPrelude` (line 268-270)**: Missing auto-resolved
  pyspec becomes a `PipelineMessage` with kind `.missingAutoResolvedPySpec`.

This also means `resolveAndBuildLaurelPrelude` needs to thread accumulated
warnings through (it already partially does via `dispatchWarnings`).

**Note**: `IdentifyOverloads.ResolveState.warnings` is `Array String` with no
location info. We can either:
- (a) Change `IdentifyOverloads` to produce `Array PipelineMessage` directly
  (cleanest, but wider change).
- (b) Wrap them at the call site with a default `SourceRange.none` and the
  relevant file path (pragmatic, minimal change).

Recommend (b) for now.

### Step 4: New result type for `pythonAndSpecToLaurel`

Replace the current `EIO PipelineError Laurel.Program` return type with:

```lean
/-- Result of the full Python + PySpec to Laurel pipeline. -/
inductive PythonToLaurelResult where
  /-- Translation succeeded, possibly with non-fatal warnings. -/
  | success (program : Laurel.Program) (warnings : Array PipelineMessage)
  /-- A fatal error prevented Laurel generation. Warnings collected before
      the failure are still available. -/
  | failure (error : PipelineError) (warnings : Array PipelineMessage)
```

Change `pythonAndSpecToLaurel` to return `BaseIO PythonToLaurelResult`.
Remove `quiet`, `warningSummaryFile`, and all stderr printing from this
function. Thread `pyspecWarnings` (plus the newly structured ad-hoc warnings)
into the result.

### Step 5: Extract output utilities

Move all stderr/JSON output into standalone functions:

```lean
/-- Print a human-readable warning summary to stderr. -/
def PipelineMessage.printSummary
    (warnings : Array PipelineMessage)
    (verbose : Bool := false) : BaseIO Unit

/-- Generate a JSON warning summary. -/
def PipelineMessage.toSummaryJson
    (warnings : Array PipelineMessage) : Lean.Json

/-- Write a JSON warning summary to a file. -/
def PipelineMessage.writeSummaryJson
    (warnings : Array PipelineMessage) (path : System.FilePath) : BaseIO Unit
```

The JSON output includes the new `impact` field:

```lean
Lean.Json.mkObj [
  ("phase", .str kind.phase.name),
  ("category", .str kind.category),
  ("impact", .str (toString kind.impact)),
  ("count", .num count)
]
```

Update callers of `pythonAndSpecToLaurel` (command-line entry points) to:
1. Match on `PythonToLaurelResult`
2. Call `PipelineMessage.printSummary` / `PipelineMessage.writeSummaryJson`
   as appropriate

### Step 6: Update tests

Update `StrataTest/Languages/Python/ToLaurelTest.lean` to use `MessageKind` /
`PipelineMessage` and verify `impact` values.

## Impact Classification for Existing Kinds

All current `reportError` calls in `ToLaurel.lean` are non-fatal: they
accumulate into the state array and translation continues. However, the
overload-extraction errors (`overload*`) cause individual overload entries to
be skipped (the function returns `none`), which is a partial data loss --
hence `internalError` rather than `internalWarning`.

`missingMethodSelf` is non-fatal: translation continues with the method
processed without self-parameter handling.

| WarningKind                   | Proposed Impact     | Rationale |
|-------------------------------|---------------------|-----------|
| `unsupportedUnion`            | `knownLimitation`   | Union types not modeled |
| `unsupportedOptionalFloat`    | `knownLimitation`   | Optional pattern gaps |
| `unsupportedOptionalList`     | `knownLimitation`   | Optional pattern gaps |
| `unsupportedOptionalDict`     | `knownLimitation`   | Optional pattern gaps |
| `unsupportedOptionalAny`      | `knownLimitation`   | Optional pattern gaps |
| `unsupportedOptionalBytes`    | `knownLimitation`   | Optional pattern gaps |
| `typeError`                   | `internalWarning`   | Unexpected type mismatch; non-fatal |
| `placeholderExpr`             | `knownLimitation`   | Expression not fully translated |
| `floatLiteral`                | `knownLimitation`   | Float precision limitation |
| `isinstanceUnsupported`       | `knownLimitation`   | isinstance not modeled |
| `forallListUnsupported`       | `knownLimitation`   | forall over list not modeled |
| `forallDictUnsupported`       | `knownLimitation`   | forall over dict not modeled |
| `missingMethodSelf`           | `internalWarning`   | Non-fatal; method still processed |
| `kwargsExpansionError`        | `internalWarning`   | Non-fatal kwargs issue |
| `postconditionUnsupported`    | `knownLimitation`   | Postconditions not yet modeled |
| `overloadNoArgs`              | `internalError`     | Overload entry skipped |
| `overloadArgArity`            | `internalError`     | Overload entry skipped |
| `overloadArgNotStringLiteral` | `internalError`     | Overload entry skipped |
| `overloadReturnArity`         | `internalError`     | Overload entry skipped |
| `overloadReturnNotClass`      | `internalError`     | Overload entry skipped |
| `pySpecParsingError`          | `internalError`     | Parse failure; spec likely skipped |
| `pySpecParsingWarning`        | `knownLimitation`   | Non-fatal parse issue |
| `invalidModuleName` (new)     | `internalWarning`   | Bad module name skipped |
| `missingAutoResolvedPySpec` (new) | `knownLimitation` | Expected pyspec file not found |
| `overloadResolveWarning` (new) | `internalWarning`  | Non-fatal overload resolution issue |
| `overloadParamNameDisagreement` (new) | `internalError` | Overload entries disagree on dispatch param name; keyword dispatch may resolve wrong overload |

## Stderr/Stdout Audit

All output is stderr-based (`IO.eprintln`). No stdout writes exist in the
pipeline.

| File | Line | What | Action |
|------|------|------|--------|
| `PySpecPipeline.lean:222-224` | `warning: invalid module name '{modName}', skipping` | Convert to `PipelineMessage` `.invalidModuleName` (Step 3) |
| `PySpecPipeline.lean:257-259` | `warning: {w}` (overload resolve warnings) | Convert to `PipelineMessage` `.overloadResolveWarning` (Step 3) |
| `PySpecPipeline.lean:268-270` | `warning: auto-resolved pyspec not found for module` | Convert to `PipelineMessage` `.missingAutoResolvedPySpec` (Step 3) |
| `PySpecPipeline.lean:448-452` | PySpec warning count + details | Move to `PipelineMessage.printSummary` utility (Step 5) |
| `PySpecPipeline.lean:453-470` | JSON warning summary + file write | Move to `PipelineMessage.writeSummaryJson` utility (Step 5) |
| `ReadPython.lean:61` | `[perf] {label}: {elapsedMs}ms` | Leave as-is (perf instrumentation, gated by flag) |
| `Specs.lean:44` | `[{event}]: {message}` | Leave as-is (debug event log, gated by event set) |
| `ToLaurel.lean:118` | `dbg_trace` overload name disagreement | Convert to `PipelineMessage` `.overloadParamNameDisagreement` (Step 2) |

## Open items for review during implementation

- Audit `internalError` vs `internalWarning` classification once everything
  compiles with the new types. The distinction is "output was lost" vs
  "output degraded but present" -- verify each case matches.