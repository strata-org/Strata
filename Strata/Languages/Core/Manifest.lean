/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Data.Json.Basic
public import Lean.Data.Json.FromToJson
public import Strata.Languages.Core.Verifier
import Lean.Data.Json

/-!
# Manifest Format for Split-Solve-Reconcile

This module defines the JSON manifest emitted during the **Generate** phase of
the Split-Solve-Reconcile workflow (see `docs/design/SplitSolveReconcile.md`
and `docs/CloudSolving.md`).

The manifest captures everything the **Reconcile** phase needs to turn raw
solver `.result` files into a `VCResults` without re-running the expensive
symbolic-evaluation pipeline:

- per-obligation metadata (label, property type, source location, …),
- a mapping from program variables to SMT identifiers, so models parsed
  from `.result` files can be re-associated with program variables,
- datatype constructor names,
- per-phase "validates?" decisions so phase validators can be reconstructed,
- the subset of `VerifyOptions` that affects classification and display.

The file is versioned; the reconcile phase rejects unknown versions with a
clear error.
-/

namespace Core
open Lean (Json ToJson FromJson)
open Strata

public section

/-! ## Version -/

/-- Current manifest format version. -/
def manifestFormatVersion : Nat := 1

/-! ## Serializable subset of `VerifyOptions` -/

/-- Subset of `VerifyOptions` preserved in the manifest. Only fields that
affect classification, rendering, or are informational for users are stored. -/
structure ManifestOptions where
  /-- Verification mode (deductive, bugFinding, bugFindingAssumingCompleteSpec). -/
  checkMode : String
  /-- Check level (minimal, minimalVerbose, full). -/
  checkLevel : String
  /-- Verbosity (quiet, models, normal, debug). -/
  verbose : String
  deriving Repr, Inhabited

instance : ToJson ManifestOptions where
  toJson o := Json.mkObj [
    ("checkMode", Json.str o.checkMode),
    ("checkLevel", Json.str o.checkLevel),
    ("verbose", Json.str o.verbose)
  ]

instance : FromJson ManifestOptions where
  fromJson? j := do
    let checkMode ← j.getObjValAs? String "checkMode"
    let checkLevel ← j.getObjValAs? String "checkLevel"
    let verbose ← j.getObjValAs? String "verbose"
    return { checkMode, checkLevel, verbose }

/-! ## Source location -/

/-- A source location: file URI + byte-offset range matching
`Strata.SourceRange`. -/
structure ManifestSourceLocation where
  /-- File URI (path string). -/
  file : String
  /-- Starting byte offset. -/
  start : Nat
  /-- One-past-the-end byte offset. -/
  stop : Nat
  deriving Repr, Inhabited, BEq, ToJson, FromJson

/-- Convert a `FileRange` into a `ManifestSourceLocation`. -/
def ManifestSourceLocation.ofFileRange (fr : Strata.FileRange) : ManifestSourceLocation :=
  let path := match fr.file with | .file p => p
  { file := path,
    start := fr.range.start.byteIdx,
    stop := fr.range.stop.byteIdx }

/-- Convert a `ManifestSourceLocation` back into a `FileRange`. -/
def ManifestSourceLocation.toFileRange (loc : ManifestSourceLocation) : Strata.FileRange :=
  { file := .file loc.file,
    range := { start := ⟨loc.start⟩, stop := ⟨loc.stop⟩ } }

/-! ## Per-variable mapping -/

/-- Entry in `obligation.variableMap`: program variable name + Strata type
string + SMT-level identifier (e.g. `$__f.0`). Used during reconcile to
associate solver model values with program variables. -/
structure ManifestVariableEntry where
  /-- Program variable name. -/
  var : String
  /-- A string representation of the Strata type (for debugging/display). -/
  type : String
  /-- The SMT-level identifier (e.g. `$__f.0`). -/
  smtId : String
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Per-phase validation decisions -/

/-- Entry in `obligation.phaseValidation`: one record per pipeline phase
indicating whether the phase would apply `modelToValidate` (currently always
rejecting models) or is `modelPreserving` for this obligation. -/
structure ManifestPhaseEntry where
  /-- The phase name (e.g. "CallElim", "LoopElim"). -/
  phase : String
  /-- True if the phase applied `modelToValidate` to this obligation.
  Currently, a `validates: true` decision means "sat results from this phase
  should be demoted to unknown". -/
  validates : Bool
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Evaluator-resolved outcomes -/

/-- When the evaluator resolves part or all of an obligation without needing
the solver, its result is stored here. Each field is `none` when the
evaluator did not resolve that check, otherwise one of `"sat"`, `"unsat"`,
`"unknown"`. When both fields are set and `smtFile` is `none`, the
obligation was fully resolved by the evaluator (no SMT file). When one
field is set and `smtFile` is present, the solver was called for the
remaining check only. -/
structure ManifestResolvedBySim where
  /-- Result of the satisfiability check (P ∧ Q), if the evaluator
  resolved it. -/
  satisfiability : Option String := none
  /-- Result of the validity check (P ∧ ¬Q), if the evaluator resolved it. -/
  validity : Option String := none
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Per-obligation manifest entry -/

/-- Per-obligation manifest entry. See the design doc for field meanings. -/
structure ManifestObligation where
  /-- Obligation label (e.g. `"assert_precondition_0"`). -/
  label : String
  /-- Property type string: `"assert"`, `"cover"`, `"divisionByZero"`, or
  `"arithmeticOverflow"`. -/
  property : String
  /-- Filename of the `.smt2` file (relative to the VC directory). `none`
  when `resolvedBySim` is set. -/
  smtFile : Option String
  /-- Was the satisfiability check requested? -/
  satisfiabilityCheck : Bool
  /-- Was the validity check requested? -/
  validityCheck : Bool
  /-- Evaluator-resolved result, if any. When set and `smtFile` is `none`,
  the obligation was resolved entirely by the evaluator. When set together
  with `smtFile`, indicates that the evaluator pre-resolved one or both
  checks and the solver was called for the remaining ones; the reconcile
  phase merges the two results. -/
  resolvedBySim : Option ManifestResolvedBySim
  /-- Primary source location. -/
  sourceLocation : Option ManifestSourceLocation
  /-- Related source locations (e.g. the original assertion location before
  inlining). Order follows the call stack: innermost first. -/
  relatedLocations : Array ManifestSourceLocation
  /-- Mirrors `PropertyType.passWhenUnreachable`. -/
  passWhenUnreachable : Bool
  /-- Whether the obligation has a `fullCheck` annotation. -/
  hasFullCheck : Bool
  /-- Variable map for interpreting solver models. -/
  variableMap : Array ManifestVariableEntry
  /-- Datatype constructor names from the SMT context. -/
  constructorNames : Array String
  /-- Per-phase validation decisions. -/
  phaseValidation : Array ManifestPhaseEntry
  /-- Human-readable property summary used as the display label for merging
  and rendering. When absent, the `label` is used as fallback. -/
  propertySummary : Option String := none
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Top-level manifest -/

/-- Top-level manifest. -/
structure Manifest where
  /-- Format version. Reconcile rejects unknown versions. -/
  version : Nat
  /-- Verification options used during generation. -/
  options : ManifestOptions
  /-- All proof obligations. -/
  obligations : Array ManifestObligation
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Conversion helpers -/

/-- Convert a `VerificationMode` to its string form. -/
def VerificationMode.toManifestString : VerificationMode → String
  | .deductive => "deductive"
  | .bugFinding => "bugFinding"
  | .bugFindingAssumingCompleteSpec => "bugFindingAssumingCompleteSpec"

/-- Parse a `VerificationMode` from its string form. Defaults to
`.deductive` on unknown strings. -/
def VerificationMode.ofManifestString (s : String) : VerificationMode :=
  (VerificationMode.ofString? s).getD .deductive

/-- Convert a `CheckLevel` to its string form. -/
def CheckLevel.toManifestString : CheckLevel → String
  | .minimal => "minimal"
  | .minimalVerbose => "minimalVerbose"
  | .full => "full"

/-- Parse a `CheckLevel` from its string form. Defaults to `.minimal`
on unknown strings. -/
def CheckLevel.ofManifestString (s : String) : CheckLevel :=
  (CheckLevel.ofString? s).getD .minimal

/-- Convert a `VerboseMode` to its string form. -/
def VerboseMode.toManifestString : VerboseMode → String
  | .quiet => "quiet"
  | .models => "models"
  | .normal => "normal"
  | .debug => "debug"

/-- Parse a `VerboseMode` from its string form. Defaults to `.normal`
on unknown strings. -/
def VerboseMode.ofManifestString (s : String) : VerboseMode :=
  match s with
  | "quiet" => .quiet
  | "models" => .models
  | "normal" => .normal
  | "debug" => .debug
  | _ => .normal

/-- Convert a `PropertyType` to its manifest string form. -/
def propertyTypeToManifestString : Imperative.PropertyType → String
  | .cover => "cover"
  | .assert => "assert"
  | .divisionByZero => "divisionByZero"
  | .arithmeticOverflow => "arithmeticOverflow"

/-- Parse a `PropertyType` from its manifest string form. Defaults to
`.assert` on unknown strings. -/
def propertyTypeOfManifestString (s : String) : Imperative.PropertyType :=
  match s with
  | "cover" => .cover
  | "assert" => .assert
  | "divisionByZero" => .divisionByZero
  | "arithmeticOverflow" => .arithmeticOverflow
  | _ => .assert

/-- Build a `ManifestOptions` from the full `VerifyOptions`. -/
def ManifestOptions.ofVerifyOptions (o : VerifyOptions) : ManifestOptions :=
  { checkMode := VerificationMode.toManifestString o.checkMode,
    checkLevel := CheckLevel.toManifestString o.checkLevel,
    verbose := VerboseMode.toManifestString o.verbose }

/-- Convert a `Core.SMT.Result` (short verdict) to its manifest string form.
Models are dropped — only the verdict is serialized. -/
def smtResultToManifestString (r : Core.SMT.Result) : String :=
  match r with
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .unknown _ => "unknown"
  | .err _ => "err"

/-- Parse a manifest verdict string into a `Core.SMT.Result` with no model.
The `"err"` case wraps a generic error message; truly authoritative error
information should be preserved by callers before serialization. -/
def smtResultOfManifestString (s : String) : Core.SMT.Result :=
  match s with
  | "sat" => .sat []
  | "unsat" => .unsat
  | "unknown" => .unknown
  | _ => .err s!"manifest:err({s})"

/-! ## Building manifest entries

`ManifestObligation.ofSim` and `ManifestObligation.ofSolver` build entries from
data already computed by the verification pipeline. They live in `Manifest.lean`
(not `Verifier.lean`) so that the serialization schema stays co-located with
the struct definitions. -/

/-- Render a Strata type to a short debug string for the manifest. -/
def renderTyForManifest (ty : Lambda.LTy) : String := toString (Std.format ty)

/-- Build the primary source-location / related-locations fields from an
obligation's metadata. -/
def buildSourceLocations (md : Imperative.MetaData Expression) :
    Option ManifestSourceLocation × Array ManifestSourceLocation :=
  let primary := (Imperative.getFileRange md).map ManifestSourceLocation.ofFileRange
  let related := (Imperative.getRelatedFileRanges md).map ManifestSourceLocation.ofFileRange
  (primary, related)

/-- Build a `ManifestObligation` entry for an obligation that will need the
solver. `typedVars` / `estate` come from the SMT encoder; `ctx` supplies
constructor names. `smtFileRelative` is the `.smt2` filename (relative to
the VC directory) that was written during the generate phase. If the
evaluator also pre-resolved one or both checks, pass them via
`peSatResult?` / `peValResult?` — those results will override the solver
output during reconcile. -/
def ManifestObligation.ofSolver
    (obligation : Imperative.ProofObligation Expression)
    (typedVars : List Expression.TypedIdent)
    (ctx : _root_.Core.SMT.Context) (estate : Strata.SMT.EncoderState)
    (satisfiabilityCheck validityCheck : Bool)
    (peSatResult? peValResult? : Option Core.SMT.Result)
    (smtFileRelative : String)
    (phaseEntries : Array ManifestPhaseEntry) : ManifestObligation :=
  let (primaryLoc, relatedLocs) := buildSourceLocations obligation.metadata
  -- Variable map: for each typed program variable, look up its SMT id via
  -- the encoder's UF table.
  let variableMap : Array ManifestVariableEntry :=
    typedVars.toArray.filterMap fun (ident, ty) =>
      match Imperative.SMT.getSMTId (_root_.Core.SMT.typedVarToSMTFn ctx) ident (some ty) estate with
      | .ok smtId =>
        some { var := toString ident, type := renderTyForManifest ty, smtId := smtId }
      | .error _ => none
  let constructorNames :=
    (_root_.Core.SMT.Context.getConstructorNames ctx).toArray
  let resolved : Option ManifestResolvedBySim :=
    if peSatResult?.isNone && peValResult?.isNone then none
    else some {
      satisfiability := peSatResult?.map smtResultToManifestString,
      validity := peValResult?.map smtResultToManifestString
    }
  { label := obligation.label,
    property := propertyTypeToManifestString obligation.property,
    smtFile := some smtFileRelative,
    satisfiabilityCheck,
    validityCheck,
    resolvedBySim := resolved,
    sourceLocation := primaryLoc,
    relatedLocations := relatedLocs,
    passWhenUnreachable := obligation.property.passWhenUnreachable,
    hasFullCheck := Imperative.MetaData.hasFullCheck obligation.metadata,
    variableMap,
    constructorNames,
    phaseValidation := phaseEntries,
    propertySummary := obligation.metadata.getPropertySummary }

/-- Build a `ManifestObligation` entry for an obligation that was resolved
entirely by the evaluator (no SMT file written). -/
def ManifestObligation.ofSim
    (obligation : Imperative.ProofObligation Expression)
    (satisfiabilityCheck validityCheck : Bool)
    (satResult valResult : Core.SMT.Result)
    (phaseEntries : Array ManifestPhaseEntry) : ManifestObligation :=
  let (primaryLoc, relatedLocs) := buildSourceLocations obligation.metadata
  { label := obligation.label,
    property := propertyTypeToManifestString obligation.property,
    smtFile := none,
    satisfiabilityCheck,
    validityCheck,
    resolvedBySim := some {
      satisfiability := some (smtResultToManifestString satResult),
      validity := some (smtResultToManifestString valResult)
    },
    sourceLocation := primaryLoc,
    relatedLocations := relatedLocs,
    passWhenUnreachable := obligation.property.passWhenUnreachable,
    hasFullCheck := Imperative.MetaData.hasFullCheck obligation.metadata,
    variableMap := #[],
    constructorNames := #[],
    phaseValidation := phaseEntries,
    propertySummary := obligation.metadata.getPropertySummary }

/-- Compute the per-phase validation decisions for an obligation. For each
phase, records whether its `getValidation` returned `modelToValidate` (true)
or `modelPreserving` (false). -/
def buildPhaseEntries (phases : List AbstractedPhase)
    (obligation : Imperative.ProofObligation Expression) : Array ManifestPhaseEntry :=
  phases.toArray.map fun p =>
    let validates := match p.getValidation obligation with
      | .modelToValidate _ => true
      | .modelPreserving => false
    { phase := p.name, validates }

/-! ## Phase validation reconstruction (Task 4)

Build an `AbstractedPhase` equivalent from manifest entries. Currently all
real validators always return `false`, so we model `validates: true` with a
validator that also returns `false` (i.e. rejects all models). See the design
doc for a discussion of why this suffices today and when the design must
revisit. -/

/-- Reconstruct `AbstractedPhase`s from manifest phase entries. Phases with
`validates: true` become `modelToValidate (fun _ => false)` (matching the
current TODO stub behavior, which demotes sat to unknown). Phases with
`validates: false` become `modelPreserving`. -/
def reconstructPhaseValidation (entries : Array ManifestPhaseEntry) :
    List AbstractedPhase :=
  entries.toList.map fun entry =>
    { name := entry.phase,
      getValidation := fun _ =>
        if entry.validates then
          .modelToValidate (fun _ => false)
        else
          .modelPreserving }

/-! ## Result file parsing (Task 3)

The `.result` file contains exactly what the solver prints to stdout — one or
two verdict lines (`sat` / `unsat` / `unknown`), optionally followed by
`(get-value ...)` output. We take the simple approach described in the
design doc: extract only verdicts, leaving models as empty. This keeps model
display SMT-level for the reconcile phase; rich Core-level rendering is a
future extension. -/

/-- Classify a raw line as a verdict, if any. -/
private def lineVerdict? (line : String) : Option Core.SMT.Result :=
  match line.trimAscii.toString with
  | "sat" => some (.sat [])
  | "unsat" => some .unsat
  | "unknown" => some .unknown
  | _ => none

/-- Parse a `.result` file's contents into `(satResult, valResult)`. When a
check was not requested, its result is `.unknown`. When a requested verdict
cannot be found, the corresponding slot is `.err "<missing>"`. Any models
referenced by subsequent `(get-value …)` output are **not** parsed; the
returned `sat` has an empty model. -/
def parseResultFile (content : String)
    (satisfiabilityCheck validityCheck : Bool) :
    Core.SMT.Result × Core.SMT.Result :=
  let lines := content.splitOn "\n"
  let verdicts := lines.filterMap lineVerdict?
  match satisfiabilityCheck, validityCheck with
  | true, true =>
    match verdicts with
    | v1 :: v2 :: _ => (v1, v2)
    | [v1] => (v1, .err "missing validity verdict")
    | _ => (.err "missing satisfiability verdict", .err "missing validity verdict")
  | true, false =>
    match verdicts with
    | v1 :: _ => (v1, .unknown)
    | [] => (.err "missing satisfiability verdict", .unknown)
  | false, true =>
    match verdicts with
    | v1 :: _ => (.unknown, v1)
    | [] => (.unknown, .err "missing validity verdict")
  | false, false =>
    (.unknown, .unknown)

/-- Read a `.result` file from disk and parse it. Missing files are reported
as `.err` results so the reconcile phase can continue with the rest of the
obligations. -/
def readResultFile (path : System.FilePath)
    (satisfiabilityCheck validityCheck : Bool) :
    IO (Core.SMT.Result × Core.SMT.Result) := do
  let exists_? ← path.pathExists
  if !exists_? then
    let msg := s!"result file not found: {path}"
    return (.err msg, .err msg)
  let content ← IO.FS.readFile path
  return parseResultFile content satisfiabilityCheck validityCheck

/-! ## Manifest I/O -/

/-- Standard manifest filename inside the VC directory. -/
def manifestFileName : String := "manifest.json"

/-- Path to the manifest file inside a VC directory. -/
def manifestFilePath (vcDir : System.FilePath) : System.FilePath :=
  vcDir / manifestFileName

/-- Write the manifest as pretty-printed JSON to `vcDir/manifest.json`. -/
def writeManifest (vcDir : System.FilePath) (m : Manifest) : IO Unit := do
  let path := manifestFilePath vcDir
  let json := ToJson.toJson m
  IO.FS.writeFile path.toString (Lean.Json.pretty json)

/-- Read and parse `vcDir/manifest.json`. -/
def readManifest (vcDir : System.FilePath) : IO (Except String Manifest) := do
  let path := manifestFilePath vcDir
  let exists_? ← path.pathExists
  if !exists_? then
    return .error s!"manifest file not found at {path}"
  let content ← IO.FS.readFile path.toString
  match Lean.Json.parse content with
  | .error e => return .error s!"failed to parse manifest JSON: {e}"
  | .ok j =>
    match FromJson.fromJson? (α := Manifest) j with
    | .error e => return .error s!"invalid manifest: {e}"
    | .ok m =>
      if m.version != manifestFormatVersion then
        return .error s!"manifest version {m.version} not supported; expected {manifestFormatVersion}"
      return .ok m

/-! ## Manifest-emitting verify callbacks

Build `VerifyCallbacks` that append `ManifestObligation` entries to a shared
`IO.Ref` as the verifier runs. The reference is consumed after `verify`
completes to assemble the full `Manifest`. -/

/-- Build `VerifyCallbacks` that accumulate manifest entries into `ref`. -/
def manifestEmittingCallbacks
    (ref : IO.Ref (Array ManifestObligation)) : VerifyCallbacks where
  onSolverObligation obligation typedVars ctx estate satCheck valCheck
      peSatResult? peValResult? smtFilePath phases := do
    -- Store a path relative to the VC directory (just the filename).
    let relative : String :=
      let absPath := System.FilePath.mk smtFilePath
      match absPath.fileName with
      | some name => name
      | none => smtFilePath
    let phaseEntries := buildPhaseEntries phases obligation
    let entry := ManifestObligation.ofSolver obligation typedVars ctx estate
      satCheck valCheck peSatResult? peValResult? relative phaseEntries
    ref.modify (·.push entry)
  onSimObligation obligation satResult valResult satCheck valCheck phases := do
    let phaseEntries := buildPhaseEntries phases obligation
    let entry := ManifestObligation.ofSim obligation satCheck valCheck
      satResult valResult phaseEntries
    ref.modify (·.push entry)

/-- Assemble and write the manifest file given the verify options and the
collected obligation entries. -/
def emitManifest (vcDir : System.FilePath) (options : VerifyOptions)
    (entries : Array ManifestObligation) : IO Unit := do
  let manifest : Manifest := {
    version := manifestFormatVersion,
    options := ManifestOptions.ofVerifyOptions options,
    obligations := entries }
  writeManifest vcDir manifest

end -- public section
end Core

/-! ## Top-level wrapper: verify + emit manifest -/

namespace Strata

open Lean.Parser

public section

/-- Drop-in replacement for `Strata.verify` that additionally writes a
`manifest.json` to `options.vcDirectory` when `options.skipSolver` is true.
This is the entry point used by the `strata verify --no-solve` path to
produce artifacts for the Split-Solve-Reconcile workflow. -/
def verifyWithManifest
    (env : Program)
    (ictx : InputContext := Inhabited.default)
    (proceduresToVerify : Option (List String) := none)
    (options : Core.VerifyOptions := Core.VerifyOptions.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (externalPhases : List Core.AbstractedPhase := [])
    (keepAllFilesPrefix : Option String := none)
    : IO Core.VCResults := do
  if options.skipSolver then
    match options.vcDirectory with
    | none =>
      -- Not possible in practice: the CLI enforces vcDirectory when
      -- --no-solve is requested. Fall back to plain verify just in case.
      Strata.verify env ictx proceduresToVerify options moreFns externalPhases keepAllFilesPrefix
    | some vcDir =>
      let ref ← IO.mkRef (#[] : Array Core.ManifestObligation)
      let callbacks := Core.manifestEmittingCallbacks ref
      let results ← Strata.verify env ictx proceduresToVerify options moreFns
        externalPhases keepAllFilesPrefix (callbacks := callbacks)
      let entries ← ref.get
      Core.emitManifest vcDir options entries
      return results
  else
    Strata.verify env ictx proceduresToVerify options moreFns externalPhases keepAllFilesPrefix

end -- public section
end Strata
