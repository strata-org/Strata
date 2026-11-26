/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Util.Sarif
public import Strata.Languages.Core.Verifier



public section

/-!
# Core SARIF Output

This module provides Core-specific conversion functions for SARIF output.
-/

namespace Core.Sarif

open Strata.Sarif Strata.SMT

/-! ## Core-Specific Conversion Functions -/

/-- Convert VCOutcome to SARIF Level -/
def outcomeToLevel (mode : VerificationMode) (property : Imperative.PropertyType) (outcome : VCOutcome) : Level :=
  match mode, property, outcome.satisfiabilityProperty, outcome.validityProperty with
  -- Cover satisfied (sat on P∧Q): always pass
  | _, .cover, .sat _, _ => .none
  -- Unreachable (both unsat): deductive=warning for assert-like properties
  -- (those that pass vacuously), error for cover and bugFinding modes.
  | .deductive, p, .unsat, .unsat | .deductiveAssumingSatisfiablePaths, p, .unsat, .unsat =>
    if p.passWhenUnreachable then .warning else .error
  | _, _, .unsat, .unsat => .error
  -- Pass: validity proven (unsat on P∧¬Q)
  | _, _, _, .unsat => .none
  -- Always false (sat unsat): error in all modes
  | _, _, .unsat, .sat _ => .error
  -- Always false if reached (unsat unknown): error in all modes
  | _, _, .unsat, _ => .error
  -- Deductive: everything non-pass is error
  | .deductive, _, _, _ | .deductiveAssumingSatisfiablePaths, _, _, _ => .error
  -- BugFinding+CompleteSpec: any counterexample (sat on P∧¬Q) is error
  | .bugFindingAssumingCompleteSpec, _, _, .sat _ => .error
  -- BugFinding: everything else is note
  | _, _, _, _ => .note

/-- Which checks' models the message of an outcome prints: the satisfiability check's (`.1`)
    when both checks are `sat`, and the validity check's (`.2`) when that check is `sat` and the
    satisfiability check is `sat`, `unsat` or `unknown`. -/
def outcomePrintedChecks (outcome : VCOutcome) : Bool × Bool :=
  match outcome.satisfiabilityProperty, outcome.validityProperty with
  | .sat _, .sat _ => (true, true)
  | .unsat, .sat _ | .unknown _, .sat _ => (false, true)
  | _, _ => (false, false)

/-- The model a message prints for a check with result `r`, given that check's component `model`
    of `VCResult.checkModels`: `model` when it is `some`, else the model `r` carries when it is
    `sat`; `none` when that model is empty or there is none. -/
def printedCheckModel (r : SMT.Result) : Option LExprModel → Option Std.Format
  | some m => if m.isEmpty then none else some (Std.format m)
  | none => match r with
    | .sat m => if m.isEmpty then none else some (Std.format m)
    | _ => none

/-- Convert VCOutcome to a descriptive message. Each check's model the message prints
    (`outcomePrintedChecks`) is `printedCheckModel` of that check's result and of its component
    of `models` (`.1` for the satisfiability check, `.2` for the validity check, as in
    `VCResult.checkModels`). -/
def outcomeToMessage (outcome : VCOutcome)
    (models : Option LExprModel × Option LExprModel := (none, none)) : String :=
  let m1 := printedCheckModel outcome.satisfiabilityProperty models.1
  let m2 := printedCheckModel outcome.validityProperty models.2
  match outcome.satisfiabilityProperty, outcome.validityProperty with
  | .sat _, .unsat => "Always true and reachable"
  | .unsat, .sat _ =>
    match m2 with
    | none => "Always false and reachable"
    | some m => s!"Always false and reachable with counterexample: {m}"
  | .sat _, .sat _ =>
    let shownModels := match m1, m2 with
      | some m1, some m2 => s!" (true: {m1}, false: {m2})"
      | some m1, none => s!" (true: {m1})"
      | none, some m2 => s!" (false: {m2})"
      | none, none => ""
    s!"True or false depending on inputs{shownModels}"
  | .unsat, .unsat => "Unreachable in this context"
  | .sat _, .unknown _ => "Can be true, unknown if always true"
  | .unsat, .unknown _ => "Always false if reached, reachability unknown"
  | .unknown _, .sat _ =>
    match m2 with
    | none => "Can be false and is reachable, unknown if always false"
    | some m => s!"Can be false and is reachable, unknown if always false with counterexample: {m}"
  | .unknown _, .unsat => "Always true if reached, reachability unknown"
  | .unknown _, .unknown _ => "Unknown (solver timeout or incomplete)"
  | .sat _, .err msg => s!"Validity check error: {msg}"
  | .unsat, .err msg => s!"Validity check error: {msg}"
  | .unknown _, .err msg => s!"Validity check error: {msg}"
  | .err msg, .sat _ => s!"Satisfiability check error: {msg}"
  | .err msg, .unsat => s!"Satisfiability check error: {msg}"
  | .err msg, .unknown _ => s!"Satisfiability check error: {msg}"
  | .err msg1, .err msg2 => s!"Both checks error: sat={msg1}, val={msg2}"

/-- The partial-model marker of the models `outcomeToMessage outcome models` prints, given the
    variables the satisfiability check's model (`satMissing`) and the validity check's model
    (`valMissing`) have no value for, each read only when that check's component of `models` is
    `some`: `partialModelMarkerOf` of the one printed model's variables, or, when the true and
    the false model are both printed, ` (partial; the true model has no value for …; the false
    model has no value for …)` naming each partial one's; the empty string when no printed model
    is partial. -/
def outcomePartialModelMarker (outcome : VCOutcome)
    (models : Option LExprModel × Option LExprModel) (satMissing valMissing : List String) :
    String :=
  let (p1, p2) := outcomePrintedChecks outcome
  let shown1 := p1 && (printedCheckModel outcome.satisfiabilityProperty models.1).isSome
  let shown2 := p2 && (printedCheckModel outcome.validityProperty models.2).isSome
  let satMissing := if models.1.isSome then satMissing else []
  let valMissing := if models.2.isSome then valMissing else []
  if shown1 && shown2 then
    let parts := [("true", satMissing), ("false", valMissing)].filterMap fun (k, vs) =>
      if vs.isEmpty then none else some s!"the {k} model has no value for {", ".intercalate vs}"
    if parts.isEmpty then "" else s!" (partial; {"; ".intercalate parts})"
  else if shown2 then partialModelMarkerOf valMissing
  else if shown1 then partialModelMarkerOf satMissing
  else ""

/-- The message text of `vcr` in outcome `outcome`: `outcomeToMessage` of the per-check models
    `vcr.checkModels`, followed by their partial-model marker (`outcomePartialModelMarker` of
    `vcr.checkModelMissing`). A check whose component is `none` prints the model its own result
    carries and contributes no partial-model marker. -/
def sarifMessage (vcr : VCResult) (outcome : VCOutcome) : String :=
  outcomeToMessage outcome vcr.checkModels ++
    outcomePartialModelMarker outcome vcr.checkModels vcr.checkModelMissing.1
      vcr.checkModelMissing.2

/-- Extract location information from metadata -/
def extractLocation (files : Map Strata.Uri Lean.FileMap) (md : Imperative.MetaData Expression) : Option Location := do
  let fr ← Imperative.getFileRange md
  let fileMap ← files.find? fr.file
  let startPos := fileMap.toPosition fr.range.start
  let uri := match fr.file with
             | .file path => path
  pure { uri, startLine := startPos.line, startColumn := startPos.column }

/-- Convert PropertyType to a property classification string for SARIF output -/
def propertyTypeToClassification : Imperative.PropertyType → String
  | .divisionByZero => "division-by-zero"
  | .arithmeticOverflow => "arithmetic-overflow"
  | .outOfBoundsAccess => "out-of-bounds-access"
  | .cover => "cover"
  | .assert => "assert"

/-- Extract related location information from metadata (e.g., original assertion location). -/
def extractRelatedLocations (files : Map Strata.Uri Lean.FileMap) (md : Imperative.MetaData Expression) : Array Strata.Sarif.RelatedLocation :=
  let ranges := Imperative.getRelatedFileRanges md
  ranges.foldl (init := (#[], 1)) (fun (acc, idx) fr =>
    match files.find? fr.file with
    | none => (acc, idx)
    | some fileMap =>
      let startPos := fileMap.toPosition fr.range.start
      let uri := match fr.file with | .file path => path
      let physLoc : Strata.Sarif.PhysicalLocation := {
        artifactLocation := { uri },
        region := { startLine := startPos.line, startColumn := startPos.column }
      }
      (acc.push { id := idx, physicalLocation := physLoc, message := { text := "original assertion location" } }, idx + 1)
  ) |>.1

/-- Convert a VCResult to a SARIF Result, with the message `sarifMessage`. -/
def vcResultToSarifResult (mode : VerificationMode) (files : Map Strata.Uri Lean.FileMap) (vcr : VCResult) : Strata.Sarif.Result :=
  let ruleId := vcr.obligation.label
  let relatedLocations := extractRelatedLocations files vcr.obligation.metadata
  let properties : Strata.Sarif.PropertyBag :=
    { propertyType := propertyTypeToClassification vcr.obligation.property }
  let locations := match extractLocation files vcr.obligation.metadata with
    | some loc => #[locationToSarif loc]
    | none => #[]
  -- An obligation a stopped run did not ask is neither a failure nor an error of Strata.
  if let some why := vcr.notChecked then
    { ruleId, level := .warning, message := { text := s!"Not checked: {why}" }, locations,
      relatedLocations, properties } else
  match vcr.outcome with
  | .error err =>
    let level := .error
    let messageText := s!"Verification error: {err}"
    let message : Strata.Sarif.Message := { text := messageText }
    { ruleId, level, message, locations, relatedLocations, properties }
  | .ok outcome =>
    let level := outcomeToLevel mode vcr.obligation.property outcome
    let messageText := sarifMessage vcr outcome
    let message : Strata.Sarif.Message := { text := messageText }
    { ruleId, level, message, locations, relatedLocations, properties }

/-- Convert VCResults to a SARIF document -/
def vcResultsToSarif (mode : VerificationMode) (files : Map Strata.Uri Lean.FileMap) (vcResults : VCResults) : Strata.Sarif.SarifDocument :=
  let tool : Strata.Sarif.Tool := {
    driver := {
      name := "Strata",
      version := "0.1.0",
      informationUri := "https://github.com/strata-org/Strata"
    }
  }

  let results := vcResults.map (vcResultToSarifResult mode files)

  let run : Strata.Sarif.Run := { tool, results }

  { version := "2.1.0",
    schema := "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json",
    runs := #[run] }

end Core.Sarif

/-- Write SARIF output for verification results to a file.
    `mode` is the verification mode (deductive or bugFinding) for error level mapping.
    `files` maps source URIs to their file maps for location resolution.
    `vcResults` are the verification results to encode.
    `outputPath` is the path to write the SARIF JSON to. -/
def Core.Sarif.writeSarifOutput
    (mode : VerificationMode)
    (files : Map Strata.Uri Lean.FileMap)
    (vcResults : Core.VCResults)
    (outputPath : String) : IO Unit := do
  let sarifDoc := Core.Sarif.vcResultsToSarif mode files vcResults
  let sarifJson := Strata.Sarif.toPrettyJsonString sarifDoc
  try
    IO.FS.writeFile outputPath sarifJson
    IO.eprintln s!"SARIF output written to {outputPath}"
  catch e =>
    IO.eprintln s!"Error writing SARIF output to {outputPath}: {e.toString}"
