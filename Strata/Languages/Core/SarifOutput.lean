/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

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
  -- Unreachable (both unsat): deductive=warning for assert/divisionByZero/arithmeticOverflow, error for cover and bugFinding modes
  | .deductive, p, .unsat, .unsat => if p.passWhenUnreachable then .warning else .error
  | _, _, .unsat, .unsat => .error
  -- Pass: validity proven (unsat on P∧¬Q)
  | _, _, _, .unsat => .none
  -- Always false (sat unsat): error in all modes
  | _, _, .unsat, .sat _ => .error
  -- Always false if reached (unsat unknown): error in all modes
  | _, _, .unsat, _ => .error
  -- Deductive: everything non-pass is error
  | .deductive, _, _, _ => .error
  -- BugFinding+CompleteSpec: any counterexample (sat on P∧¬Q) is error
  | .bugFindingAssumingCompleteSpec, _, _, .sat _ => .error
  -- BugFinding: everything else is note
  | _, _, _, _ => .note

/-- Convert VCOutcome to a descriptive message -/
def outcomeToMessage (outcome : VCOutcome) : String :=
  match outcome.satisfiabilityProperty, outcome.validityProperty with
  | .sat _, .unsat => "Always true and reachable"
  | .unsat, .sat m =>
    if m.isEmpty then "Always false and reachable"
    else s!"Always false and reachable with counterexample: {Std.format m}"
  | .sat m1, .sat m2 =>
    let models :=
      if !m1.isEmpty && !m2.isEmpty then s!" (true: {Std.format m1}, false: {Std.format m2})"
      else if !m1.isEmpty then s!" (true: {Std.format m1})"
      else if !m2.isEmpty then s!" (false: {Std.format m2})"
      else ""
    s!"True or false depending on inputs{models}"
  | .unsat, .unsat => "Unreachable: path condition is contradictory"
  | .sat _, .unknown _ => "Can be true, unknown if always true"
  | .unsat, .unknown _ => "Always false if reached, reachability unknown"
  | .unknown _, .sat m =>
    if m.isEmpty then "Can be false and is reachable, unknown if always false"
    else s!"Can be false and is reachable, unknown if always false with counterexample: {Std.format m}"
  | .unknown _, .unsat => "Always true if reached, reachability unknown"
  | .unknown _, .unknown _ => "Unknown (solver timeout or incomplete)"
  | .sat _, .err msg => s!"Validity check error: {msg}"
  | .unsat, .err msg => s!"Validity check error: {msg}"
  | .unknown _, .err msg => s!"Validity check error: {msg}"
  | .err msg, .sat _ => s!"Satisfiability check error: {msg}"
  | .err msg, .unsat => s!"Satisfiability check error: {msg}"
  | .err msg, .unknown _ => s!"Satisfiability check error: {msg}"
  | .err msg1, .err msg2 => s!"Both checks error: sat={msg1}, val={msg2}"

/-- Extract location information from metadata -/
def extractLocation (files : Map Strata.Uri Lean.FileMap) (md : Imperative.MetaData Expression) : Option Location := do
  let fileRangeElem ← md.findElem Imperative.MetaData.fileRange
  match fileRangeElem.value with
  | .fileRange fr =>
    let fileMap ← files.find? fr.file
    let startPos := fileMap.toPosition fr.range.start
    let uri := match fr.file with
               | .file path => path
    pure { uri, startLine := startPos.line, startColumn := startPos.column }
  | _ => none

/-- Convert PropertyType to a property classification string for SARIF output -/
def propertyTypeToClassification : Imperative.PropertyType → String
  | .divisionByZero => "division-by-zero"
  | .arithmeticOverflow => "arithmetic-overflow"
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

/-- Convert a VCResult to a SARIF Result -/
def vcResultToSarifResult (mode : VerificationMode) (files : Map Strata.Uri Lean.FileMap) (vcr : VCResult) : Strata.Sarif.Result :=
  let ruleId := vcr.obligation.label
  let relatedLocations := extractRelatedLocations files vcr.obligation.metadata
  match vcr.outcome with
  | .error err =>
    let level := .error
    let messageText := s!"Verification error: {err}"
    let message : Strata.Sarif.Message := { text := messageText }
    let locations := match extractLocation files vcr.obligation.metadata with
      | some loc => #[locationToSarif loc]
      | none => #[]
    { ruleId, level, message, locations, relatedLocations }
  | .ok outcome =>
    let level := outcomeToLevel mode vcr.obligation.property outcome
    let messageText := outcomeToMessage outcome
    let message : Strata.Sarif.Message := { text := messageText }
    let locations := match extractLocation files vcr.obligation.metadata with
      | some loc => #[locationToSarif loc]
      | none => #[]
    { ruleId, level, message, locations, relatedLocations }

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
