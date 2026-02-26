/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Util.Sarif

/-!
# Core SARIF Output

This module provides Core-specific conversion functions for SARIF output.
-/

namespace Core.Sarif

open Strata.Sarif Strata.SMT

/-! ## Core-Specific Conversion Functions -/

inductive VerificationMode where
  | deductive  -- Prove correctness (unknown is error)
  | bugFinding -- Find bugs (unknown is warning)

/-- Convert VCOutcome to SARIF Level -/
def outcomeToLevel (mode : VerificationMode) (outcome : VCOutcome) : Level :=
  match mode with
  | .deductive =>
    -- Deductive verification: prove correctness
    if outcome.passAndReachable || outcome.passReachabilityUnknown then 
      .none
    else if outcome.unreachable then 
      .warning -- Dead code
    else 
      .error -- Everything not proven is an error
  | .bugFinding =>
    -- Bug finding: find counterexamples
    if outcome.passAndReachable || outcome.passReachabilityUnknown then 
      .none
    else if outcome.isAlwaysFalse then 
      .error
    else if outcome.indecisiveAndReachable || outcome.canBeFalseAndReachable || outcome.unknown then 
      .warning
    else 
      .note -- unreachable, satisfiableValidityUnknown

/-- Convert VCOutcome to a descriptive message -/
def outcomeToMessage (outcome : VCOutcome) : String :=
  if outcome.passAndReachable then "Verification succeeded: always true and reachable"
  else if outcome.alwaysFalseAndReachable then
    match outcome.validityProperty with
    | .sat m =>
      if m.isEmpty then
        "Verification failed: always false and reachable"
      else
        s!"Verification failed: always false and reachable with counterexample: {Std.format m}"
    | _ => "Verification failed: always false and reachable"
  else if outcome.indecisiveAndReachable then
    let models := match outcome.satisfiabilityProperty, outcome.validityProperty with
      | .sat m1, .sat m2 =>
        if !m1.isEmpty && !m2.isEmpty then
          s!" (true: {Std.format m1}, false: {Std.format m2})"
        else if !m1.isEmpty then
          s!" (true: {Std.format m1})"
        else if !m2.isEmpty then
          s!" (false: {Std.format m2})"
        else ""
      | _, _ => ""
    s!"Verification inconclusive: true or false depending on inputs{models}"
  else if outcome.unreachable then "Path unreachable: path condition is contradictory"
  else if outcome.satisfiableValidityUnknown then "Reachable and can be true, unknown if always true"
  else if outcome.alwaysFalseReachabilityUnknown then
    match outcome.validityProperty with
    | .sat m =>
      if m.isEmpty then
        "Always false if reached, reachability unknown"
      else
        s!"Always false if reached, reachability unknown with counterexample: {Std.format m}"
    | _ => "Always false if reached, reachability unknown"
  else if outcome.canBeFalseAndReachable then
    match outcome.validityProperty with
    | .sat m =>
      if m.isEmpty then
        "Reachable and can be false, unknown if always false"
      else
        s!"Reachable and can be false, unknown if always false with counterexample: {Std.format m}"
    | _ => "Reachable and can be false, unknown if always false"
  else if outcome.passReachabilityUnknown then "Always true if reached, reachability unknown"
  else "Verification result unknown (solver timeout or incomplete)"

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

/-- Convert a VCResult to a SARIF Result -/
def vcResultToSarifResult (files : Map Strata.Uri Lean.FileMap) (vcr : VCResult) : Strata.Sarif.Result :=
  let ruleId := vcr.obligation.label
  match vcr.outcome with
  | .error msg =>
    let level := .error
    let messageText := s!"Verification error: {msg}"
    let message : Strata.Sarif.Message := { text := messageText }
    let locations := match extractLocation files vcr.obligation.metadata with
      | some loc => #[locationToSarif loc]
      | none => #[]
    { ruleId, level, message, locations }
  | .ok outcome =>
    let level := outcomeToLevel .deductive outcome
    let messageText := outcomeToMessage outcome
    let message : Strata.Sarif.Message := { text := messageText }
    let locations := match extractLocation files vcr.obligation.metadata with
      | some loc => #[locationToSarif loc]
      | none => #[]
    { ruleId, level, message, locations }

/-- Convert VCResults to a SARIF document -/
def vcResultsToSarif (files : Map Strata.Uri Lean.FileMap) (vcResults : VCResults) : Strata.Sarif.SarifDocument :=
  let tool : Strata.Sarif.Tool := {
    driver := {
      name := "Strata",
      version := "0.1.0",
      informationUri := "https://github.com/strata-org/Strata"
    }
  }

  let results := vcResults.map (vcResultToSarifResult files)

  let run : Strata.Sarif.Run := { tool, results }

  { version := "2.1.0",
    schema := "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json",
    runs := #[run] }

end Core.Sarif

/-- Write SARIF output for verification results to a file.
    `files` maps source URIs to their file maps for location resolution.
    `vcResults` are the verification results to encode.
    `outputPath` is the path to write the SARIF JSON to. -/
def Core.Sarif.writeSarifOutput
    (files : Map Strata.Uri Lean.FileMap)
    (vcResults : Core.VCResults)
    (outputPath : String) : IO Unit := do
  let sarifDoc := Core.Sarif.vcResultsToSarif files vcResults
  let sarifJson := Strata.Sarif.toPrettyJsonString sarifDoc
  try
    IO.FS.writeFile outputPath sarifJson
    IO.println s!"SARIF output written to {outputPath}"
  catch e =>
    IO.eprintln s!"Error writing SARIF output to {outputPath}: {e.toString}"
