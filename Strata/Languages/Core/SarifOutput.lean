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
      .error -- alwaysFalseAndReachable, alwaysFalseReachabilityUnknown, indecisiveAndReachable, canBeFalseAndReachable, satisfiableValidityUnknown, unknown
  | .bugFinding =>
    -- Bug finding: find counterexamples
    if outcome.passAndReachable || outcome.passReachabilityUnknown then
      .none
    else if outcome.alwaysFalseAndReachable || outcome.alwaysFalseReachabilityUnknown then
      .error
    else if outcome.unreachable then
      .warning -- Proved something that could indicate an issue
    else
      .note -- indecisiveAndReachable, canBeFalseAndReachable, unknown, satisfiableValidityUnknown

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
  | .sat _, .unknown => "Can be true, unknown if always true"
  | .unsat, .unknown => "Always false if reachable, reachability unknown"
  | .unknown, .sat m =>
    if m.isEmpty then "Can be false and reachable, unknown if always false"
    else s!"Can be false and reachable, unknown if always false with counterexample: {Std.format m}"
  | .unknown, .unsat => "Always true if reachable, reachability unknown"
  | .unknown, .unknown => "Unknown (solver timeout or incomplete)"
  | .sat _, .err msg => s!"Validity check error: {msg}"
  | .unsat, .err msg => s!"Validity check error: {msg}"
  | .unknown, .err msg => s!"Validity check error: {msg}"
  | .err msg, .sat _ => s!"Satisfiability check error: {msg}"
  | .err msg, .unsat => s!"Satisfiability check error: {msg}"
  | .err msg, .unknown => s!"Satisfiability check error: {msg}"
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

/-- Convert a VCResult to a SARIF Result -/
def vcResultToSarifResult (mode : VerificationMode) (files : Map Strata.Uri Lean.FileMap) (vcr : VCResult) : Strata.Sarif.Result :=
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
    let level := outcomeToLevel mode outcome
    let messageText := outcomeToMessage outcome
    let message : Strata.Sarif.Message := { text := messageText }
    let locations := match extractLocation files vcr.obligation.metadata with
      | some loc => #[locationToSarif loc]
      | none => #[]
    { ruleId, level, message, locations }

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
    IO.println s!"SARIF output written to {outputPath}"
  catch e =>
    IO.eprintln s!"Error writing SARIF output to {outputPath}: {e.toString}"
