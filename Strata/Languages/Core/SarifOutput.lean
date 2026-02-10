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

/-- Convert Core Outcome to SARIF Level -/
def outcomeToLevel : Outcome → Level
  | .pass => .none
  | .fail => .error
  | .unknown => .warning
  | .implementationError _ => .error

/-- Convert Core Outcome to a descriptive message -/
def outcomeToMessage (outcome : Outcome) (smtResult : SMT.Result) : String :=
  match outcome with
  | .pass => "Verification succeeded"
  | .fail =>
    match smtResult with
    | .sat m =>
      if m.isEmpty then
        "Verification failed"
      else
        s!"Verification failed with counterexample: {Std.format m}"
    | _ => "Verification failed"
  | .unknown => "Verification result unknown (solver timeout or incomplete)"
  | .implementationError msg => s!"Verification error: {msg}"

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
  let level := outcomeToLevel vcr.result
  let messageText := outcomeToMessage vcr.result vcr.smtResult
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
