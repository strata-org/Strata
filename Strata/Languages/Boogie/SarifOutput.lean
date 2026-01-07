/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier
import Strata.Util.Sarif

/-!
# Boogie SARIF Output

This module provides Boogie-specific conversion functions for SARIF output.
-/

namespace Boogie.Sarif

open Strata.Sarif

/-! ## Boogie-Specific Conversion Functions -/

/-- Convert Boogie Result to SARIF Level -/
def resultToLevel : Boogie.Result → Level
  | .unsat => .none      -- Verification passed
  | .sat _ => .error     -- Verification failed (counterexample found)
  | .unknown => .warning -- Solver could not determine
  | .err _ => .error     -- Error during verification

/-- Convert Boogie Result to a descriptive message -/
def resultToMessage : Boogie.Result → String
  | .unsat => "Verification succeeded"
  | .sat cex =>
    if cex.isEmpty then
      "Verification failed"
    else
      s!"Verification failed with counterexample: {Std.format cex}"
  | .unknown => "Verification result unknown (solver timeout or incomplete)"
  | .err msg => s!"Verification error: {msg}"

/-- Extract location information from metadata -/
def extractLocation (md : Imperative.MetaData Expression) : Option Location := do
  let file ← md.findElem Imperative.MetaData.fileLabel
  let line ← md.findElem Imperative.MetaData.startLineLabel
  let col ← md.findElem Imperative.MetaData.startColumnLabel

  let uri? := match file.value with
              | .msg m => some m
              | _ => none

  let startLine? := match line.value with
                    | .msg s => s.toNat?
                    | _ => none

  let startColumn? := match col.value with
                      | .msg s => s.toNat?
                      | _ => none

  match uri?, startLine?, startColumn? with
  | some uri, some startLine, some startColumn => pure { uri, startLine, startColumn }
  | some uri, some startLine, none => pure { uri, startLine, startColumn := 1 }
  | some uri, none, some startColumn => pure { uri, startLine := 1, startColumn }
  | some uri, none, none => pure { uri, startLine := 1, startColumn := 1 }
  | none, _, _ => none

/-- Convert a VCResult to a SARIF Result -/
def vcResultToSarifResult (vcr : VCResult) : Strata.Sarif.Result :=
  let ruleId := vcr.obligation.label
  let level := resultToLevel vcr.result
  let messageText := resultToMessage vcr.result
  let message : Strata.Sarif.Message := { text := messageText }

  let locations := match extractLocation vcr.obligation.metadata with
    | some loc => #[locationToSarif loc]
    | none => #[]

  { ruleId, level, message, locations }

/-- Convert VCResults to a SARIF document -/
def vcResultsToSarif (vcResults : VCResults) : Strata.Sarif.SarifDocument :=
  let tool : Strata.Sarif.Tool := {
    driver := {
      name := "Strata",
      version := "0.1.0",
      informationUri := "https://github.com/strata-org/Strata"
    }
  }

  let results := vcResults.map vcResultToSarifResult

  let run : Strata.Sarif.Run := { tool, results }

  { version := "2.1.0",
    schema := "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json",
    runs := #[run] }

end Boogie.Sarif
