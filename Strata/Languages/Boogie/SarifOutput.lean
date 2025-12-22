/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier
import Lean.Data.Json

/-!
# SARIF Output

This module provides support for outputting verification results in SARIF
(Static Analysis Results Interchange Format) version 2.1.0.

SARIF specification: https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html
-/

namespace Boogie.Sarif

open Lean (Json ToJson FromJson)

/-! ## SARIF Data Structures -/

/-- SARIF location representing a position in source code -/
structure Location where
  uri : String
  startLine : Nat
  startColumn : Nat
  deriving Repr, ToJson, FromJson, BEq

/-- SARIF artifact location representing a file URI -/
structure ArtifactLocation where
  uri : String
  deriving Repr, ToJson, FromJson

/-- SARIF region representing a source code region with line and column information -/
structure Region where
  startLine : Nat
  startColumn : Nat
  deriving Repr, ToJson, FromJson

/-- SARIF physical location with region information -/
structure PhysicalLocation where
  artifactLocation : ArtifactLocation
  region : Region
  deriving Repr, ToJson, FromJson

/-- SARIF location wrapper -/
structure SarifLocation where
  physicalLocation : PhysicalLocation
  deriving Repr, ToJson, FromJson

/-- SARIF message -/
structure Message where
  text : String
  deriving Repr, ToJson, FromJson

/-- SARIF result level -/
inductive Level where
  | none     -- Verification passed
  | note     -- Informational
  | warning  -- Unknown result or potential issue
  | error    -- Verification failed
  deriving Repr, DecidableEq

instance : ToString Level where
  toString
  | .none => "none"
  | .note => "note"
  | .warning => "warning"
  | .error => "error"

instance : ToJson Level where
  toJson level := Json.str (toString level)

instance : FromJson Level where
  fromJson? j := do
    let s ← j.getStr?
    match s with
    | "none" => pure .none
    | "note" => pure .note
    | "warning" => pure .warning
    | "error" => pure .error
    | _ => throw s!"Invalid SARIF level: {s}"

/-- SARIF result representing a single verification result -/
structure Result where
  ruleId : String
  level : Level
  message : Message
  locations : Array SarifLocation := #[]
  deriving Repr, ToJson, FromJson

instance : Inhabited Result where
  default := { ruleId := "", level := .none, message := { text := "" } }

/-- SARIF tool driver information -/
structure Driver where
  name : String
  version : String := "0.1.0"
  informationUri : String := "https://github.com/strata-org/Strata"
  deriving Repr, ToJson, FromJson, Inhabited

/-- SARIF tool information -/
structure Tool where
  driver : Driver
  deriving Repr, ToJson, FromJson, Inhabited

/-- SARIF run representing a single analysis run -/
structure Run where
  tool : Tool
  results : Array Result
  deriving Repr, ToJson, FromJson

instance : Inhabited Run where
  default := { tool := default, results := #[] }

/-- Top-level SARIF document -/
structure SarifDocument where
  version : String := "2.1.0"
  /-- Schema URI as specified by SARIF 2.1.0 -/
  schema : String := "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json"
  runs : Array Run
  deriving Repr, ToJson, FromJson

/-! ## Conversion Functions -/

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

/-- Convert a location to SARIF format -/
def locationToSarif (loc : Location) : SarifLocation :=
  let artifactLocation : ArtifactLocation := { uri := loc.uri }
  let region : Region := { startLine := loc.startLine, startColumn := loc.startColumn }
  { physicalLocation := { artifactLocation, region } }

/-- Convert a VCResult to a SARIF Result -/
def vcResultToSarifResult (vcr : VCResult) : Result :=
  let ruleId := vcr.obligation.label
  let level := resultToLevel vcr.result
  let messageText := resultToMessage vcr.result
  let message : Message := { text := messageText }

  let locations := match extractLocation vcr.obligation.metadata with
    | some loc => #[locationToSarif loc]
    | none => #[]

  { ruleId, level, message, locations }

/-- Convert VCResults to a SARIF document -/
def vcResultsToSarif (vcResults : VCResults) : SarifDocument :=
  let tool : Tool := {
    driver := {
      name := "Strata",
      version := "0.1.0",
      informationUri := "https://github.com/tautschnig/strata-private"
    }
  }

  let results := vcResults.map vcResultToSarifResult

  let run : Run := { tool, results }

  { version := "2.1.0",
    schema := "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json",
    runs := #[run] }

/-- Convert SARIF document to JSON string -/
def toJsonString (sarif : SarifDocument) : String :=
  Json.compress (ToJson.toJson sarif)

/-- Convert SARIF document to pretty-printed JSON string -/
def toPrettyJsonString (sarif : SarifDocument) : String :=
  Json.pretty (ToJson.toJson sarif)

end Boogie.Sarif
