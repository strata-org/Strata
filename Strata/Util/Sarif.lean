/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Data.Json

/-!
# SARIF Output

This module provides support for outputting results in SARIF
(Static Analysis Results Interchange Format) version 2.1.0.

SARIF specification: https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html
-/

namespace Strata.Sarif

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
  deriving Repr, ToJson, FromJson, DecidableEq

/-- SARIF region representing a source code region with line and column information -/
structure Region where
  startLine : Nat
  startColumn : Nat
  deriving Repr, ToJson, FromJson, DecidableEq

/-- SARIF physical location with region information -/
structure PhysicalLocation where
  artifactLocation : ArtifactLocation
  region : Region
  deriving Repr, ToJson, FromJson, DecidableEq

/-- SARIF location wrapper -/
structure SarifLocation where
  physicalLocation : PhysicalLocation
  deriving Repr, ToJson, FromJson, DecidableEq

/-- SARIF message -/
structure Message where
  text : String
  deriving Repr, ToJson, FromJson, DecidableEq

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
  /-- Stable identifier of the rule that was evaluated to produce the result --/
  ruleId : String
  level : Level
  message : Message
  locations : Array SarifLocation := #[]
  deriving Repr, ToJson, FromJson, DecidableEq

instance : Inhabited Result where
  default := { ruleId := "", level := .none, message := { text := "" } }

/-- SARIF tool driver information -/
structure Driver where
  /-- The exact command-line tool in Strata --/
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

/-! ## Utility Functions -/

/-- Convert a location to SARIF format -/
def locationToSarif (loc : Location) : SarifLocation :=
  let artifactLocation : ArtifactLocation := { uri := loc.uri }
  let region : Region := { startLine := loc.startLine, startColumn := loc.startColumn }
  { physicalLocation := { artifactLocation, region } }

/-- Convert SARIF document to JSON string -/
def toJsonString (sarif : SarifDocument) : String :=
  Json.compress (ToJson.toJson sarif)

/-- Convert SARIF document to pretty-printed JSON string -/
def toPrettyJsonString (sarif : SarifDocument) : String :=
  Json.pretty (ToJson.toJson sarif)

end Strata.Sarif
