/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.SarifOutput
import Strata.Languages.Boogie.Verifier
import Lean.Data.Json

/-!
# SARIF Output Tests

This file contains tests for the SARIF output functionality, including:
- SARIF JSON structure validation
- VCResult to SARIF conversion
- Various verification result types (success, failure, error, unknown)
- Source location mapping
-/

namespace Boogie.Sarif.Tests

open Lean (Json)
open Imperative
open Strata.Sarif (Level Message)
open Boogie.SMT (SMTModel Result)

/-! ## Test Helpers -/

/-- Create a simple metadata with file and location information -/
def makeMetadata (file : String) (line col : Nat) : MetaData Expression :=
  let uri := Imperative.Uri.file file
  let pos : Lean.Position := { line := line, column := col }
  let fr : Imperative.FileRange := { file := uri, start := pos, ending := pos }
  #[{ fld := Imperative.MetaData.fileRange, value := .fileRange fr }]

/-- Create a simple proof obligation for testing -/
def makeObligation (label : String) (md : MetaData Expression := #[]) : ProofObligation Expression :=
  { label := label
    property := .assert
    assumptions := []
    obligation := Lambda.LExpr.boolConst () true
    metadata := md }

/-- Create a VCResult for testing -/
def makeVCResult (label : String) (outcome : Outcome) (smtResult : Result := .unknown) (md : MetaData Expression := #[]) : VCResult :=
  { obligation := makeObligation label md
    smtResult := smtResult
    result := outcome
    verbose := true }

/-! ## Level Conversion Tests -/

-- Test that pass (verified) maps to "none" level
#guard outcomeToLevel .pass = Level.none

-- Test that fail maps to "error" level
#guard outcomeToLevel .fail = Level.error

-- Test that unknown maps to "warning" level
#guard outcomeToLevel .unknown = Level.warning

-- Test that implementationError maps to "error" level
#guard outcomeToLevel (.implementationError "test error") = Level.error

/-! ## Message Generation Tests -/

-- Test pass message
#guard outcomeToMessage .pass .unknown = "Verification succeeded"

-- Test fail message without counterexample
#guard outcomeToMessage .fail .unknown = "Verification failed"

-- Test unknown message
#guard (outcomeToMessage .unknown .unknown).startsWith "Verification result unknown"

-- Test error message
#guard (outcomeToMessage (.implementationError "test error") .unknown).startsWith "Verification error:"

/-! ## Location Extraction Tests -/

-- Test location extraction from complete metadata
#guard_msgs in
#eval
  let md := makeMetadata "/test/file.st" 10 5
  let loc? := extractLocation md
  match loc? with
  | some loc =>
    if loc.uri = "/test/file.st" && loc.startLine = 10 && loc.startColumn = 5 then
      pure ()
    else
      IO.println s!"Location extraction test failed: uri={loc.uri} line={loc.startLine} col={loc.startColumn}"
  | none => IO.println "Location extraction test failed: no location"

-- Test location extraction from empty metadata
#guard (extractLocation #[] == none)

-- Test location extraction from metadata with wrong value type
#guard
  let md : MetaData Expression := #[
    { fld := Imperative.MetaData.fileRange, value := .msg "not a fileRange" }
  ]
  (extractLocation md == none)

/-! ## VCResult to SARIF Conversion Tests -/

-- Test converting a successful VCResult
#guard_msgs in
#eval
  let md := makeMetadata "/test/file.st" 10 5
  let vcr := makeVCResult "test_obligation" .pass .unsat md
  let sarifResult := vcResultToSarifResult vcr
  if sarifResult.ruleId = "test_obligation" &&
     sarifResult.level = Level.none &&
     sarifResult.locations.size = 1 then
    pure ()
  else
    IO.println s!"Successful VCResult conversion test failed: {repr sarifResult}"

-- Test converting a failed VCResult
#guard
  let md := makeMetadata "/test/file.st" 20 10
  let vcr := makeVCResult "failed_obligation" .fail (.sat []) md
  let sarifResult := vcResultToSarifResult vcr
  let expected := { 
    ruleId := "failed_obligation"
    level := Level.error
    message := { text = "Verification failed" }
  }
  sarifResult = expected

-- Test converting an unknown VCResult
#guard_msgs in
#eval
  let vcr := makeVCResult "unknown_obligation" .unknown
  let sarifResult := vcResultToSarifResult vcr
  if sarifResult.ruleId = "unknown_obligation" &&
     sarifResult.level = Level.warning &&
     sarifResult.locations.size = 0 then
    pure ()
  else
    IO.println s!"Unknown VCResult conversion test failed: {repr sarifResult}"

-- Test converting an error VCResult
#guard_msgs in
#eval
  let vcr := makeVCResult "error_obligation" (.implementationError "SMT solver error")
  let sarifResult := vcResultToSarifResult vcr
  if sarifResult.ruleId = "error_obligation" &&
     sarifResult.level = Level.error &&
     (sarifResult.message.text.startsWith "Verification error:") then
    pure ()
  else
    IO.println s!"Error VCResult conversion test failed: {repr sarifResult}"

/-! ## SARIF Document Structure Tests -/

#guard_msgs in
#eval
  let vcResults : VCResults := #[]
  let sarif := vcResultsToSarif vcResults
  if sarif.version = "2.1.0" &&
     sarif.runs.size = 1 &&
     sarif.runs[0]!.results.size = 0 &&
     sarif.runs[0]!.tool.driver.name = "Strata" then
    pure ()
  else
    IO.println s!"Empty SARIF document test failed"

-- Test creating a SARIF document with multiple VCResults
#guard_msgs in
#eval
  let md1 := makeMetadata "/test/file1.st" 10 5
  let md2 := makeMetadata "/test/file2.st" 20 10
  let vcResults : VCResults := #[
    makeVCResult "obligation1" .pass .unsat md1,
    makeVCResult "obligation2" .fail (.sat []) md2,
    makeVCResult "obligation3" .unknown
  ]
  let sarif := vcResultsToSarif vcResults
  if sarif.version = "2.1.0" &&
     sarif.runs.size = 1 &&
     sarif.runs[0]!.results.size = 3 &&
     sarif.runs[0]!.results[0]!.level = Level.none &&
     sarif.runs[0]!.results[1]!.level = Level.error &&
     sarif.runs[0]!.results[2]!.level = Level.warning then
    pure ()
  else
    IO.println s!"Multiple VCResults SARIF document test failed"

/-! ## JSON Serialization Tests -/

#guard_msgs in
#eval
  let json := Lean.ToJson.toJson Level.none
  match json with
  | Json.str "none" => pure ()
  | _ => IO.println s!"Level serialization test failed: {json}"

#guard_msgs in
#eval
  let msg : Message := { text := "Test message" }
  let _ := Lean.ToJson.toJson msg
  -- Just check that it serializes without error
  pure ()

-- Test full SARIF document JSON generation
#guard_msgs in
#eval
  let md := makeMetadata "/test/example.st" 15 7
  let vcResults : VCResults := #[
    makeVCResult "test_assertion" .pass .unsat md
  ]
  let sarif := vcResultsToSarif vcResults
  let jsonStr := Strata.Sarif.toJsonString sarif

  -- Check that the JSON contains expected fields
  if (jsonStr.splitOn "\"version\":\"2.1.0\"").length > 1 &&
     (jsonStr.splitOn "\"Strata\"").length > 1 &&
     (jsonStr.splitOn "test_assertion").length > 1 then
    pure ()
  else
    IO.println s!"SARIF document JSON generation test failed"

-- Test pretty JSON generation
#guard_msgs in
#eval
  let vcResults : VCResults := #[
    makeVCResult "simple_test" .pass
  ]
  let sarif := vcResultsToSarif vcResults
  let prettyJson := Strata.Sarif.toPrettyJsonString sarif

  -- Pretty JSON should contain newlines for formatting
  if prettyJson.contains '\n' then
    pure ()
  else
    IO.println s!"Pretty JSON generation test failed"

/-! ## Integration Test with Counter-Examples -/

-- Test SARIF output with counter-example
#guard_msgs in
#eval
  let cex : SMTModel := [((BoogieIdent.unres "x", some .int), "42")]
  let md := makeMetadata "/test/cex.st" 25 3
  let vcr := makeVCResult "cex_obligation" .fail (.sat cex) md
  let sarifResult := vcResultToSarifResult vcr

  if sarifResult.level = Level.error &&
     (sarifResult.message.text.splitOn "counterexample").length > 1 &&
     sarifResult.locations.size = 1 then
    pure ()
  else
    IO.println s!"Counter-example SARIF test failed: {repr sarifResult}"

/-! ## Schema URI Test -/

#guard_msgs in
#eval
  let sarif := vcResultsToSarif #[]
  if sarif.schema = "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json" then
    pure ()
  else
    IO.println s!"Schema URI test failed: {sarif.schema}"

end Boogie.Sarif.Tests
