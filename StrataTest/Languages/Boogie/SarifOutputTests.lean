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
    assumptions := []
    obligation := Lambda.LExpr.boolConst () true
    metadata := md }

/-- Create a VCResult for testing -/
def makeVCResult (label : String) (result : Boogie.Result) (md : MetaData Expression := #[]) : VCResult :=
  { obligation := makeObligation label md
    result := result
    verbose := true }

/-! ## Level Conversion Tests -/

-- Test that unsat (verified) maps to "none" level
#guard resultToLevel .unsat = Level.none

-- Test that sat (failed) maps to "error" level
#guard resultToLevel (.sat []) = Level.error

-- Test that unknown maps to "warning" level
#guard resultToLevel .unknown = Level.warning

-- Test that error maps to "error" level
#guard resultToLevel (.err "test error") = Level.error

/-! ## Message Generation Tests -/

-- Test unsat message
#guard resultToMessage .unsat = "Verification succeeded"

-- Test sat message without counterexample
#guard resultToMessage (.sat []) = "Verification failed"

-- Test unknown message
#guard (resultToMessage .unknown).startsWith "Verification result unknown"

-- Test error message
#guard (resultToMessage (.err "test error")).startsWith "Verification error:"

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
  let vcr := makeVCResult "test_obligation" .unsat md
  let sarifResult := vcResultToSarifResult vcr
  if sarifResult.ruleId = "test_obligation" &&
     sarifResult.level = Level.none &&
     sarifResult.locations.size = 1 then
    pure ()
  else
    IO.println s!"Successful VCResult conversion test failed: {repr sarifResult}"

-- Test converting a failed VCResult
#guard_msgs in
#eval
  let md := makeMetadata "/test/file.st" 20 10
  let vcr := makeVCResult "failed_obligation" (.sat []) md
  let sarifResult := vcResultToSarifResult vcr
  if sarifResult.ruleId = "failed_obligation" &&
     sarifResult.level = Level.error &&
     sarifResult.message.text = "Verification failed" then
    pure ()
  else
    IO.println s!"Failed VCResult conversion test failed: {repr sarifResult}"

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
  let vcr := makeVCResult "error_obligation" (.err "SMT solver error")
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
    makeVCResult "obligation1" .unsat md1,
    makeVCResult "obligation2" (.sat []) md2,
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
    makeVCResult "test_assertion" .unsat md
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
    makeVCResult "simple_test" .unsat
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
  let cex : CounterEx := [((BoogieIdent.unres "x", some .int), "42")]
  let md := makeMetadata "/test/cex.st" 25 3
  let vcr := makeVCResult "cex_obligation" (.sat cex) md
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
