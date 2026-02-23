/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.SarifOutput
import Strata.Languages.Core.Verifier
import Lean.Data.Json

/-!
# SARIF Output Tests

This file contains tests for the SARIF output functionality, including:
- SARIF JSON structure validation
- VCResult to SARIF conversion
- Various verification result types (success, failure, error, unknown)
- Source location mapping
-/

namespace Core.Sarif.Tests

open Lean (Json)
open Imperative
open Strata.Sarif (Level Message)
open Core.SMT (Result)

/-! ## Test Helpers -/

/-- Create a simple metadata with file and location information -/
def makeMetadata (file : String) (_line _col : Nat) : MetaData Expression :=
  let uri := Strata.Uri.file file
  -- Create a 1D range (byte offsets). For testing, we use simple offsets.
  let range : Strata.SourceRange := { start := ⟨0⟩, stop := ⟨10⟩ }
  let fr : Strata.FileRange := { file := uri, range := range }
  #[{ fld := Imperative.MetaData.fileRange, value := .fileRange fr }]

/-- Create a simple FileMap for testing -/
def makeFileMap : Lean.FileMap :=
  -- Create a simple file map with some dummy content
  Lean.FileMap.ofString "test content\nline 2\nline 3"

/-- Create a files map for testing -/
def makeFilesMap (file : String) : Map Strata.Uri Lean.FileMap :=
  let uri := Strata.Uri.file file
  Map.empty.insert uri makeFileMap

/-- Create a simple proof obligation for testing -/
def makeObligation (label : String) (md : MetaData Expression := #[]) : ProofObligation Expression :=
  { label := label
    property := .assert
    assumptions := []
    obligation := Lambda.LExpr.boolConst () true
    metadata := md }

/-- Create a VCResult for testing -/
def makeVCResult (label : String) (outcome : Outcome)
  (smtResult : Result := .unknown) (md : MetaData Expression := #[]) : VCResult :=
  { obligation := makeObligation label md
    smtResult := smtResult
    result := outcome
    verbose := .normal }

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
#guard
  let md := makeMetadata "/test/file.st" 10 5
  let files := makeFilesMap "/test/file.st"
  let loc? := extractLocation files md
  match loc? with
  | some loc => loc.uri = "/test/file.st"
  | none => false

-- Test location extraction from empty metadata
#guard
  let files := makeFilesMap "/test/file.st"
  (extractLocation files #[] == none)

-- Test location extraction from metadata with wrong value type
#guard
  let md : MetaData Expression := #[
    { fld := Imperative.MetaData.fileRange, value := .msg "not a fileRange" }
  ]
  let files := makeFilesMap "/test/file.st"
  (extractLocation files md == none)

/-! ## VCResult to SARIF Conversion Tests -/

-- Test converting a successful VCResult
#guard
  let md := makeMetadata "/test/file.st" 10 5
  let files := makeFilesMap "/test/file.st"
  let vcr := makeVCResult "test_obligation" .pass .unsat md
  let sarifResult := vcResultToSarifResult files vcr
  sarifResult.ruleId = "test_obligation" &&
  sarifResult.level = Level.none &&
  sarifResult.locations.size = 1 &&
  match sarifResult.locations[0]? with
  | some loc =>
    loc.physicalLocation.artifactLocation.uri = "/test/file.st" &&
    loc.physicalLocation.region.startLine = 1 &&
    loc.physicalLocation.region.startColumn = 0
  | none => false

-- Test converting a failed VCResult
#guard
  let md := makeMetadata "/test/file.st" 20 10
  let files := makeFilesMap "/test/file.st"
  let vcr := makeVCResult "failed_obligation" .fail (.sat []) md
  let sarifResult := vcResultToSarifResult files vcr
  sarifResult.ruleId = "failed_obligation" &&
  sarifResult.level = Level.error &&
  sarifResult.message.text = "Verification failed" &&
  sarifResult.locations.size = 1 &&
  match sarifResult.locations[0]? with
  | some loc =>
    loc.physicalLocation.artifactLocation.uri = "/test/file.st" &&
    loc.physicalLocation.region.startLine = 1 &&
    loc.physicalLocation.region.startColumn = 0
  | none => false

-- Test converting an unknown VCResult
#guard
  let files := makeFilesMap "/test/file.st"
  let vcr := makeVCResult "unknown_obligation" .unknown
  let sarifResult := vcResultToSarifResult files vcr
  sarifResult.ruleId = "unknown_obligation" &&
  sarifResult.level = Level.warning &&
  sarifResult.locations.size = 0

-- Test converting an error VCResult
#guard
  let files := makeFilesMap "/test/file.st"
  let vcr := makeVCResult "error_obligation" (.implementationError "SMT solver error")
  let sarifResult := vcResultToSarifResult files vcr
  sarifResult.ruleId = "error_obligation" &&
  sarifResult.level = Level.error &&
  sarifResult.message.text.startsWith "Verification error:"

/-! ## SARIF Document Structure Tests -/

#guard
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[]
  let sarif := vcResultsToSarif files vcResults
  sarif.version = "2.1.0" &&
  sarif.runs.size = 1 &&
  match sarif.runs[0]? with
  | some run => run.results.size = 0 && run.tool.driver.name = "Strata"
  | none => false

-- Test creating a SARIF document with multiple VCResults
#guard
  let md1 := makeMetadata "/test/file1.st" 10 5
  let md2 := makeMetadata "/test/file2.st" 20 10
  let files1 := makeFilesMap "/test/file1.st"
  let files2 := makeFilesMap "/test/file2.st"
  let files := files1.union files2
  let vcResults : VCResults := #[
    makeVCResult "obligation1" .pass .unsat md1,
    makeVCResult "obligation2" .fail (.sat []) md2,
    makeVCResult "obligation3" .unknown
  ]
  let sarif := vcResultsToSarif files vcResults
  sarif.version = "2.1.0" &&
  sarif.runs.size = 1 &&
  match sarif.runs[0]? with
  | some run =>
    match run.results.toList with
    | [r0, r1, r2] =>
      r0.level = Level.none && r0.locations.size = 1 &&
      r1.level = Level.error && r1.locations.size = 1 &&
      r2.level = Level.warning && r2.locations.size = 0
    | _ => false
  | none => false

/-! ## JSON Serialization Tests -/

#guard (Lean.ToJson.toJson Level.none == Json.str "none")

#guard
  let msg : Message := { text := "Test message" }
  let json := Lean.ToJson.toJson msg
  match json with
  | Json.obj _ => true
  | _ => false

-- Test full SARIF document JSON generation
#guard
  let md := makeMetadata "/test/example.st" 15 7
  let files := makeFilesMap "/test/example.st"
  let vcResults : VCResults := #[
    makeVCResult "test_assertion" .pass .unsat md
  ]
  let sarif := vcResultsToSarif files vcResults
  let jsonStr := Strata.Sarif.toJsonString sarif
  (jsonStr.splitOn "\"version\":\"2.1.0\"").length > 1 &&
  (jsonStr.splitOn "\"Strata\"").length > 1 &&
  (jsonStr.splitOn "test_assertion").length > 1

-- Test pretty JSON generation
#guard
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[
    makeVCResult "simple_test" .pass
  ]
  let sarif := vcResultsToSarif files vcResults
  let prettyJson := Strata.Sarif.toPrettyJsonString sarif
  prettyJson.contains '\n'

/-! ## Integration Test with Counter-Examples -/

-- Test SARIF output with counter-example
#guard
  let cex : List (Core.Expression.Ident × String) :=
    [({ name := "x", metadata := Visibility.unres }, "42")]
  let md := makeMetadata "/test/cex.st" 25 3
  let files := makeFilesMap "/test/cex.st"
  let vcr := makeVCResult "cex_obligation" .fail (.sat cex) md
  let sarifResult := vcResultToSarifResult files vcr
  sarifResult.level = Level.error &&
  (sarifResult.message.text.splitOn "counterexample").length > 1 &&
  sarifResult.locations.size = 1 &&
  match sarifResult.locations[0]? with
  | some loc =>
    loc.physicalLocation.artifactLocation.uri = "/test/cex.st" &&
    loc.physicalLocation.region.startLine = 1 &&
    loc.physicalLocation.region.startColumn = 0
  | none => false

/-! ## JSON Output Tests -/

/-- info: "{\"runs\":[{\"results\":[],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[]
  let sarif := vcResultsToSarif files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"none\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/pass.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"message\":{\"text\":\"Verification succeeded\"},\"ruleId\":\"test_pass\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let md := makeMetadata "/test/pass.st" 10 5
  let files := makeFilesMap "/test/pass.st"
  let vcResults : VCResults := #[makeVCResult "test_pass" .pass .unsat md]
  let sarif := vcResultsToSarif files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"error\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/fail.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"message\":{\"text\":\"Verification failed\"},\"ruleId\":\"test_fail\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let md := makeMetadata "/test/fail.st" 20 15
  let files := makeFilesMap "/test/fail.st"
  let vcResults : VCResults := #[makeVCResult "test_fail" .fail (.sat []) md]
  let sarif := vcResultsToSarif files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"warning\",\"locations\":[],\"message\":{\"text\":\"Verification result unknown (solver timeout or incomplete)\"},\"ruleId\":\"test_unknown\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[makeVCResult "test_unknown" .unknown]
  let sarif := vcResultsToSarif files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"error\",\"locations\":[],\"message\":{\"text\":\"Verification error: timeout\"},\"ruleId\":\"test_error\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[makeVCResult "test_error" (.implementationError "timeout")]
  let sarif := vcResultsToSarif files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"none\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/multi.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"message\":{\"text\":\"Verification succeeded\"},\"ruleId\":\"obligation1\"},{\"level\":\"error\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/multi.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"message\":{\"text\":\"Verification failed\"},\"ruleId\":\"obligation2\"},{\"level\":\"warning\",\"locations\":[],\"message\":{\"text\":\"Verification result unknown (solver timeout or incomplete)\"},\"ruleId\":\"obligation3\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let md1 := makeMetadata "/test/multi.st" 5 1
  let md2 := makeMetadata "/test/multi.st" 10 1
  let files := makeFilesMap "/test/multi.st"
  let vcResults : VCResults := #[
    makeVCResult "obligation1" .pass .unsat md1,
    makeVCResult "obligation2" .fail (.sat []) md2,
    makeVCResult "obligation3" .unknown
  ]
  let sarif := vcResultsToSarif files vcResults
  Strata.Sarif.toJsonString sarif

end Core.Sarif.Tests
