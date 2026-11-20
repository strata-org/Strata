/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.SarifOutput
meta import Strata.Languages.Core.Verifier
meta import Lean.Data.Json

meta section

/-!
# SARIF Output Tests

This file contains tests for the SARIF output functionality, including:
- SARIF JSON structure validation
- VCResult to SARIF conversion
- Various verification result types (success, failure, error, unknown)
- Source location mapping
-/

namespace Core.Sarif.Tests
private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"

open Lean (Json)
open Imperative
open Lambda
open Strata.Sarif (Level Message)
open Core.SMT (Result)

/-! ## Test Helpers -/

private def mkOutcome (sat val : Result) : VCOutcome :=
  { satisfiabilityProperty := sat, validityProperty := val }

/-- Create a simple metadata with file and location information -/
def makeMetadata (file : String) (_line _col : Nat) : MetaData Expression :=
  let uri := Strata.Uri.file file
  -- Create a 1D range (byte offsets). For testing, we use simple offsets.
  let range : StrataDDM.SourceRange := { start := ⟨0⟩, stop := ⟨10⟩ }
  Imperative.MetaData.ofProvenance (Strata.Provenance.ofSourceRange uri range)

/-- Create metadata with a specific byte offset for the file range start. -/
def makeMetadataAt (file : String) (startByte : Nat) : MetaData Expression :=
  let uri := Strata.Uri.file file
  let range : StrataDDM.SourceRange := { start := ⟨startByte⟩, stop := ⟨startByte + 10⟩ }
  Imperative.MetaData.ofProvenance (Strata.Provenance.ofSourceRange uri range)

/-- Create a simple FileMap for testing -/
def makeFileMap : Lean.FileMap :=
  -- Create a simple file map with some dummy content
  Lean.FileMap.ofString "test content\nline 2\nline 3"

/-- Create a files map for testing -/
def makeFilesMap (file : String) : Map Strata.Uri Lean.FileMap :=
  let uri := Strata.Uri.file file
  Map.empty.insert uri makeFileMap

/-- Create a simple proof obligation for testing -/
def makeObligation (label : String) (md : MetaData Expression := #[])
    (property : Imperative.PropertyType := .assert) : ProofObligation Expression :=
  { label := label
    property := property
    assumptions := []
    obligation := Lambda.LExpr.boolConst testLoc true
    metadata := md }

/-- Create a VCResult for testing -/
def makeVCResult (label : String) (outcome : VCOutcome)
  (md : MetaData Expression := #[])
  (lexprModel : LExprModel := [])
  (property : Imperative.PropertyType := .assert) : VCResult :=
  { obligation := makeObligation label md property
    outcome := .ok outcome
    verbose := .normal
    lexprModel := lexprModel
    checkLevel := .minimal
    checkMode := .deductive }

/-! ## Level Conversion Tests -/

-- Test that pass (verified) maps to "none" level
#guard outcomeToLevel .deductive .assert (mkOutcome (.sat []) .unsat) = Level.none

-- Test that fail maps to "error" level
#guard outcomeToLevel .deductive .assert (mkOutcome .unsat (.sat [])) = Level.error

-- Test that unknown maps to "error" level in deductive mode
#guard outcomeToLevel .deductive .assert (mkOutcome .unknown .unknown) = Level.error

-- Test that unreachable assert maps to "warning" level
#guard outcomeToLevel .deductive .assert (mkOutcome .unsat .unsat) = Level.warning

/-! ## Message Generation Tests -/

-- Test pass message
#guard outcomeToMessage (mkOutcome (.sat []) .unsat) = "Always true and reachable"

-- Test fail message without counterexample
#guard outcomeToMessage (mkOutcome .unsat (.sat [])) = "Always false and reachable"

-- Test unknown message
#guard outcomeToMessage (mkOutcome .unknown .unknown) = "Unknown (solver timeout or incomplete)"

-- Test unreachable message
#guard outcomeToMessage (mkOutcome .unsat .unsat) = "Unreachable in this context"

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
    { fld := Imperative.MetaData.provenanceField, value := .msg "not a provenance" }
  ]
  let files := makeFilesMap "/test/file.st"
  (extractLocation files md == none)

/-! ## VCResult to SARIF Conversion Tests -/

-- Test converting a successful VCResult
#guard
  let md := makeMetadata "/test/file.st" 10 5
  let files := makeFilesMap "/test/file.st"
  let vcr := makeVCResult "test_obligation" (mkOutcome (.sat []) .unsat) md
  let sarifResult := vcResultToSarifResult .deductive files vcr
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
  let vcr := makeVCResult "failed_obligation" (mkOutcome .unsat (.sat [])) md
  let sarifResult := vcResultToSarifResult .deductive files vcr
  sarifResult.ruleId = "failed_obligation" &&
  sarifResult.level = Level.error &&
  sarifResult.message.text = "Always false and reachable" &&
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
  let vcr := makeVCResult "unknown_obligation" (mkOutcome .unknown .unknown)
  let sarifResult := vcResultToSarifResult .deductive files vcr
  sarifResult.ruleId = "unknown_obligation" &&
  sarifResult.level = Level.error &&
  sarifResult.locations.size = 0

-- Test converting an error VCResult
#guard
  let files := makeFilesMap "/test/file.st"
  let vcr := makeVCResult "error_obligation" (mkOutcome .unknown .unknown)
  let sarifResult := vcResultToSarifResult .deductive files vcr
  sarifResult.ruleId = "error_obligation" &&
  sarifResult.level = Level.error &&
  sarifResult.message.text = "Unknown (solver timeout or incomplete)"

/-! ## SARIF Document Structure Tests -/

#guard
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[]
  let sarif := vcResultsToSarif .deductive files vcResults
  sarif.version = "2.1.0" &&
  sarif.runs.size = 1 &&
  match sarif.runs[0]? with
  | some run => run.results.size = 0 && run.tool.driver.name = "Strata"
  | none => false

/- TODO: Expression too complex for type checker
-- Test creating a SARIF document with multiple VCResults
#guard
  let md1 := makeMetadata "/test/file1.st" 10 5
  let md2 := makeMetadata "/test/file2.st" 20 10
  let files1 := makeFilesMap "/test/file1.st"
  let files2 := makeFilesMap "/test/file2.st"
  let files := files1.union files2
  let vcResults : VCResults := #[
    makeVCResult "obligation1" (mkOutcome (.sat []) .unsat) md1,
    makeVCResult "obligation2" (mkOutcome .unsat (.sat [])) md2,
    makeVCResult "obligation3" (mkOutcome .unknown .unknown)
  ]
  let sarif := vcResultsToSarif .deductive files vcResults
  sarif.version = "2.1.0" &&
  sarif.runs.size = 1 &&
  match sarif.runs[0]? with
  | some run =>
    match run.results.toList with
    | [r0, r1, r2] =>
      r0.level = Level.none && r0.locations.size = 1 &&
      r1.level = Level.error && r1.locations.size = 1 &&
      r2.level = Level.error && r2.locations.size = 0
    | _ => false
  | none => false
-/

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
    makeVCResult "test_assertion" (mkOutcome (.sat []) .unsat) md
  ]
  let sarif := vcResultsToSarif .deductive files vcResults
  let jsonStr := Strata.Sarif.toJsonString sarif
  (jsonStr.splitOn "\"version\":\"2.1.0\"").length > 1 &&
  (jsonStr.splitOn "\"Strata\"").length > 1 &&
  (jsonStr.splitOn "test_assertion").length > 1

-- Test pretty JSON generation
#guard
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[
    makeVCResult "simple_test" (mkOutcome (.sat []) .unsat)
  ]
  let sarif := vcResultsToSarif .deductive files vcResults
  let prettyJson := Strata.Sarif.toPrettyJsonString sarif
  prettyJson.contains '\n'

/-! ## Integration Test with Counter-Examples -/

-- Test SARIF output with counter-example
#guard
  let cex : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 42))]
  let lexprCex : LExprModel :=
    [({ name := "x", metadata := () }, .intConst testLoc 42)]
  let md := makeMetadata "/test/cex.st" 25 3
  let files := makeFilesMap "/test/cex.st"
  let vcr := { makeVCResult "cex_obligation" (mkOutcome .unsat (.sat cex)) md lexprCex with
    checkModels := (some [], some lexprCex) }
  let sarifResult := vcResultToSarifResult .deductive files vcr
  sarifResult.level = Level.error &&
  (sarifResult.message.text.splitOn "counterexample").length > 1 &&
  sarifResult.locations.size = 1 &&
  match sarifResult.locations[0]? with
  | some loc =>
    loc.physicalLocation.artifactLocation.uri = "/test/cex.st" &&
    loc.physicalLocation.region.startLine = 1 &&
    loc.physicalLocation.region.startColumn = 0
  | none => false

-- A result built without per-check models prints the model the validity check's result carries.
/-- info: "Always false and reachable with counterexample: (x, 42)" -/
#guard_msgs in
#eval
  let cex : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 42))]
  let lexprCex : LExprModel := [({ name := "x", metadata := () }, .intConst testLoc 42)]
  let vcr := makeVCResult "cex_unfilled" (mkOutcome .unsat (.sat cex)) (lexprModel := lexprCex)
  (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") vcr).message.text

-- A producer that filtered every variable out records two empty models: the message prints no
-- model, not the unfiltered solver model the outcome carries.
/-- info: "Always false and reachable" -/
#guard_msgs in
#eval
  let cex : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x@1", metadata := () }, .prim (.int 42))]
  let vcr := { makeVCResult "cex_filtered" (mkOutcome .unsat (.sat cex)) with
    checkModels := (some [], some []) }
  (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") vcr).message.text

-- The printed model is the producer's conversion: a nullary constructor prints as the
-- constructor, whatever the solver's term for it.
/-- info: "Always false and reachable with counterexample: (c, Red)" -/
#guard_msgs in
#eval
  let cex : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "c", metadata := () }, .var ⟨"Red", .prim .bool⟩)]
  let lexprCex : LExprModel :=
    [({ name := "c", metadata := () }, .op testLoc ⟨"Red", ()⟩ none)]
  let vcr := { makeVCResult "cex_ctor" (mkOutcome .unsat (.sat cex)) (lexprModel := lexprCex) with
    checkModels := (some [], some lexprCex) }
  (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") vcr).message.text

-- Without per-check models, a `sat`/`sat` result prints each check's own model: the
-- satisfiability check's as the true model and the validity check's as the false one.
/-- info: "True or false depending on inputs (true: (x, 1), false: (x, 2))" -/
#guard_msgs in
#eval
  let m1 : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 1))]
  let m2 : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 2))]
  let lexprCex : LExprModel := [({ name := "x", metadata := () }, .intConst testLoc 1)]
  let vcr := makeVCResult "satsat" (mkOutcome (.sat m1) (.sat m2)) (lexprModel := lexprCex)
  (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") vcr).message.text

-- Without per-check models, an empty satisfiability model prints nothing in the true slot and the
-- validity check's model in the false slot.
/-- info: "True or false depending on inputs (false: (x, 2))" -/
#guard_msgs in
#eval
  let m2 : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 2))]
  let vcr := makeVCResult "emptysat" (mkOutcome (.sat []) (.sat m2))
  (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") vcr).message.text

-- Two results without per-check models for one assertion (one source range), `(unsat, sat a)` and
-- `(sat b, unsat)`, merge (`VCResults.mergeByAssertion`) into a `sat`/`sat` result that prints `b`
-- as the true model and `a` as the false one, in either order.
/-- info: ["True or false depending on inputs (true: (x, 2), false: (x, 1))",
  "True or false depending on inputs (true: (x, 2), false: (x, 1))"] -/
#guard_msgs in
#eval
  let ma : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 1))]
  let mb : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 2))]
  let md := makeMetadata "/test/cex.st" 1 0
  let ra := makeVCResult "merged" (mkOutcome .unsat (.sat ma)) md
  let rb := makeVCResult "merged" (mkOutcome (.sat mb) .unsat) md
  [#[ra, rb], #[rb, ra]].flatMap fun rs =>
    (VCResults.mergeByAssertion rs).toList.map fun r =>
      (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") r).message.text

-- A result with per-check models, `(unsat, sat a)` whose validity model is `y = 3` and lacks
-- `x`, merges with a result without them, `(sat b, unsat)`: the merge keeps the recorded false
-- model with its partial marker and prints `b`, the model the satisfiability check carries, as
-- the true model, in either order.
/-- info: ["True or false depending on inputs (true: (x, 2), false: (y, 3)) (partial; the false model has no value for x)",
  "True or false depending on inputs (true: (x, 2), false: (y, 3)) (partial; the false model has no value for x)"] -/
#guard_msgs in
#eval
  let ma : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "y", metadata := () }, .prim (.int 3))]
  let mb : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 2))]
  let la : LExprModel := [({ name := "y", metadata := () }, .intConst testLoc 3)]
  let md := makeMetadata "/test/cex.st" 1 0
  let ra := { makeVCResult "mixed" (mkOutcome .unsat (.sat ma)) md with
    checkModels := (some [], some la), checkModelMissing := ([], ["x"]) }
  let rb := makeVCResult "mixed" (mkOutcome (.sat mb) .unsat) md
  [#[ra, rb], #[rb, ra]].flatMap fun rs =>
    (VCResults.mergeByAssertion rs).toList.map fun r =>
      (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") r).message.text

-- Without per-check models, an `unknown` satisfiability check with a candidate model and a `sat`
-- validity check print the validity check's model as the counterexample.
/-- info: "Can be false and is reachable, unknown if always false with counterexample: (x, 2)" -/
#guard_msgs in
#eval
  let m1 : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 1))]
  let m2 : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 2))]
  let vcr := makeVCResult "unknownsat" (mkOutcome (.unknown (some m1)) (.sat m2))
  (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") vcr).message.text

-- Recorded per-check models print with the partial marker of `checkModelMissing`.
/-- info: "True or false depending on inputs (true: (x, 1), false: (y, 2)) (partial; the true model has no value for y; the false model has no value for x)" -/
#guard_msgs in
#eval
  let m1 : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "x", metadata := () }, .prim (.int 1))]
  let m2 : List (Core.Expression.Ident × Strata.SMT.Term) :=
    [({ name := "y", metadata := () }, .prim (.int 2))]
  let l1 : LExprModel := [({ name := "x", metadata := () }, .intConst testLoc 1)]
  let l2 : LExprModel := [({ name := "y", metadata := () }, .intConst testLoc 2)]
  let vcr := { makeVCResult "partial" (mkOutcome (.sat m1) (.sat m2)) with
    checkModels := (some l1, some l2), checkModelMissing := (["y"], ["x"]) }
  (vcResultToSarifResult .deductive (makeFilesMap "/test/cex.st") vcr).message.text

/-! ## JSON Output Tests -/

/-- info: "{\"runs\":[{\"results\":[],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[]
  let sarif := vcResultsToSarif .deductive files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"none\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/pass.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"message\":{\"text\":\"Always true and reachable\"},\"properties\":{\"propertyType\":\"assert\"},\"relatedLocations\":[],\"ruleId\":\"test_pass\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let md := makeMetadata "/test/pass.st" 10 5
  let files := makeFilesMap "/test/pass.st"
  let vcResults : VCResults := #[makeVCResult "test_pass" (mkOutcome (.sat []) .unsat) md]
  let sarif := vcResultsToSarif .deductive files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"error\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/fail.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"message\":{\"text\":\"Always false and reachable\"},\"properties\":{\"propertyType\":\"assert\"},\"relatedLocations\":[],\"ruleId\":\"test_fail\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let md := makeMetadata "/test/fail.st" 20 15
  let files := makeFilesMap "/test/fail.st"
  let vcResults : VCResults := #[makeVCResult "test_fail" (mkOutcome .unsat (.sat [])) md]
  let sarif := vcResultsToSarif .deductive files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"error\",\"locations\":[],\"message\":{\"text\":\"Unknown (solver timeout or incomplete)\"},\"properties\":{\"propertyType\":\"assert\"},\"relatedLocations\":[],\"ruleId\":\"test_unknown\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[makeVCResult "test_unknown" (mkOutcome .unknown .unknown)]
  let sarif := vcResultsToSarif .deductive files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"error\",\"locations\":[],\"message\":{\"text\":\"Unknown (solver timeout or incomplete)\"},\"properties\":{\"propertyType\":\"assert\"},\"relatedLocations\":[],\"ruleId\":\"test_error\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let files := makeFilesMap "/test/file.st"
  let vcResults : VCResults := #[makeVCResult "test_error" (mkOutcome .unknown .unknown)]
  let sarif := vcResultsToSarif .deductive files vcResults
  Strata.Sarif.toJsonString sarif

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"none\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/multi.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"message\":{\"text\":\"Always true and reachable\"},\"properties\":{\"propertyType\":\"assert\"},\"relatedLocations\":[],\"ruleId\":\"obligation1\"},{\"level\":\"error\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/multi.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"message\":{\"text\":\"Always false and reachable\"},\"properties\":{\"propertyType\":\"assert\"},\"relatedLocations\":[],\"ruleId\":\"obligation2\"},{\"level\":\"error\",\"locations\":[],\"message\":{\"text\":\"Unknown (solver timeout or incomplete)\"},\"properties\":{\"propertyType\":\"assert\"},\"relatedLocations\":[],\"ruleId\":\"obligation3\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  let md1 := makeMetadata "/test/multi.st" 5 1
  let md2 := makeMetadata "/test/multi.st" 10 1
  let files := makeFilesMap "/test/multi.st"
  let vcResults : VCResults := #[
    makeVCResult "obligation1" (mkOutcome (.sat []) .unsat) md1,
    makeVCResult "obligation2" (mkOutcome .unsat (.sat [])) md2,
    makeVCResult "obligation3" (mkOutcome .unknown .unknown)
  ]
  let sarif := vcResultsToSarif .deductive files vcResults
  Strata.Sarif.toJsonString sarif

/-! ## Related Locations Test -/

/-- info: "{\"runs\":[{\"results\":[{\"level\":\"error\",\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/caller.st\"},\"region\":{\"startColumn\":0,\"startLine\":2}}}],\"message\":{\"text\":\"Always false and reachable\"},\"properties\":{\"propertyType\":\"assert\"},\"relatedLocations\":[{\"id\":1,\"message\":{\"text\":\"original assertion location\"},\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"/test/caller.st\"},\"region\":{\"startColumn\":0,\"startLine\":1}}}],\"ruleId\":\"inlined_assert\"}],\"tool\":{\"driver\":{\"informationUri\":\"https://github.com/strata-org/Strata\",\"name\":\"Strata\",\"version\":\"0.1.0\"}}}],\"schema\":\"https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json\",\"version\":\"2.1.0\"}" -/
#guard_msgs in
#eval
  -- Simulate inlining: original assertion at byte 0 (line 1), call site at byte 13 (line 2)
  let origMd := makeMetadataAt "/test/caller.st" 0
  let callSiteMd := makeMetadataAt "/test/caller.st" 13
  let inlinedMd := origMd.setCallSiteFileRange callSiteMd
  let files := makeFilesMap "/test/caller.st"
  let vcResults : VCResults := #[makeVCResult "inlined_assert" (mkOutcome .unsat (.sat [])) inlinedMd]
  let sarif := vcResultsToSarif .deductive files vcResults
  Strata.Sarif.toJsonString sarif

/-! ## Property classification tests

The SARIF `properties.propertyType` field should reflect the obligation's
`PropertyType`, not the default `"assert"`. -/

private def sarifPropertyType (vcr : VCResult) : String :=
  let files := makeFilesMap "/test/x.st"
  (vcResultToSarifResult .deductive files vcr).properties.propertyType

/-- info: "assert" -/
#guard_msgs in
#eval sarifPropertyType (makeVCResult "t" (mkOutcome (.sat []) .unsat) (property := .assert))

/-- info: "division-by-zero" -/
#guard_msgs in
#eval sarifPropertyType (makeVCResult "t" (mkOutcome (.sat []) .unsat) (property := .divisionByZero))

/-- info: "arithmetic-overflow" -/
#guard_msgs in
#eval sarifPropertyType (makeVCResult "t" (mkOutcome (.sat []) .unsat) (property := .arithmeticOverflow))

/-- info: "out-of-bounds-access" -/
#guard_msgs in
#eval sarifPropertyType (makeVCResult "t" (mkOutcome (.sat []) .unsat) (property := .outOfBoundsAccess))

/-- info: "cover" -/
#guard_msgs in
#eval sarifPropertyType (makeVCResult "t" (mkOutcome (.sat []) .unsat) (property := .cover))

end Core.Sarif.Tests

end
