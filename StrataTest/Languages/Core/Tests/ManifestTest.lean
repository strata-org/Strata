/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for the manifest format (Strata/Languages/Core/Manifest.lean) used by
the Split-Solve-Reconcile workflow. Covers round-trip JSON serialization,
individual field conversions, and phase-validation reconstruction.
-/

import Strata.Languages.Core.Manifest

open Lean (Json ToJson FromJson)
open Core

namespace ManifestTest

/-! ## Substring helper (`String.Contains` is not in core) -/

private def strContains (haystack needle : String) : Bool :=
  let hl := haystack.toList
  let nl := needle.toList
  let rec go : List Char → Bool
    | [] => nl.isEmpty
    | c :: rest =>
      if nl.isPrefixOf (c :: rest) then true
      else go rest
  go hl

/-! ## Round-trip: ManifestSourceLocation -/

def sampleSourceLocation : ManifestSourceLocation :=
  { file := "Examples/Foo.core.st", start := 42, stop := 57 }

/-- info: true -/
#guard_msgs in
#eval do
  let j := ToJson.toJson sampleSourceLocation
  match FromJson.fromJson? (α := ManifestSourceLocation) j with
  | .ok v => return v == sampleSourceLocation
  | .error _ => return false

/-! ## FileRange ↔ ManifestSourceLocation -/

/-- info: true -/
#guard_msgs in
#eval do
  let loc := sampleSourceLocation
  let fr := loc.toFileRange
  let loc' := ManifestSourceLocation.ofFileRange fr
  return loc == loc'

/-! ## Round-trip: ManifestVariableEntry -/

def sampleVariable : ManifestVariableEntry :=
  { var := "x", type := "Int", smtId := "$__f.0" }

/-- info: true -/
#guard_msgs in
#eval do
  let j := ToJson.toJson sampleVariable
  match FromJson.fromJson? (α := ManifestVariableEntry) j with
  | .ok v => return v.var == sampleVariable.var
             && v.type == sampleVariable.type
             && v.smtId == sampleVariable.smtId
  | .error _ => return false

/-! ## Round-trip: ManifestPhaseEntry -/

def samplePhase : ManifestPhaseEntry :=
  { phase := "CallElim", validates := true }

/-- info: true -/
#guard_msgs in
#eval do
  let j := ToJson.toJson samplePhase
  match FromJson.fromJson? (α := ManifestPhaseEntry) j with
  | .ok v => return v.phase == samplePhase.phase && v.validates == samplePhase.validates
  | .error _ => return false

/-! ## Round-trip: ManifestOptions -/

def sampleOptions : ManifestOptions :=
  { checkMode := "deductive", checkLevel := "minimal", verbose := "quiet" }

/-- info: true -/
#guard_msgs in
#eval do
  let j := ToJson.toJson sampleOptions
  match FromJson.fromJson? (α := ManifestOptions) j with
  | .ok v => return v.checkMode == sampleOptions.checkMode
             && v.checkLevel == sampleOptions.checkLevel
             && v.verbose == sampleOptions.verbose
  | .error _ => return false

/-! ## Round-trip: full Manifest -/

def sampleResolvedBySim : ManifestResolvedBySim :=
  { satisfiability := some "unsat", validity := some "unsat" }

def sampleObligation : ManifestObligation := {
  label := "assert_precondition_0",
  property := "assert",
  smtFile := some "assert_precondition_0_0.smt2",
  satisfiabilityCheck := false,
  validityCheck := true,
  resolvedBySim := none,
  sourceLocation := some sampleSourceLocation,
  relatedLocations := #[],
  passWhenUnreachable := true,
  hasFullCheck := false,
  variableMap := #[sampleVariable],
  constructorNames := #["Nil", "Cons"],
  phaseValidation := #[samplePhase,
    { phase := "LoopElim", validates := false }]
}

def sampleObligationSim : ManifestObligation := {
  label := "trivial_true_1",
  property := "assert",
  smtFile := none,
  satisfiabilityCheck := true,
  validityCheck := true,
  resolvedBySim := some sampleResolvedBySim,
  sourceLocation := some sampleSourceLocation,
  relatedLocations := #[],
  passWhenUnreachable := true,
  hasFullCheck := false,
  variableMap := #[],
  constructorNames := #[],
  phaseValidation := #[]
}

def sampleManifest : Manifest := {
  version := 1,
  options := sampleOptions,
  obligations := #[sampleObligation, sampleObligationSim]
}

/-- info: 1 -/
#guard_msgs in
#eval do
  let j := ToJson.toJson sampleManifest
  match FromJson.fromJson? (α := Manifest) j with
  | .ok m => return m.version
  | .error _ => return 0

/-- info: 2 -/
#guard_msgs in
#eval do
  let j := ToJson.toJson sampleManifest
  match FromJson.fromJson? (α := Manifest) j with
  | .ok m => return m.obligations.size
  | .error _ => return 0

/-- info: "assert_precondition_0" -/
#guard_msgs in
#eval do
  let j := ToJson.toJson sampleManifest
  match FromJson.fromJson? (α := Manifest) j with
  | .ok m => return m.obligations[0]!.label
  | .error _ => return "<error>"

/-! ## Property type round-trip -/

#guard propertyTypeToManifestString .assert == "assert"
#guard propertyTypeToManifestString .cover == "cover"
#guard propertyTypeToManifestString .divisionByZero == "divisionByZero"
#guard propertyTypeToManifestString .arithmeticOverflow == "arithmeticOverflow"

#guard propertyTypeOfManifestString "assert" == .assert
#guard propertyTypeOfManifestString "cover" == .cover
#guard propertyTypeOfManifestString "divisionByZero" == .divisionByZero
#guard propertyTypeOfManifestString "arithmeticOverflow" == .arithmeticOverflow
#guard propertyTypeOfManifestString "unknown" == .assert

/-! ## VerificationMode round-trip -/

#guard VerificationMode.toManifestString .deductive == "deductive"
#guard VerificationMode.toManifestString .bugFinding == "bugFinding"
#guard VerificationMode.toManifestString .bugFindingAssumingCompleteSpec == "bugFindingAssumingCompleteSpec"

#guard VerificationMode.ofManifestString "deductive" == .deductive
#guard VerificationMode.ofManifestString "bugFinding" == .bugFinding
#guard VerificationMode.ofManifestString "garbage" == .deductive

/-! ## CheckLevel round-trip -/

#guard CheckLevel.toManifestString .minimal == "minimal"
#guard CheckLevel.toManifestString .minimalVerbose == "minimalVerbose"
#guard CheckLevel.toManifestString .full == "full"

#guard CheckLevel.ofManifestString "minimal" == .minimal
#guard CheckLevel.ofManifestString "full" == .full
#guard CheckLevel.ofManifestString "garbage" == .minimal

/-! ## Result verdict round-trip (lossy: models are dropped) -/

#guard smtResultToManifestString .unsat == "unsat"
#guard smtResultToManifestString (.sat []) == "sat"
#guard smtResultToManifestString .unknown == "unknown"

/-! ## parseResultFile: verdict classification -/

/-- info: "unsat" -/
#guard_msgs in
#eval do
  let (s, _) := parseResultFile "unsat\nunsat\n" true true
  return smtResultToManifestString s

/-- info: "sat" -/
#guard_msgs in
#eval do
  let (s, _) := parseResultFile "sat\n(model ...)\nunsat\n" true true
  return smtResultToManifestString s

/-- info: "err" -/
#guard_msgs in
#eval do
  let (_, v) := parseResultFile "unsat\n" true true
  return smtResultToManifestString v

/-! ## parseResultFile: one-sided checks -/

/-- info: ("unsat", "unknown") -/
#guard_msgs in
#eval do
  let (s, v) := parseResultFile "unsat\n" true false
  return (smtResultToManifestString s, smtResultToManifestString v)

/-- info: ("unknown", "sat") -/
#guard_msgs in
#eval do
  let (s, v) := parseResultFile "sat\n(model ...)\n" false true
  return (smtResultToManifestString s, smtResultToManifestString v)

/-! ## Phase validation reconstruction -/

/-- info: 2 -/
#guard_msgs in
#eval do
  let entries : Array ManifestPhaseEntry := #[
    { phase := "CallElim", validates := false },
    { phase := "LoopElim", validates := true }
  ]
  let phases := reconstructPhaseValidation entries
  return phases.length

/-- info: "unknown" -/
#guard_msgs in
#eval do
  let entries : Array ManifestPhaseEntry := #[
    { phase := "LoopElim", validates := true }
  ]
  let phases := reconstructPhaseValidation entries
  let obligation : Imperative.ProofObligation Core.Expression := {
    label := "x",
    property := .assert,
    assumptions := [],
    obligation := default,
    metadata := #[]
  }
  let (adjusted, _) := SMT.Result.adjustForPhases (.sat []) phases obligation
  return smtResultToManifestString adjusted

/-- info: "sat" -/
#guard_msgs in
#eval do
  let entries : Array ManifestPhaseEntry := #[
    { phase := "LoopElim", validates := false }
  ]
  let phases := reconstructPhaseValidation entries
  let obligation : Imperative.ProofObligation Core.Expression := {
    label := "x",
    property := .assert,
    assumptions := [],
    obligation := default,
    metadata := #[]
  }
  let (adjusted, _) := SMT.Result.adjustForPhases (.sat []) phases obligation
  return smtResultToManifestString adjusted

/-! ## Manifest I/O round-trip (uses temp file) -/

/-- info: true -/
#guard_msgs in
#eval do
  IO.FS.withTempDir fun dir => do
    writeManifest dir sampleManifest
    match ← readManifest dir with
    | .ok m => return m.version == sampleManifest.version
               && m.obligations.size == sampleManifest.obligations.size
               && m.obligations[0]!.label == sampleManifest.obligations[0]!.label
    | .error _ => return false

/-- info: true -/
#guard_msgs in
#eval do
  IO.FS.withTempDir fun dir => do
    let bad : Manifest := { sampleManifest with version := 999 }
    writeManifest dir bad
    match ← readManifest dir with
    | .ok _ => return false
    | .error e => return (strContains e "not supported")

/-- info: true -/
#guard_msgs in
#eval do
  IO.FS.withTempDir fun dir => do
    match ← readManifest dir with
    | .ok _ => return false
    | .error e => return (strContains e "not found")

/-! ## End-to-end: verifyWithManifest emits manifest.json -/

/-- Run `strata verify --no-solve` programmatically on a trivial program and
    verify that `manifest.json` is written with at least one obligation. -/
def trivialProgram : Strata.Program :=
#strata
program Core;
procedure Test(x : bool, out y : bool)
spec {
  ensures (y == x);
}
{
  y := x;
};
#end

/-- info: true -/
#guard_msgs in
#eval do
  IO.FS.withTempDir fun dir => do
    let opts : VerifyOptions := { VerifyOptions.default with
      skipSolver := true,
      vcDirectory := some dir,
      verbose := .quiet }
    let _ ← Strata.verifyWithManifest trivialProgram (options := opts)
    match ← readManifest dir with
    | .ok m => return m.version == 1 && m.obligations.size > 0
    | .error _ => return false

end ManifestTest
