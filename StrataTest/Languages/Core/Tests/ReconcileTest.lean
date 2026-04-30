/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for the reconcile phase (Strata/Languages/Core/Reconcile.lean) of the
Split-Solve-Reconcile workflow.

Covers:
- Building a `VCResult` from a `ManifestObligation` plus hand-crafted
  solver results.
- Evaluator-resolved obligations (no `.smt2` / `.result` files).
- Options override: a manifest's `checkMode` can be overridden at
  reconcile time.
- End-to-end I/O: write manifest + `.result` files to a temp directory,
  then `reconcileDirectory` round-trips them into a `VCResults`.
- `mergeByAssertion`: two obligations referring to the same source location
  are merged into a single `VCResult`.
-/

import Strata.Languages.Core.Reconcile

open Core
open Imperative

namespace ReconcileTest

/-! ## Scaffolding -/

def mkSourceLoc (file : String) (start stop : Nat) : ManifestSourceLocation :=
  { file, start, stop }

def mkSolverObligation
    (label : String)
    (loc : Option ManifestSourceLocation := some (mkSourceLoc "A.core.st" 0 10))
    (smtFile : Option String := some "A_0.smt2")
    (property : String := "assert")
    (satCheck : Bool := false) (valCheck : Bool := true)
    : ManifestObligation := {
  label,
  property,
  smtFile,
  satisfiabilityCheck := satCheck,
  validityCheck := valCheck,
  resolvedBySim := none,
  sourceLocation := loc,
  relatedLocations := #[],
  passWhenUnreachable := true,
  hasFullCheck := false,
  variableMap := #[],
  constructorNames := #[],
  phaseValidation := #[]
}

def mkSimObligation
    (label : String)
    (sat : String) (val : String)
    (satCheck : Bool := false) (valCheck : Bool := true)
    : ManifestObligation := {
  label,
  property := "assert",
  smtFile := none,
  satisfiabilityCheck := satCheck,
  validityCheck := valCheck,
  resolvedBySim := some { satisfiability := some sat, validity := some val },
  sourceLocation := some (mkSourceLoc "A.core.st" 0 10),
  relatedLocations := #[],
  passWhenUnreachable := true,
  hasFullCheck := false,
  variableMap := #[],
  constructorNames := #[],
  phaseValidation := #[]
}

/-! ## reconcileOne: pass (validity unsat) -/

/-- info: true -/
#guard_msgs in
#eval do
  let mo := mkSolverObligation "assert_0"
  let opts := VerifyOptions.default
  let r := reconcileOne mo opts .unsat .unsat
  return r.isSuccess

/-! ## reconcileOne: fail (validity sat) -/

/-- info: false -/
#guard_msgs in
#eval do
  let mo := mkSolverObligation "assert_0"
  let opts := VerifyOptions.default
  let r := reconcileOne mo opts .unknown (.sat [])
  return r.isSuccess

/-- info: true -/
#guard_msgs in
#eval do
  let mo := mkSolverObligation "assert_0"
  let opts := VerifyOptions.default
  let r := reconcileOne mo opts .unknown (.sat [])
  return r.isFailure

/-! ## reconcileOne: unknown -/

/-- info: true -/
#guard_msgs in
#eval do
  let mo := mkSolverObligation "assert_0"
  let opts := VerifyOptions.default
  let r := reconcileOne mo opts .unknown .unknown
  return r.isUnknown

/-! ## Evaluator-resolved obligations are handled inline -/

/-- info: true -/
#guard_msgs in
#eval do
  IO.FS.withTempDir fun dir => do
    let mo := mkSimObligation "trivial_true" "unknown" "unsat"
    let manifest : Manifest := {
      version := 1,
      options := { checkMode := "deductive", checkLevel := "minimal", verbose := "quiet" },
      obligations := #[mo]
    }
    writeManifest dir manifest
    -- No .smt2 or .result files needed.
    let results ← reconcile manifest dir {}
    if h : results.size = 1 then
      return (results[0]'(by simp [h])).isSuccess
    else
      return false

/-! ## missingResultFiles detects absent .result files -/

/-- info: 1 -/
#guard_msgs in
#eval do
  IO.FS.withTempDir fun dir => do
    let mo := mkSolverObligation "assert_0" (smtFile := some "assert_0_0.smt2")
    let manifest : Manifest := {
      version := 1,
      options := { checkMode := "deductive", checkLevel := "minimal", verbose := "quiet" },
      obligations := #[mo]
    }
    let missing ← missingResultFiles manifest dir
    return missing.size

/-! ## End-to-end via reconcileDirectory -/

/-- info: true -/
#guard_msgs in
#eval do
  IO.FS.withTempDir fun dir => do
    let mo := mkSolverObligation "assert_0" (smtFile := some "assert_0_0.smt2")
    let manifest : Manifest := {
      version := 1,
      options := { checkMode := "deductive", checkLevel := "minimal", verbose := "quiet" },
      obligations := #[mo]
    }
    writeManifest dir manifest
    -- Write a matching .result file.
    let resultPath := (dir / "assert_0_0.result").toString
    IO.FS.writeFile resultPath "unsat\n"
    match ← reconcileDirectory dir {} with
    | .error _ => return false
    | .ok results =>
      if h : results.size = 1 then
        return (results[0]'(by simp [h])).isSuccess
      else
        return false

/-! ## Option override: change check mode from deductive to bugFinding -/

/-- info: "bugFinding" -/
#guard_msgs in
#eval do
  let manifest : Manifest := {
    version := 1,
    options := { checkMode := "deductive", checkLevel := "minimal", verbose := "quiet" },
    obligations := #[]
  }
  let ov : ReconcileOverride := { checkMode := some .bugFinding }
  let opts := resolveOptions manifest ov
  return VerificationMode.toManifestString opts.checkMode

/-- info: "deductive" -/
#guard_msgs in
#eval do
  let manifest : Manifest := {
    version := 1,
    options := { checkMode := "deductive", checkLevel := "minimal", verbose := "quiet" },
    obligations := #[]
  }
  let opts := resolveOptions manifest {}
  return VerificationMode.toManifestString opts.checkMode

/-! ## mergeByAssertion: two obligations at the same location merge -/

/-- info: 1 -/
#guard_msgs in
#eval do
  IO.FS.withTempDir fun dir => do
    -- Two obligations pointing to the same source location with the same
    -- display label. After reconcile+merge they should collapse to a single
    -- VCResult.
    let sameLoc := mkSourceLoc "A.core.st" 100 120
    let mo1 := mkSolverObligation "assert_same" (loc := some sameLoc)
                                  (smtFile := some "assert_same_0.smt2")
    let mo2 := mkSolverObligation "assert_same" (loc := some sameLoc)
                                  (smtFile := some "assert_same_1.smt2")
    let manifest : Manifest := {
      version := 1,
      options := { checkMode := "deductive", checkLevel := "minimal", verbose := "quiet" },
      obligations := #[mo1, mo2]
    }
    writeManifest dir manifest
    IO.FS.writeFile (dir / "assert_same_0.result").toString "unsat\n"
    IO.FS.writeFile (dir / "assert_same_1.result").toString "unsat\n"
    let results ← reconcile manifest dir {}
    return results.size

/-! ## Phase validation is applied during reconcile -/

-- Reconcile honors `validates: true`: the stub validator demotes `.sat` to
-- `.unknown`, so a "bug-finding" satisfiability check backed by a sat
-- verdict loses its `isSatisfiable` status when a validator is present.
/-- info: false -/
#guard_msgs in
#eval do
  let mo : ManifestObligation := {
    label := "x",
    property := "assert",
    smtFile := some "x_0.smt2",
    satisfiabilityCheck := true,
    validityCheck := false,
    resolvedBySim := none,
    sourceLocation := some (mkSourceLoc "A.core.st" 0 10),
    relatedLocations := #[],
    passWhenUnreachable := true,
    hasFullCheck := false,
    variableMap := #[],
    constructorNames := #[],
    phaseValidation := #[{ phase := "LoopElim", validates := true }]
  }
  let opts := VerifyOptions.default
  let r := reconcileOne mo opts (.sat []) .unknown
  match r.outcome with
  | .ok o => return o.isSatisfiable
  | .error _ => return false

-- Without a validator, the same input stays `.sat`.
/-- info: true -/
#guard_msgs in
#eval do
  let mo : ManifestObligation := {
    label := "x",
    property := "assert",
    smtFile := some "x_0.smt2",
    satisfiabilityCheck := true,
    validityCheck := false,
    resolvedBySim := none,
    sourceLocation := some (mkSourceLoc "A.core.st" 0 10),
    relatedLocations := #[],
    passWhenUnreachable := true,
    hasFullCheck := false,
    variableMap := #[],
    constructorNames := #[],
    phaseValidation := #[{ phase := "LoopElim", validates := false }]
  }
  let opts := VerifyOptions.default
  let r := reconcileOne mo opts (.sat []) .unknown
  match r.outcome with
  | .ok o => return o.isSatisfiable
  | .error _ => return false

end ReconcileTest
