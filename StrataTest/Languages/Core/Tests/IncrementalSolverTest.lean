/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Incremental Solver Backend Tests

End-to-end tests verifying that the `--incremental` solver backend produces
the same results as the batch pipeline.
-/

namespace Strata.IncrementalSolverTest
open Core

def quietIncremental : Core.VerifyOptions where
  verbose := .quiet
  parseOnly := false
  typeCheckOnly := false
  checkOnly := false
  skipSolver := false
  solver := Core.defaultSolver
  solverTimeout := 10
  vcDirectory := .none
  alwaysGenerateSMT := false
  uniqueBoundNames := false
  useArrayTheory := false
  stopOnFirstError := false
  removeIrrelevantAxioms := .Off
  checkMode := .deductive
  checkLevel := .minimal
  outputSarif := false
  profile := false
  overflowChecks := {}
  incremental := true
  parallelWorkers := 1

private def getVerdict (results : Array Core.VCResult) : String := Id.run do
  for r in results do
    if Core.VCResult.isSuccess r then return "pass"
    else if Core.VCResult.isFailure r then return "fail"
    else return "other"
  return "none"

---------------------------------------------------------------------
-- Simple passing assertion (incremental)
---------------------------------------------------------------------

def passingPgm : Program :=
#strata
program Core;
procedure P() {
  var x : int;
  x := 1;
  assert [x_is_one]: (x == 1);
};
#end

/-- info: pass -/
#guard_msgs in
#eval do
  let results ← verify passingPgm (options := quietIncremental)
  IO.println (getVerdict results)

---------------------------------------------------------------------
-- Simple failing assertion (incremental)
---------------------------------------------------------------------

def failingPgm : Program :=
#strata
program Core;
procedure P() {
  var x : int;
  havoc x;
  assert [always_one]: (x == 1);
};
#end

/-- info: fail -/
#guard_msgs in
#eval do
  let results ← verify failingPgm (options := quietIncremental)
  IO.println (getVerdict results)

---------------------------------------------------------------------
-- Batch and incremental produce the same verdict
---------------------------------------------------------------------

/-- info: batch=pass incremental=pass -/
#guard_msgs in
#eval do
  let batchResults ← verify passingPgm (options := .quiet)
  let incrResults ← verify passingPgm (options := quietIncremental)
  IO.println s!"batch={getVerdict batchResults} incremental={getVerdict incrResults}"

end Strata.IncrementalSolverTest
