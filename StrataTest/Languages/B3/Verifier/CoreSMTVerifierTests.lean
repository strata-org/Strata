/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion
import Strata.Languages.B3.ToCore
import Strata.Languages.Core.CoreSMT
import Strata.DL.SMT.Solver

/-!
# B3 → Core → CoreSMT Verification Tests

Tests that verify B3 programs through the B3→Core→CoreSMT pipeline.
These tests use B3 DDM syntax (no rewriting required) but verify through
the CoreSMT verifier instead of the direct B3→SMT path.

The test harness:
1. Parses B3 DDM syntax to B3 AST
2. Transforms functions to axioms (FunctionToAxiom)
3. Converts B3 AST to Core AST (B3.ToCore)
4. Verifies Core AST via CoreSMT verifier
5. Reports results with diagnosis
-/

namespace B3.Verifier.CoreSMTTests

open Strata
open Strata.B3.Verifier
open Strata.B3.ToCore
open Strata.Core.CoreSMT
open Strata.SMT
---------------------------------------------------------------------
-- Test Harness: B3 → Core → CoreSMT Pipeline
---------------------------------------------------------------------

/-- Format a CheckOutcome for display -/
private def formatOutcome (outcome : CheckOutcome) (isCover : Bool) : String :=
  match outcome, isCover with
  | .pass, false => "✓ verified"
  | .pass, true => "✓ reachable"
  | .fail, false => "✗ counterexample found"
  | .fail, true => "✗ refuted"
  | .unknown, false => "✗ unknown"
  | .unknown, true => "✓ reachability unknown"
  | .refuted, _ => "✗ refuted"
  | .error msg, _ => s!"✗ error: {msg}"

/-- Check if a CheckOutcome represents an error -/
private def isErrorOutcome (outcome : CheckOutcome) : Bool :=
  match outcome with
  | .pass => false
  | _ => true

/-- Extract procedure name from B3 AST -/
private def getProcedureName (prog : B3AST.Program SourceRange) : String :=
  match prog with
  | .program _ decls =>
    match decls.val.toList.filterMap (fun d =>
      match d with
      | .procedure _ name _ _ _ => some name.val
      | _ => none) with
    | name :: _ => name
    | [] => "unknown"

/-- Verify a B3 program through the B3→Core→CoreSMT pipeline.
    Parses B3 DDM syntax, converts to Core, and verifies via CoreSMT. -/
def testB3ViaCoreVerification (prog : Program) : IO Unit := do
  -- Step 1: Parse B3 DDM syntax to B3 AST
  let b3AST ← match programToB3AST prog with
    | .ok ast => pure ast
    | .error msg => throw (IO.userError s!"Parse error: {msg}")

  -- Step 2: Transform functions to axioms
  let transformedAST := B3.Transform.functionToAxiom b3AST

  -- Step 3: Convert B3 AST to Core AST
  let coreStmts := convertProgram transformedAST

  -- Step 4: Create CoreSMT solver and state
  let solver ← mkCvc5Solver
  let config : CoreSMTConfig := { diagnosisEnabled := true, accumulateErrors := true }
  let state := CoreSMTState.init solver config

  -- Step 5: Verify via CoreSMT
  let (_, _, results) ← verify state Core.Env.init coreStmts

  -- Step 6: Display results
  let procName := getProcedureName b3AST
  for result in results do
    let marker := formatOutcome result.outcome result.isCover
    IO.println s!"{procName}: {marker}"
---------------------------------------------------------------------
-- Basic Tests
---------------------------------------------------------------------

/--
info: test: ✓ verified
-/
#guard_msgs in
#eval testB3ViaCoreVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) x > 0 ==> f(x) > 0
procedure test() {
  check 5 > 0 ==> f(5) > 0
}
#end

/--
info: test_fail: ✗ counterexample found
-/
#guard_msgs in
#eval testB3ViaCoreVerification $ #strata program B3CST;
function f(x : int) : int
procedure test_fail() {
  check 5 == 5 && f(5) == 10
}
#end

/--
info: test_assert: ✓ verified
-/
#guard_msgs in
#eval testB3ViaCoreVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) == x + 1
procedure test_assert() {
  assert f(5) == 6
  check f(5) == 6
}
#end

/--
info: test_reach: ✓ reachable
-/
#guard_msgs in
#eval testB3ViaCoreVerification $ #strata program B3CST;
procedure test_reach() {
  reach true
}
#end

end B3.Verifier.CoreSMTTests

/--
info: test_complex: ✗ counterexample found
-/
#guard_msgs in
#eval testB3ViaCoreVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) == x + 1
procedure test_complex() {
  check f(5) == 6 && f(10) == 11 && f(5) == 7
}
#end

end B3.Verifier.CoreSMTTests
