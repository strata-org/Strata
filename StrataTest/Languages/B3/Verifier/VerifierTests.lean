/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Verifier Tests

Tests for B3 to SMT conversion and verification.
-/

namespace B3.Verifier.Tests

open Strata
open Strata.B3.Verifier

---------------------------------------------------------------------
-- Test Helpers
---------------------------------------------------------------------

def programToB3AST (prog : Program) : B3AST.Program SourceRange :=
  match prog.commands.toList with
  | [op] =>
      if op.name.name == "command_program" then
        match op.args.toList with
        | [ArgF.op progOp] =>
            match B3CST.Program.ofAst progOp with
            | .ok cstProg =>
                let (ast, _) := B3.programFromCST B3.FromCSTContext.empty cstProg
                ast
            | .error _ => default
        | _ => default
      else default
  | _ => default

def testSMTGeneration (prog : Program) : IO Unit := do
  let ast := programToB3AST prog
  let commands := programToSMTCommands ast
  for cmd in commands do
    IO.println cmd

def formatSourceLocation (baseOffset : String.Pos.Raw) (sr : SourceRange) : String :=
  let relativePos := sr.start.byteIdx - baseOffset.byteIdx
  s!"(0,{relativePos})"

def formatStatementError (prog : Program) (stmt : B3AST.Statement SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  let loc := match stmt with
    | .check m _ => formatSourceLocation baseOffset m
    | .assert m _ => formatSourceLocation baseOffset m
    | .assume m _ => formatSourceLocation baseOffset m
    | .reach m _ => formatSourceLocation baseOffset m
    | _ => "unknown location"

  let (cstStmt, _errors) := B3.stmtToCST B3.ToCSTContext.empty stmt
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let state : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  let stmtAst := cstStmt.toAst
  let formatted := (mformat (ArgF.op stmtAst) ctx state).format.pretty.trim

  s!"{loc}: {formatted}"

def formatExpressionError (prog : Program) (expr : B3AST.Expression SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  let loc := match expr with
    | .binaryOp m _ _ _ => formatSourceLocation baseOffset m
    | .literal m _ => formatSourceLocation baseOffset m
    | .id m _ => formatSourceLocation baseOffset m
    | .ite m _ _ _ => formatSourceLocation baseOffset m
    | .unaryOp m _ _ => formatSourceLocation baseOffset m
    | .functionCall m _ _ => formatSourceLocation baseOffset m
    | .labeledExpr m _ _ => formatSourceLocation baseOffset m
    | .letExpr m _ _ _ => formatSourceLocation baseOffset m
    | .quantifierExpr m _ _ _ _ _ => formatSourceLocation baseOffset m

  let (cstExpr, _) := B3.expressionToCST B3.ToCSTContext.empty expr
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let fmtState : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  let formatted := (mformat (ArgF.op cstExpr.toAst) ctx fmtState).format.pretty.trim

  s!"{loc}: {formatted}"

def testAutoDiagnosis (prog : Program) : IO Unit := do
  let ast := programToB3AST prog
  let reports ← verifyWithDiagnosis ast

  for report in reports do
    IO.println s!"Procedure {report.procedureName}:"
    for (result, diagnosis) in report.results do
      -- Check if this is a reach statement
      let isReach := match result.sourceStmt with
        | some (.reach _ _) => true
        | _ => false

      let isFailed := if isReach then
        !result.result.isError  -- For reach, unsat is failure
      else
        result.result.isError  -- For check, sat is failure

      if !isFailed then
        IO.println "  ✓ Verified"
      else
        IO.println "  ✗ Could not prove"
        match result.sourceStmt with
        | some stmt =>
            IO.println s!"    {formatStatementError prog stmt}"
        | none => pure ()
        match diagnosis with
        | some diag =>
            if !diag.diagnosedFailures.isEmpty then
              for (_desc, failedExpr, _) in diag.diagnosedFailures do
                IO.println s!"    Related: {formatExpressionError prog failedExpr}"
        | none => pure ()

def testVerification (prog : Program) : IO Unit := do
  let ast := programToB3AST prog
  let results ← verifyProgram ast
  IO.println "Verification results:"
  for result in results do
    match result.decl with
    | .procedure _ name _ _ _ =>
        -- Check if this is a reach statement
        let isReach := match result.sourceStmt with
          | some (.reach _ _) => true
          | _ => false

        let status := if isReach then
          match result.decision with
          | .unsat => "✗ unreachable"
          | .sat => "✓ satisfiable"
          | .unknown => "? unknown"
        else
          match result.decision with
          | .unsat => "✓ verified"
          | .sat => "✗ proved wrong"
          | .unknown => "? unknown"

        IO.println s!"  {name.val}: {status}"
        -- Show details for failures
        if (result.result.isError && !isReach) || (!result.result.isError && isReach) then
          match result.sourceStmt with
          | some stmt =>
              IO.println s!"    {formatStatementError prog stmt}"
          | none => pure ()
    | _ => pure ()

---------------------------------------------------------------------
-- SMT Generation Tests
---------------------------------------------------------------------

/--
info: (declare-fun abs (Int) Int)
(assert (forall ((x Int)) (! (= (abs x) (ite (>= x 0) x (- x))) :pattern ((abs x)))))
(push 1)
(assert (not (= (abs (- 5)) 5)))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function abs(x : int) : int {
  if x >= 0 then x else -x
}
procedure test() {
  check abs(-5) == 5
}
#end

/--
info: (declare-fun isEven (Int) Int)
(declare-fun isOdd (Int) Int)
(assert (forall ((n Int)) (! (= (isEven n) (ite (= n 0) 1 (isOdd (- n 1)))) :pattern ((isEven n)))))
(assert (forall ((n Int)) (! (= (isOdd n) (ite (= n 0) 0 (isEven (- n 1)))) :pattern ((isOdd n)))))
(push 1)
(assert (not (= (isEven 4) 1)))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function isEven(n : int) : int {
  if n == 0 then 1 else isOdd(n - 1)
}
function isOdd(n : int) : int {
  if n == 0 then 0 else isEven(n - 1)
}
procedure test() {
  check isEven(4) == 1
}
#end

/--
info: (declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (=> (> x 0) (> (f x) 0)) :pattern ((f x)))))
(push 1)
(assert (not (=> (> 5 0) (> (f 5) 0))))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) x > 0 ==> f(x) > 0
procedure test() {
  check 5 > 0 ==> f(5) > 0
}
#end

---------------------------------------------------------------------
-- Solver Integration Tests
---------------------------------------------------------------------

/--
info: Verification results:
  test: ✓ verified
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) x > 0 ==> f(x) > 0
procedure test() {
  check 5 > 0 ==> f(5) > 0
}
#end

/--
info: Verification results:
  test_fail: ✗ proved wrong
    (0,52): check 5 == 5 && f(5) == 10
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
procedure test_fail() {
  check 5 == 5 && f(5) == 10
}
#end

---------------------------------------------------------------------
-- Automatic Diagnosis Tests
---------------------------------------------------------------------

/--
info: Procedure test:
  ✗ Could not prove
    (0,47): check 5 == 5 && f(5) == 10
    Related: (0,63): f(5) == 10
-/
#guard_msgs in
#eval testAutoDiagnosis $ #strata program B3CST;
function f(x : int) : int
procedure test() {
  check 5 == 5 && f(5) == 10
}
#end

/--
info: Verification results:
  test_reach_bad: ✗ unreachable
    (0,100): reach f(5) < 0
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_bad() {
  reach f(5) < 0
}
#end

/--
info: Verification results:
  test_reach_good: ✓ satisfiable
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_good() {
  reach f(5) > 5
}
#end

/--
info: Procedure test_reach_diagnosis:
  ✗ Could not prove
    (0,106): reach f(5) > 5 && f(5) < 0
    Related: (0,124): f(5) < 0
-/
#guard_msgs in
#eval testAutoDiagnosis $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_diagnosis() {
  reach f(5) > 5 && f(5) < 0
}
#end

end B3.Verifier.Tests


/--
info: Verification results:
  test_assert_helps: ✓ verified
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
procedure test_assert_helps() {
  assert f(5) > 0
  check f(5) > -1
}
#end
