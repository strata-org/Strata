/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Verifier Integration Tests

Tests for B3 verification with SMT solvers (Z3/CVC5).
These tests run the actual solver and test check, assert, reach statements with automatic diagnosis.
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

def formatExpressionLocation (prog : Program) (expr : B3AST.Expression SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  match expr with
    | .binaryOp m _ _ _ => formatSourceLocation baseOffset m
    | .literal m _ => formatSourceLocation baseOffset m
    | .id m _ => formatSourceLocation baseOffset m
    | .ite m _ _ _ => formatSourceLocation baseOffset m
    | .unaryOp m _ _ => formatSourceLocation baseOffset m
    | .functionCall m _ _ => formatSourceLocation baseOffset m
    | .labeledExpr m _ _ => formatSourceLocation baseOffset m
    | .letExpr m _ _ _ => formatSourceLocation baseOffset m
    | .quantifierExpr m _ _ _ _ _ => formatSourceLocation baseOffset m

def formatExpressionOnly (prog : Program) (expr : B3AST.Expression SourceRange) : String :=
  let (cstExpr, _) := B3.expressionToCST B3.ToCSTContext.empty expr
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let fmtState : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  (mformat (ArgF.op cstExpr.toAst) ctx fmtState).format.pretty.trim

def testVerification (prog : Program) : IO Unit := do
  let ast := programToB3AST prog
  let reports ← verifyWithDiagnosis ast
  for report in reports do
    for (result, diagnosis) in report.results do
      match result.decl with
      | .procedure _ name _ _ _ =>
          let marker := if result.result.isError then "✗" else "✓"
          let description := match result.result with
            | .proofResult .proved => "verified"
            | .proofResult .counterexample => "counterexample found"
            | .proofResult .proofUnknown => "proof unknown"
            | .reachabilityResult .unreachable => "unreachable"
            | .reachabilityResult .reachable => "satisfiable"
            | .reachabilityResult .reachabilityUnknown => "reachability unknown"

          IO.println s!"{name.val}: {marker} {description}"
          if result.result.isError then
            match result.sourceStmt with
            | some stmt =>
                IO.println s!"  {formatStatementError prog stmt}"
            | none => pure ()
            match diagnosis with
            | some diag =>
                if !diag.diagnosedFailures.isEmpty then
                  -- Determine prefix based on result type
                  let prefixStr := match result.result with
                    | .proofResult _ => "could not prove"
                    | .reachabilityResult _ => "unreachable"
                  for (_desc, failedExpr, _) in diag.diagnosedFailures do
                    let exprLoc := formatExpressionLocation prog failedExpr
                    let exprFormatted := formatExpressionOnly prog failedExpr
                    IO.println s!"  └─ {exprLoc}: {prefixStr} {exprFormatted}"
            | none => pure ()
      | _ => pure ()

---------------------------------------------------------------------
-- Check Statement Tests
---------------------------------------------------------------------

/--
info: test: ✓ verified
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
info: test_fail: ✗ counterexample found
  (0,52): check 5 == 5 && f(5) == 10
  └─ (0,68): could not prove f(5) == 10
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
procedure test_fail() {
  check 5 == 5 && f(5) == 10
}
#end

---------------------------------------------------------------------
-- Assert Statement Tests
---------------------------------------------------------------------

/--
info: test_assert_helps: ✓ verified
test_assert_helps: ✓ verified
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_assert_helps() {
  assert f(5) > 0
  check f(5) > -1
}
#end

---------------------------------------------------------------------
-- Reach Statement Tests
---------------------------------------------------------------------

/--
info: test_reach_bad: ✗ unreachable
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
info: test_reach_good: ✓ satisfiable
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_good() {
  reach f(5) > 5
}
#end

---------------------------------------------------------------------
-- Automatic Diagnosis Tests
---------------------------------------------------------------------

/--
info: test_reach_diagnosis: ✗ unreachable
  (0,106): reach f(5) > 5 && f(5) < 0
  └─ (0,124): unreachable f(5) < 0
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test_reach_diagnosis() {
  reach f(5) > 5 && f(5) < 0
}
#end

end B3.Verifier.Tests
