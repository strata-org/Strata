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
  s!"offset +{relativePos}"

def formatStatementError (prog : Program) (stmt : B3AST.Statement SourceRange) : String :=
  let baseOffset := match prog.commands.toList with
    | [op] => op.ann.start
    | _ => { byteIdx := 0 }
  let loc := match stmt with
    | .check m _ => formatSourceLocation baseOffset m
    | .assert m _ => formatSourceLocation baseOffset m
    | .assume m _ => formatSourceLocation baseOffset m
    | _ => "unknown location"

  -- Convert statement back to concrete syntax
  let (cstStmt, _errors) := B3.stmtToCST B3.ToCSTContext.empty stmt
  let ctx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let state : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a d => a.insert d.name }
  let stmtAst := cstStmt.toAst
  let formatted := (mformat (ArgF.op stmtAst) ctx state).format.pretty.trim

  s!"{loc}\n    {formatted}"

def testVerification (prog : Program) : IO Unit := do
  let ast := programToB3AST prog
  let results ← verifyProgram ast
  IO.println "Verification results:"
  for result in results do
    match result.decl with
    | .procedure _ name _ _ _ =>
        let status := match result.decision with
          | .unsat => "✓ verified"
          | .sat => "✗ counterexample"
          | .unknown => "? unknown"
        IO.println s!"  {name.val}: {status}"
        if result.decision != .unsat then
          match result.sourceStmt with
          | some stmt =>
              IO.println s!"    Failed at: {formatStatementError prog stmt}"
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
  test_fail: ✗ counterexample
    Failed at: offset +52
    check f(5) == 10
-/
#guard_msgs in
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
procedure test_fail() {
  check f(5) == 10
}
#end

end B3.Verifier.Tests
