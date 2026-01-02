/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 to SMT Conversion Tests

Tests for converting B3 programs to SMT commands.
-/

namespace B3.Verifier.Tests

open Strata
open Strata.B3.Verifier

/-- Helper to extract B3 program from DDM parse result -/
def programToB3CST (prog : Program) : B3CST.Program SourceRange :=
  match prog.commands.toList with
  | [op] =>
      if op.name.name == "command_program" then
        match op.args.toList with
        | [ArgF.op progOp] =>
            match B3CST.Program.ofAst progOp with
            | .ok cstProg => cstProg
            | .error _ => default
        | _ => default
      else default
  | _ => default

/-- Helper to convert B3CST to B3AST -/
def b3CSTToAST (cst : B3CST.Program SourceRange) : B3AST.Program Unit × List (B3.CSTToASTError SourceRange) :=
  let (prog, errors) := B3.programFromCST B3.FromCSTContext.empty cst
  (B3AST.Program.mapMetadata (fun _ => ()) prog, errors)

/-- Test B3 to SMT command generation -/
def testB3ToSMT (prog : Program) : IO Unit := do
  let cst := programToB3CST prog
  let (ast, _errors) := b3CSTToAST cst
  let smtCommands := programToSMTCommands ast
  for cmd in smtCommands do
    IO.println cmd

---------------------------------------------------------------------
-- Tests
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
#eval testB3ToSMT $ #strata program B3CST;
function abs(x : int) : int {
  if x >= 0 then x else -x
}
check abs(-5) == 5
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
#eval testB3ToSMT $ #strata program B3CST;
function isEven(n : int) : int {
  if n == 0 then 1 else isOdd(n - 1)
}
function isOdd(n : int) : int {
  if n == 0 then 0 else isEven(n - 1)
}
check isEven(4) == 1
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
#eval testB3ToSMT $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) x > 0 ==> f(x) > 0
check 5 > 0 ==> f(5) > 0
#end

end B3.Verifier.Tests
