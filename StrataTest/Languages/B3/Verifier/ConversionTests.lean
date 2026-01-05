/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 to SMT Conversion Tests

Tests for B3 AST to SMT-LIB translation.
These tests verify the generated SMT-LIB output without running solvers.
-/

namespace B3.Verifier.ConversionTests

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
  let commands ← programToSMTCommands ast
  -- Strip common prefix/suffix for stable tests
  let lines := commands.splitOn "\n"
  let filtered := lines.filter (fun line =>
    !line.startsWith "(set-logic" &&
    !line.startsWith "(set-option" &&
    !line.startsWith "(exit"
  )
  IO.println (String.intercalate "\n" filtered)

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

/--
info: (declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(assert (forall ((x Int)) (! (= (f x) (+ x 1)) :pattern ((f x)))))
(push 1)
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= 5 5) (not (= 3 4))) (< 2 3)) (<= 2 2)) (> 4 3)) (>= 4 4)) (+ 1 2)) (- 5 2)) (* 3 4)) (div 10 2)) (mod 7 3)) (- 5)) (=> true true)) (or false true)) (ite true 1 0)) (f 5)) (g 1 2)) (forall ((y Int)) (! (> y 0) :pattern (y))))))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function f(x : int) : int { x + 1 }
function g(a : int, b : int) : int
procedure test_all_expressions() {
  check 5 == 5 &&
        !(3 == 4) &&
        2 < 3 &&
        2 <= 2 &&
        4 > 3 &&
        4 >= 4 &&
        1 + 2 &&
        5 - 2 &&
        3 * 4 &&
        10 div 2 &&
        7 mod 3 &&
        -5 &&
        (true ==> true) &&
        (false || true) &&
        (if true then 1 else 0) &&
        f(5) &&
        g(1, 2) &&
        (forall y : int y > 0)
}
#end

end B3.Verifier.ConversionTests
