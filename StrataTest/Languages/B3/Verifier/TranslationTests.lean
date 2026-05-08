/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 to SMT Translation Tests

Tests for B3 AST to SMT-LIB translation.
These tests verify the generated SMT-LIB output without running solvers.
-/

namespace B3.Verifier.TranslationTests

open Strata
open Strata.B3.Verifier

---------------------------------------------------------------------
-- Test Helpers
---------------------------------------------------------------------

def testSMTGeneration (prog : Program) : IO Unit := do
  let ast ← match programToB3AST prog with
    | .ok ast => pure ast
    | .error msg => throw (IO.userError s!"Parse error: {msg}")

  -- Create a buffer solver to capture SMT commands
  let (solver, buffer) ← createBufferSolver

  -- Run verification to get both SMT and errors
  let results ← programToSMTWithoutDiagnosis ast solver

  -- Collect and print conversion errors first (strip location info for stable tests)
  let errors := results.filterMap (fun r =>
    match r with
    | .error msg => some msg
    | .ok _ => none
  )
  for err in errors do
    -- Strip location information (anything between "at {" and "}: ") for stable tests
    let cleanErr := err.splitOn "at {" |>.head!
    let suffix := err.splitOn "}: " |>.tail.headD ""
    let finalErr := if suffix.isEmpty then cleanErr else cleanErr ++ suffix
    IO.println s!"error: {finalErr.trimAscii}"

  -- Get and print SMT commands
  let contents ← buffer.get
  let commands := if h: contents.data.IsValidUTF8
    then String.fromUTF8 contents.data h
    else "Error: Invalid UTF-8 in SMT output"

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
  if x >= 0 x else -x
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
  if n == 0 1 else isOdd(n - 1)
}
function isOdd(n : int) : int {
  if n == 0 0 else isEven(n - 1)
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
info: (declare-fun f (Int) Bool)
(declare-fun g (Int Int) Bool)
(assert (forall ((x Int)) (! (= (f x) (= (+ x 1) 6)) :pattern ((f x)))))
(push 1)
(assert (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= 5 5) (not (= 3 4))) (< 2 3)) (<= 2 2)) (> 4 3)) (>= 4 4)) (= (+ 1 2) 4)) (= (- 5 2) 3)) (= (* 3 4) 12)) (= (div 10 2) 5)) (= (mod 7 3) 1)) (= (- 5) (- 0 5))) (=> true true)) (or false true)) (ite true true false)) (f 5)) (g 1 2)) (forall ((y Int)) (! (or (f y) (not (f y))) :pattern ((f y))))) (forall ((y Int)) (or (> y 0) (<= y 0))))))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function f(x : int) : bool { x + 1 == 6 }
function g(a : int, b : int) : bool
procedure test_all_expressions() {
  check 5 == 5 &&
        !(3 == 4) &&
        2 < 3 &&
        2 <= 2 &&
        4 > 3 &&
        4 >= 4 &&
        1 + 2 == 4 &&
        5 - 2 == 3 &&
        3 * 4 == 12 &&
        10 div 2 == 5 &&
        7 mod 3 == 1 &&
        -5 == 0 - 5 &&
        (true ==> true) &&
        (false || true) &&
        (if true true else false) &&
        f(5) &&
        g(1, 2) &&
        (forall y : int pattern f(y) f(y) || !f(y)) &&
        (forall y : int y > 0 || y <= 0)
}
#end

---------------------------------------------------------------------
-- Invalid Pattern Tests
---------------------------------------------------------------------

-- The test below should return an error and the SMT code.
/--
info: error: Invalid pattern each pattern expression must be a function application
(declare-fun f (Int) Bool)
(push 1)
(assert (not (forall ((y Int)) (! (> y 0) :pattern (y)))))
(check-sat)
(pop 1)
-/
#guard_msgs in
#eval testSMTGeneration $ #strata program B3CST;
function f(x : int) : bool
procedure test_invalid_pattern() {
  check forall y : int pattern y y > 0
}
#end

end B3.Verifier.TranslationTests
