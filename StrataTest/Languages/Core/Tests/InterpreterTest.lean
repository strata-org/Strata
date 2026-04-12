/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Interpreter
import Strata.Languages.Core.Verifier

/-! # Tests for the Strata Core Interpreter -/

namespace Core.InterpreterTest

open Lambda Strata
open Std (ToFormat Format format)

/-! ## Helper: parse, type-check, then interpret -/

def parseAndTypeCheck (pgm : Strata.Program) : Except DiagnosticModel Core.Program := do
  let (cst, _errs) := TransM.run Inhabited.default (translateProgram pgm)
  Core.typeCheck { VerifyOptions.default with verbose := .quiet } cst

def runProc (pgm : Strata.Program) (procName : String)
    (args : List Expression.Expr := [])
    (fuel : Nat := 10000) : IO Unit := do
  match parseAndTypeCheck pgm with
  | .error e => IO.println s!"type error: {e.message}"
  | .ok prog =>
    match Core.initConcreteEnv prog fuel with
    | .error e => IO.println s!"init error: {e.message}"
    | .ok E =>
    let result := Core.interpProcedure E procName args
    match result with
    | .success E =>
      let proc := Core.Program.Procedure.find? prog ⟨procName, ()⟩
      match proc with
      | none => IO.println "success (no proc)"
      | some p =>
        let outputs := p.header.outputs.keys.map fun name =>
          let val := (E.exprEnv.state.find? name).map (·.snd)
          s!"{name} = {val.map (fun v => toString (format v))}"
        IO.println (String.intercalate ", " outputs)
    | .assertionFailure label _ _ => IO.println s!"assertion failure: {label}"
    | .error msg => IO.println s!"error: {msg}"
    | .stuck msg => IO.println s!"stuck: {msg}"

/-! ## Test Programs -/

-- Simple assignment
def simplePgm : Strata.Program :=
#strata
program Core;
procedure Test() returns (y : int)
{
  y := 42;
};
#end

/-- info: y = (some 42) -/
#guard_msgs in
#eval! runProc simplePgm "Test"

-- Arithmetic
def arithPgm : Strata.Program :=
#strata
program Core;
procedure Test(x : int) returns (y : int)
{
  y := x + x;
};
#end

/-- info: y = (some 10) -/
#guard_msgs in
#eval! runProc arithPgm "Test" [.intConst () 5]

-- If-then-else
def itePgm : Strata.Program :=
#strata
program Core;
procedure Test(x : int) returns (y : int)
{
  if (x > 0) {
    y := x;
  } else {
    y := 0 - x;
  }
};
#end

/-- info: y = (some 7) -/
#guard_msgs in
#eval! runProc itePgm "Test" [.intConst () 7]

/-- info: y = (some 3) -/
#guard_msgs in
#eval! runProc itePgm "Test" [.intConst () (Int.negSucc 2)]

-- Procedure call
def callPgm : Strata.Program :=
#strata
program Core;
procedure Double(n : int) returns (result : int)
{
  result := n + n;
};
procedure Test(x : int) returns (y : int)
{
  call y := Double(x);
};
#end

/-- info: y = (some 20) -/
#guard_msgs in
#eval! runProc callPgm "Test" [.intConst () 10]

-- Chained procedure calls (DoubleTwice)
def chainedCallPgm : Strata.Program :=
#strata
program Core;
procedure Double(n : int) returns (result : int)
{
  result := n + n;
};
procedure Test(x : int) returns (output : int)
{
  call output := Double(x);
  call output := Double(output);
};
#end

/-- info: output = (some 20) -/
#guard_msgs in
#eval! runProc chainedCallPgm "Test" [.intConst () 5]

-- Loop (sum of 0..n-1)
def loopPgm : Strata.Program :=
#strata
program Core;
procedure Test(n : int) returns (sum : int)
{
  var i : int;
  sum := 0;
  i := 0;
  while (i < n)
  {
    sum := sum + i;
    i := i + 1;
  }
};
#end

/-- info: sum = (some 10) -/
#guard_msgs in
#eval! runProc loopPgm "Test" [.intConst () 5]

-- Assertion success
def assertSuccessPgm : Strata.Program :=
#strata
program Core;
procedure Test() returns (y : int)
{
  y := 42;
  assert [check]: (y == 42);
};
#end

/-- info: y = (some 42) -/
#guard_msgs in
#eval! runProc assertSuccessPgm "Test"

-- Assertion failure
def assertFailPgm : Strata.Program :=
#strata
program Core;
procedure Test() returns (y : int)
{
  y := 42;
  assert [check]: (y == 0);
};
#end

/-- info: assertion failure: check -/
#guard_msgs in
#eval! runProc assertFailPgm "Test"

-- Nested blocks with scoping
def blockPgm : Strata.Program :=
#strata
program Core;
procedure Test() returns (y : int)
{
  y := 0;
  anon0: {
    var x : int;
    x := 10;
    y := x;
  }
};
#end

/-- info: y = (some 10) -/
#guard_msgs in
#eval! runProc blockPgm "Test"

end Core.InterpreterTest
