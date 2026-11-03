/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation
import StrataLaurel.Implementation.LaurelCompilationPipeline
import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.Interpreter
import StrataCortex.Implementation.Pipeline

open Strata

namespace Strata.Laurel

private def stackOf (name : Identifier) (source : FileRange) : Option Variable :=
  match name.text with
  | "stk" => some (.Stack none)
  | "stki" => some (.Stack (some ⟨.TInt, source⟩))
  | "stks" => some (.Stack (some ⟨.UserDefined (mkId "small"), source⟩))
  | "stkb" => some (.Stack (some ⟨.TBool, source⟩))
  | _ => none

private def toStack (program : LaurelProgram) : LaurelProgram :=
  let node (e : StmtExprMd) : StmtExprMd :=
    match e.val with
    | .Var (.Local name) => match stackOf name e.source with
      | some v => ⟨.Var v, e.source⟩
      | none => e
    | .StaticCall callee args typeArgs =>
      if callee.text == "preconditionOf" then match args with
        | [call] => ⟨.ContractOf .Precondition call, e.source⟩
        | _ => e
      else if callee.text.startsWith "permute_" || callee.text == "cmp3" then
        ⟨.StaticCall (mkId s!"${callee.text}") args typeArgs, e.source⟩
      else e
    | .Assign targets value =>
      ⟨.Assign (targets.map fun t => match t.val with
        | .Local name => match stackOf name t.source with
          | some v => ⟨v, t.source⟩
          | none => t
        | _ => t) value, e.source⟩
    | _ => e
  mapLaurelProgramProcedures (fun proc => mapProcedureM (m := Id) (mapStmtExpr node) proc) program

private def parse (source : String) : IO LaurelProgram :=
  return toStack (← (Strata.parseLaurelText "<eliminate-stack-test>" source : IO LaurelProgram))

private def showEliminated (source : String) (wrapOld : StmtExprMd → Bool := fun _ => true) : IO Unit := do
  let (program, diags) := eliminateStack (← parse source) wrapOld
  for proc in program.staticProcedures do
    IO.println (Std.format proc)
  for d in diags do
    IO.println s!"{d.kind}: {d.message}"

private def verify (source : String) : IO Unit := do
  let messages ← verifyToMessagesCapturing (← parse source) StrataTest.Util.defaultLaurelTestOptions
  if messages.isEmpty then IO.println "verified"
  for d in messages do
    IO.println s!"{d.kind}: {d.message}"

private def ordered := r"
procedure ordered()
  opaque
{
  stk := 1;
  stk := 2;
  var d: int := stk - stk;
  assert d == -1
};
"

/--
info: procedure ordered()
  opaque
{
  var d: int := 1 - 2;
  assert d == -1
};
-/
#guard_msgs in
#eval showEliminated ordered

/-- info: verified -/
#guard_msgs in
#eval verify ordered

private def merged := r"
procedure f(x: int) returns (r: int)
  opaque
  ensures r == x + 1
;

procedure merged(b: bool)
  opaque
{
  stk := f(1);
  if (b) then { stki := f(2) } else { stki := 5 };
  var r: int := stk + stk;
  assert r == 5 || r == 7;
  assert r == 7
};
"

/--
info: procedure f(x: int)
  returns (r: int)
  opaque
  ensures r == x + 1;
procedure merged(b: bool)
  opaque
{
  var $stack_0 := f(1);
  var $stack_3: int := if b
    then f(2)
    else 5;
  var r: int := $stack_0 + $stack_3;
  assert r == 5 || r == 7;
  assert r == 7
};
-/
#guard_msgs in
#eval showEliminated merged

/-- info: userError: assertion does not hold -/
#guard_msgs in
#eval verify merged

private def contract := r"
procedure f(x: int) returns (r: int)
{
  return x + 1
};

procedure guarded(x: int)
  requires { stk := f(x); stk > 1 }
  opaque
{
  assert x > 0
};
"

/-- info: verified -/
#guard_msgs in
#eval verify contract

private def malformed := r"
procedure underflow()
  opaque
{
  var r: int := stk
};

procedure leftover()
  opaque
{
  stk := 1
};

procedure untypedMerge(b: bool)
  opaque
{
  if (b) then { stk := 1 } else { stk := 2 };
  var r: int := stk
};
"

/--
info: userError: this reads more stack values than were pushed
userError: stack values are left over at the end of an expression
userError: a value pushed in both branches needs a type on its push
-/
#guard_msgs in
#eval do
  let (_, diags) := eliminateStack (← parse malformed)
  for d in diags do
    IO.println s!"{d.kind}: {d.message}"

private def refused := r"
procedure acrossLabelledBlock()
  opaque
{
  { stk := 1 } out
};

procedure acrossJump()
  opaque
{
  { stk := 1; exit out } out
};

procedure inLoopCondition()
  opaque
{
  while (stk > 0) { }
};

procedure acrossLoopBody()
  opaque
{
  while (true) { stk := 1 }
};

procedure acrossTry()
  opaque
{
  try { stk := 1 } catch e { } finally { }
};

procedure acrossCatch()
  opaque
{
  try { } catch e { stk := 1 }
};

procedure acrossFinally()
  opaque
{
  try { } finally { stk := 1 }
};

procedure pushInExpression()
  opaque
{
  var r: int := { stk := 1; 2 }
};

procedure branchConsumesOuter(b: bool)
  opaque
{
  stk := 1;
  if (b) then { var r: int := stk } else { }
};

procedure branchesDiffer(b: bool)
  opaque
{
  if (b) then { stki := 1 };
  var r: int := stk
};
"

/--
info: userError: a value pushed in both branches needs a type on its push
userError: stack values are left over at the end of an expression
userError: a value pushed in both branches needs a type on its push
userError: stack values are left over at the end of an expression
userError: a loop condition cannot use the stack
userError: stack values are left over at the end of a loop body
userError: stack values are left over at the end of a try block
userError: stack values are left over at the end of a catch handler
userError: stack values are left over at the end of a finally block
userError: a stack push must be a statement
userError: the branches consume different numbers of the stack values pushed before them
userError: stack values are left over at the end of an expression
userError: the branches leave different numbers of values on the stack
userError: this reads more stack values than were pushed
-/
#guard_msgs in
#eval do
  let (_, diags) := eliminateStack (← parse refused)
  for d in diags do
    IO.println s!"{d.kind}: {d.message}"

private def interpret (source : String) : IO Unit := do
  let (_, failures, outcome) ← Strata.Laurel.Interpreter.evalProgramWithOutcome {}
    { entryProcedure := "main", dumpState := false, printAsserts := false } (← parse source)
  let outcome := match outcome with
    | .refused r => s!"refused: {r}"
    | .completed => "completed"
    | .escaped v => s!"escaped {v.display}"
    | .outOfFuel => "out of fuel"
  IO.println s!"failures: {failures.map (·.message)}"
  IO.println outcome

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret r"
procedure main()
  opaque
{
  stk := 1;
  stk := 2;
  var d: int := stk - stk;
  assert d == -1
};
"

/--
info: failures: #[assertion does not hold]
completed
-/
#guard_msgs in
#eval interpret r"
procedure main()
  opaque
{
  var b: bool := true;
  stk := 1;
  if (b) then { stk := 2 } else { stk := 5 };
  var r: int := stk + stk;
  assert r == 3;
  assert r == 6
};
"

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret r"
procedure g() returns (r: int)
  opaque
{
  stk := 10;
  r := stk
};

procedure main()
  opaque
{
  stk := 1;
  var x: int := g();
  var y: int := stk;
  assert x == 10;
  assert y == 1
};
"

/-- error: this reads more stack values than were pushed -/
#guard_msgs in
#eval interpret r"
procedure main()
  opaque
{
  var r: int := stk
};
"

private def untypedMerge := r"
procedure untypedMerge(b: bool)
  opaque
{
  stk := 1;
  if (b) then { stk := 2 } else { stk := 5 };
  var r: int := stk + stk;
  assert r == 3 || r == 6
};
"

/-- info: verified -/
#guard_msgs in
#eval verify untypedMerge

private def thrown := r"
composite Exception {}
composite ParseError extends Exception {}
procedure throwsPushed() throws (e: Exception) opaque {
  stk := new ParseError;
  throw stk
};
"

/-- info: verified -/
#guard_msgs in
#eval verify thrown

private def caught := r"
composite Exception {}
composite ParseError extends Exception {}
procedure caughtPushed()
  opaque
{
  var r: int := 0;
  try {
    stk := new ParseError;
    throw stk
  } catch e {
    r := 1
  };
  assert r == 1
};
"

/-- info: verified -/
#guard_msgs in
#eval verify caught

private def dupped := r"
procedure f(x: int) returns (r: int)
  opaque
  ensures r == x + 1
;

procedure dupped()
  opaque
{
  stk := f(1);
  assign stk, stk := permute_0_0(stk);
  var a: int := stk;
  var b: int := stk;
  assert a == b;
  assert a == 2
};
"

/--
info: procedure f(x: int)
  returns (r: int)
  opaque
  ensures r == x + 1;
procedure dupped()
  opaque
{
  var $stack_0 := f(1);
  var a: int := $stack_0;
  var b: int := $stack_0;
  assert a == b;
  assert a == 2
};
-/
#guard_msgs in
#eval showEliminated dupped

/-- info: verified -/
#guard_msgs in
#eval verify dupped

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret r"
procedure main()
  opaque
{
  stk := 5;
  assign stk, stk := permute_0_0(stk);
  var r: int := stk + stk;
  assert r == 10
};
"

private def consumedInArms := r"
procedure consumedInArms(b: bool) returns (r: int)
  opaque
  ensures r == 1 || r == 2
{
  stk := 1;
  { r := stk };
  stk := 2;
  if (b) then { r := stk } else { var t: int := stk; r := t - 1 }
};

procedure abruptArm(b: bool) returns (r: int)
  opaque
  ensures r == 0 || r == 2
{
  if (b) then { r := 0; return } else { stk := 2 };
  r := stk
};
"

/-- info: verified -/
#guard_msgs in
#eval verify consumedInArms

private def abruptBlock := r"
procedure g(p0: int) returns (r: int)
  opaque
  ensures r == p0
;
procedure sign(i: int) returns (r: int)
  opaque
  ensures r == 1 || r == 0
{
  stk := g(i);
  {
    var sel: int := stk;
    if sel == 1 then { r := 1; return }
    else { stk := 0; r := stk; return }
  }
};
"

/-- info: verified -/
#guard_msgs in
#eval verify abruptBlock

private def receiver := r"
composite Box {
  var v: int
  procedure get(self: Box) returns (r: int)
    opaque
    ensures r == self#v
  ;
}
procedure readsBox(b: Box)
  opaque
{
  stk := b;
  stk := stk#get();
  var r: int := stk;
  assert r == b#v
};
"

/-- info: verified -/
#guard_msgs in
#eval verify receiver

private def siblingArms := r"
composite Animal { }
composite Cat extends Animal { }
composite Dog extends Animal { }
procedure pick(c: bool): Animal
  opaque
{
  if c then { stk := new Cat } else { stk := new Dog };
  return stk
};
"

/-- info: verified -/
#guard_msgs in
#eval verify siblingArms

private def witnessed := r"
constrained small = x: int where x >= 0 witness 0
procedure g() returns (r: small)
  opaque
;
procedure f(c: bool, a: small, b: small)
  opaque
{
  if c then { stks := g() } else { assert a == a; stks := b };
  var r: small := stks
};
"

/--
info: procedure g()
  returns (r: small)
  opaque;
procedure f(c: bool, a: small, b: small)
  opaque
{
  var $stack_2: small := 0;
  if c
    then {
      $stack_2 := g()
    }
    else {
      assert a == a;
      $stack_2 := b
    };
  var r: small := $stack_2
};
-/
#guard_msgs in
#eval showEliminated witnessed

private def oldOfPush := r"
composite Box { var v: int }
procedure bump(b: Box)
  opaque
  ensures { stk := b#v; b#v == old(stk) + 1 }
  modifies b
{
  b#v := b#v + 1
};
"

/--
info: procedure bump(b: Box)
  opaque
  ensures b#v == old(b#v) + 1
  modifies b
{
  b#v := b#v + 1
};
-/
#guard_msgs in
#eval showEliminated oldOfPush

/-- info: verified -/
#guard_msgs in
#eval verify oldOfPush

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret r"
composite Box { var v: int }
procedure bump(b: Box)
  opaque
  ensures { stk := b#v; b#v == old(stk) + 1 }
  modifies b
{
  b#v := b#v + 1
};
procedure main()
  opaque
{
  var b: Box := new Box;
  b#v := 1;
  bump(b)
};
"

/-- info: verified -/
#guard_msgs in
#eval verify r"
procedure abruptElseLess(c: bool)
  opaque
{
  stk := 1;
  if c then { stk := true; return };
  var r: int := stk;
  assert r == 1
};
"

private def permuted := r"
procedure permuted()
  opaque
{
  stk := 1;
  stk := 2;
  assign stk, stk, stk := permute_1_0_1(stk, stk);
  var a: int := stk;
  var b: int := stk;
  var c: int := stk;
  assert a == 2 && b == 1 && c == 2
};
"

/--
info: procedure permuted()
  opaque
{
  var $stack_1 := 2;
  var a: int := $stack_1;
  var b: int := 1;
  var c: int := $stack_1;
  assert a == 2 && b == 1 && c == 2
};
-/
#guard_msgs in
#eval showEliminated permuted

/-- info: verified -/
#guard_msgs in
#eval verify permuted

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret r"
procedure main()
  opaque
{
  stk := 1;
  stk := 2;
  assign stk, stk := permute_1_0(stk, stk);
  var a: int := stk - stk;
  assert a == 1
};
"

private def notInlined := r"
composite Box { var v: int }
procedure bump(b: Box)
  opaque
  modifies b
;
procedure notInlined(b: Box)
  opaque
  modifies b
{
  var x: int := 1;
  stk := x;
  x := 2;
  var y: int := stk;
  stk := b#v;
  bump(b);
  var z: int := stk
};
"

/--
info: procedure bump(b: Box)
  opaque
  modifies b;
procedure notInlined(b: Box)
  opaque
  modifies b
{
  var x: int := 1;
  var $stack_0 := x;
  x := 2;
  var y: int := $stack_0;
  var $stack_1 := b#v;
  bump(b);
  var z: int := $stack_1
};
-/
#guard_msgs in
#eval showEliminated notInlined

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret r"
composite Box { var v: int }
procedure main()
  opaque
{
  var b: Box := new Box;
  stk := b;
  stk := 3;
  stk#v := stk;
  assert b#v == 3
};
"

/-- info: verified -/
#guard_msgs in
#eval verify r"
composite Node { var v: int var next: Node }
procedure redirect(h: Node, o: Node) returns (r: int)
  opaque
  ensures h#next == o && r == 7
  modifies h
;
procedure storeIntoOldReceiver(h: Node, a: Node, b: Node)
  requires h != a && h != b && a != b && h#next == a
  opaque
  modifies h
  modifies a
  modifies b
{
  stk := h#next;
  stki := redirect(h, b);
  stk#v := stki;
  assert a#v == 7
};
"

private def compared := r"
procedure less(a: int, b: int) returns (r: bool)
  opaque
  ensures r == (a < b)
{
  stk := a;
  stk := b;
  stk := cmp3(stk, stk);
  if (stk < 0) then { r := true } else { r := false }
};
procedure main()
  opaque
{
  stk := 3;
  stk := 5;
  stk := cmp3(stk, stk);
  var c: int := stk;
  assert c == -1;
  stk := 5;
  stk := 5;
  stk := cmp3(stk, stk);
  assert stk == 0
};
"

/-- info: verified -/
#guard_msgs in
#eval verify compared

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret compared

private def preconditionOfCalls := r"
procedure f(x: int) returns (r: int)
  requires x > 0
  requires x < 100
  opaque
{
  r := x
};
procedure caller(y: int)
  requires preconditionOf(f(y))
  opaque
{
  var z: int := f(y)
};
procedure pushed(y: int)
  opaque
{
  stk := y;
  var b: bool := preconditionOf(f(stk));
  assert b ==> y > 0
};
procedure main()
  opaque
{
  assert preconditionOf(f(5));
  assert !preconditionOf(f(0))
};
"

/-- info: verified -/
#guard_msgs in
#eval verify preconditionOfCalls

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret preconditionOfCalls

/-- info: userError: assertion does not hold -/
#guard_msgs in
#eval verify r"
procedure f(x: int) returns (r: int)
  requires x > 0
  opaque
{
  r := x
};
procedure wrong(y: int)
  opaque
{
  assert preconditionOf(f(y))
};
"

/-- info: userError: call to 'f' expects 1 argument(s) but 2 were provided -/
#guard_msgs in
#eval verify r"
procedure f(x: int) returns (r: int)
  requires x > 0
  opaque
{
  r := x
};
procedure wrongArity(y: int)
  opaque
{
  assert preconditionOf(f(y, y))
};
"

private def preconditionOfTwiceInOneExpression := r"
procedure f(x: int) returns (r: int)
  requires { var t: int := x + 1; t > 0 }
  opaque
{
  r := x
};
procedure main()
  opaque
{
  assert preconditionOf(f(1)) && preconditionOf(f(2))
};
"

/-- info: verified -/
#guard_msgs in
#eval verify preconditionOfTwiceInOneExpression

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret preconditionOfTwiceInOneExpression

private def preconditionOfInSeparateAsserts := r"
procedure f(x: int) returns (r: int)
  requires { var t: int := x + 1; t > 0 }
  opaque
{
  r := x
};
procedure main()
  opaque
{
  assert preconditionOf(f(1));
  assert preconditionOf(f(2))
};
"

/-- info: verified -/
#guard_msgs in
#eval verify preconditionOfInSeparateAsserts

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret preconditionOfInSeparateAsserts

private def preconditionOfBesideCallerLocal := r"
procedure f(x: int) returns (r: int)
  requires { var t: int := x + 1; t > 0 }
  opaque
{
  r := x
};
procedure main()
  opaque
{
  var t: int := 3;
  assert preconditionOf(f(2));
  assert t == 3
};
"

/-- info: verified -/
#guard_msgs in
#eval verify preconditionOfBesideCallerLocal

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret preconditionOfBesideCallerLocal

private def preconditionOfTwoClausesDeclareSameName := r"
procedure f(x: int) returns (r: int)
  requires { var t: int := x + 1; t > 0 }
  requires { var t: int := x - 1; t < 100 }
  opaque
{
  r := x
};
procedure main()
  opaque
{
  assert preconditionOf(f(1))
};
"

/-- info: verified -/
#guard_msgs in
#eval verify preconditionOfTwoClausesDeclareSameName

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret preconditionOfTwoClausesDeclareSameName

private def preconditionOfNestedInRequires := r"
procedure g(x: int) returns (r: int)
  requires x > 0
  opaque
{
  r := x
};
procedure f(x: int) returns (r: int)
  requires preconditionOf(g(x))
  opaque
{
  r := x
};
procedure main()
  opaque
{
  assert preconditionOf(f(1))
};
"

/-- info: verified -/
#guard_msgs in
#eval verify preconditionOfNestedInRequires

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret preconditionOfNestedInRequires

private def preconditionOfNestedInRequiresFails := r"
procedure g(x: int) returns (r: int)
  requires x > 0
  opaque
{
  r := x
};
procedure f(x: int) returns (r: int)
  requires preconditionOf(g(x))
  opaque
{
  r := x
};
procedure main()
  opaque
{
  assert preconditionOf(f(0))
};
"

/-- info: userError: assertion does not hold -/
#guard_msgs in
#eval verify preconditionOfNestedInRequiresFails

private def preconditionOfRecursive := r"
procedure f(x: int) returns (r: int)
  requires preconditionOf(f(x))
  opaque
{
  r := x
};
procedure main()
  opaque
{
  assert preconditionOf(f(1))
};
"

/--
info: userError: preconditionOf of 'f' refers back to itself
userError: preconditionOf of 'f' refers back to itself
-/
#guard_msgs in
#eval verify preconditionOfRecursive

private def exitsCarryValues := r"
procedure pick(x: int, y: int) returns (r: int)
  opaque
  ensures r == (if x > y then x else y)
{
  {
    {
      stki := x;
      stki := y;
      if (stk <= stk) then { exit b2 };
      stki := x;
      exit b3
    }b2;
    stki := y
  }b3;
  r := stk
};
procedure main()
  opaque
{
  var a: int := pick(3, 5);
  assert a == 5;
  var b: int := pick(5, 3);
  assert b == 5
};
"

/-- info: verified -/
#guard_msgs in
#eval verify exitsCarryValues

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret exitsCarryValues

/--
info: procedure pick(x: int, y: int)
  returns (r: int)
  opaque
  ensures r == (if x > y
  then x
  else y)
{
  r := if x <= y
    then y
    else x
};
procedure main()
  opaque
{
  var a: int := pick(3, 5);
  assert a == 5;
  var b: int := pick(5, 3);
  assert b == 5
};
-/
#guard_msgs in
#eval showEliminated exitsCarryValues

private def quantifiedStack := r"
procedure q(n: int)
  opaque
{
  assert forall(i: int) => {
    {
      {
        stki := i;
        if (stk < 0) then { exit e };
        stkb := true;
        exit j
      }e;
      stkb := i < 0
    }j;
    stk
  }
};
"

/-- info: verified -/
#guard_msgs in
#eval verify quantifiedStack

private def backEdgeAfterIfElse := r"
procedure meet(len: int) returns (r: int)
  requires len >= 0
  opaque
{
  var go: bool := true;
  var fast: int := 0;
  {
    {
      stkb := go;
      if (!stk) then { exit skip };
      {
        {
          stkb := fast >= len;
          if (!stk) then { exit other };
          go := false;
          exit join
        }other;
        fast := fast + 1
      }join;
      goto loop
    }skip
  }loop invariant 0 <= fast && fast <= len;
  r := fast
};
"

/-- info: verified -/
#guard_msgs in
#eval verify backEdgeAfterIfElse

private def globalAcrossCall := r"
var g: int := 0
procedure setG(x: int) returns (r: int)
  opaque
  ensures g == x && r == x
{
  g := x;
  r := x
};
procedure main()
  opaque
{
  g := 1;
  stki := g;
  stki := setG(5);
  var y: int := stk + stk;
  assert y == 6
};
"

/--
info: procedure setG(x: int)
  returns (r: int)
  opaque
  ensures g == x && r == x
{
  g := x;
  r := x
};
procedure main()
  opaque
{
  g := 1;
  var $stack_0: int := g;
  var $stack_1: int := setG(5);
  var y: int := $stack_0 + $stack_1;
  assert y == 6
};
-/
#guard_msgs in
#eval showEliminated globalAcrossCall

/-- info: verified -/
#guard_msgs in
#eval verify globalAcrossCall

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret globalAcrossCall

private def fieldWriteOrder := r"
composite Node {
  var next: Node
  var v: int
}
procedure redirect(h: Node, b: Node) returns (r: int)
  opaque
  ensures h#next == b && r == 7
  modifies h
{
  h#next := b;
  r := 7
};
procedure main()
  opaque
{
  var a: Node := new Node;
  var b: Node := new Node;
  var h: Node := new Node;
  h#next := a;
  h#next#v := redirect(h, b);
  assert a#v == 7
};
"

/-- info: verified -/
#guard_msgs in
#eval verify fieldWriteOrder

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret fieldWriteOrder

private def permutedOne := r"
procedure main()
  opaque
{
  stk := 3;
  stk := permute_0(stk);
  var y: int := stk;
  assert y == 3
};
"

/--
info: procedure main()
  opaque
{
  var y: int := 3;
  assert y == 3
};
-/
#guard_msgs in
#eval showEliminated permutedOne

/-- info: verified -/
#guard_msgs in
#eval verify permutedOne

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret permutedOne

private def permutedOneOfTwo := r"
procedure main()
  opaque
{
  stk := 1;
  stk := 2;
  stk := permute_1(stk, stk);
  var y: int := stk;
  assert y == 2
};
"

/--
info: procedure main()
  opaque
{
  var $stack_0 := 1;
  var y: int := 2;
  assert y == 2
};
-/
#guard_msgs in
#eval showEliminated permutedOneOfTwo

/-- info: verified -/
#guard_msgs in
#eval verify permutedOneOfTwo

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret permutedOneOfTwo

private def stackRootedReceiver := r"
composite Node {
  var next: Node
  var v: int
}
procedure redirect(h: Node, b: Node) returns (r: int)
  opaque
  ensures h#next == b && r == 7
  modifies h
{
  h#next := b;
  r := 7
};
procedure main()
  opaque
{
  var a: Node := new Node;
  var b: Node := new Node;
  var h: Node := new Node;
  h#next := a;
  stk := h;
  stk#next#v := redirect(h, b);
  assert a#v == 7
};
"

/-- info: verified -/
#guard_msgs in
#eval verify stackRootedReceiver

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret stackRootedReceiver

private def userLocalFromCallNotFolded := r"
procedure read(n: int) returns (r: int)
  requires n > 0
  opaque
  ensures r == 5
{
  r := 5
};
procedure main()
  opaque
{
  var x: int := read(1);
  if (x > 0) then { x := 1 } else { x := -1 };
  stki := x;
  var y: int := stk;
  assert y == 1
};
"

/--
info: procedure read(n: int)
  returns (r: int)
  requires n > 0
  opaque
  ensures r == 5
{
  r := 5
};
procedure main()
  opaque
{
  var x: int := read(1);
  if x > 0
    then {
      x := 1
    }
    else {
      x := -1
    };
  var y: int := x;
  assert y == 1
};
-/
#guard_msgs in
#eval showEliminated userLocalFromCallNotFolded

/-- info: verified -/
#guard_msgs in
#eval verify userLocalFromCallNotFolded

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret userLocalFromCallNotFolded

private def oldOfUserLocal := r"
composite Node { var next: Node  var v: int }
procedure m(t: Node, o: Node)
  opaque
  modifies t
{
  t#next := o;
  stk := t;
  stk := stk#next;
  var n: Node := stk;
  stk := n;
  stk := stk#v;
  var r: int := old(stk);
  assert r == old(o#v)
};
"

/--
info: procedure m(t: Node, o: Node)
  opaque
  modifies t
{
  t#next := o;
  var n: Node := t#next;
  var r: int := old(old(n)#v);
  assert r == old(o#v)
};
-/
#guard_msgs in
#eval showEliminated oldOfUserLocal

/-- info: verified -/
#guard_msgs in
#eval verify oldOfUserLocal

private def oldOfAssignedInput := r"
procedure m(p: int) returns (r: int)
  opaque
{
  p := p + 1;
  stk := p;
  stk := old(stk);
  var y: int := stk;
  assert y == p
};
"

/--
info: procedure m(p: int)
  returns (r: int)
  opaque
{
  p := p + 1;
  var y: int := old(p);
  assert y == p
};
-/
#guard_msgs in
#eval showEliminated oldOfAssignedInput (exprReadsHeap {})

/-- info: userError: assertion does not hold -/
#guard_msgs in
#eval verify oldOfAssignedInput

private def oldOfAssignedInputHolds := r"
procedure m(p: int) returns (r: int)
  opaque
{
  p := p + 1;
  stk := p;
  stk := old(stk);
  var y: int := stk;
  assert y + 1 == p
};
"

/--
info: procedure m(p: int)
  returns (r: int)
  opaque
{
  p := p + 1;
  var y: int := old(p);
  assert y + 1 == p
};
-/
#guard_msgs in
#eval showEliminated oldOfAssignedInputHolds (exprReadsHeap {})

/-- info: verified -/
#guard_msgs in
#eval verify oldOfAssignedInputHolds

private def andMerge := r"
procedure f(i: int) returns (r: int)
  requires {
    stki := i;
    {
      {
        {
          if (!(0 <= stk)) then { exit skip };
          stki := i;
          if (!(stk <= 3)) then { exit merge0 };
          { stkb := true; exit merge1 }
        }skip
      }merge0;
      stkb := false
    }merge1;
    stk
  }
  opaque
  ensures r == i
{
  r := i
};
procedure main()
  opaque
{
  var a: int := f(2);
  assert a == 2
};
"

/--
info: procedure f(i: int)
  returns (r: int)
  requires 0 <= i && i <= 3
  opaque
  ensures r == i
{
  r := i
};
procedure main()
  opaque
{
  var a: int := f(2);
  assert a == 2
};
-/
#guard_msgs in
#eval showEliminated andMerge

/-- info: verified -/
#guard_msgs in
#eval verify andMerge

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret andMerge

private def orMerge := r"
procedure f(i: int) returns (r: int)
  requires {
    stki := i;
    {
      {
        {
          if (stk < 0) then { exit skip };
          stki := i;
          if (stk > 3) then { exit merge0 };
          { stkb := false; exit merge1 }
        }skip
      }merge0;
      stkb := true
    }merge1;
    stk
  }
  opaque
  ensures r == i
{
  r := i
};
procedure main()
  opaque
{
  var a: int := f(5);
  assert a == 5
};
"

/--
info: procedure f(i: int)
  returns (r: int)
  requires i < 0 || i > 3
  opaque
  ensures r == i
{
  r := i
};
procedure main()
  opaque
{
  var a: int := f(5);
  assert a == 5
};
-/
#guard_msgs in
#eval showEliminated orMerge

/-- info: verified -/
#guard_msgs in
#eval verify orMerge

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret orMerge

private def andChain := r"
procedure f(i: int, n: int) returns (r: int)
  requires {
    stki := i;
    {
      {
        {
          if (!(0 <= stk)) then { exit skip };
          stki := i;
          stki := n;
          if (!(stk < stk)) then { exit merge0 };
          stki := n;
          if (!(stk < 100)) then { exit merge0 };
          { stkb := true; exit merge1 }
        }skip
      }merge0;
      stkb := false
    }merge1;
    stk
  }
  opaque
  ensures r == i
{
  r := i
};
procedure main()
  opaque
{
  var a: int := f(2, 5);
  assert a == 2
};
"

/--
info: procedure f(i: int, n: int)
  returns (r: int)
  requires 0 <= i && (i < n && n < 100)
  opaque
  ensures r == i
{
  r := i
};
procedure main()
  opaque
{
  var a: int := f(2, 5);
  assert a == 2
};
-/
#guard_msgs in
#eval showEliminated andChain

/-- info: verified -/
#guard_msgs in
#eval verify andChain

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret andChain

private def nonLiteralTail := r"
procedure f(i: int) returns (r: bool)
  opaque
  ensures r == (0 <= i && i <= 3 || i == 9)
{
  stki := i;
  {
    {
      {
        if (!(0 <= stk)) then { exit skip };
        stki := i;
        if (!(stk <= 3)) then { exit merge0 };
        { stkb := true; exit merge1 }
      }skip
    }merge0;
    stkb := i == 9
  }merge1;
  r := stk
};
procedure main()
  opaque
{
  var a: bool := f(9);
  assert a
};
"

/--
info: procedure f(i: int)
  returns (r: bool)
  opaque
  ensures r == (0 <= i && i <= 3 || i == 9)
{
  var $stack_5: bool := false;
  {
    if !(0 <= i)
      then {
        
      }
      else {
        if !(i <= 3)
          then {
            
          }
          else {
            $stack_5 := true;
            exit merge1
          }
      };
    $stack_5 := i == 9
  }merge1;
  r := $stack_5
};
procedure main()
  opaque
{
  var a: bool := f(9);
  assert a
};
-/
#guard_msgs in
#eval showEliminated nonLiteralTail

/-- info: verified -/
#guard_msgs in
#eval verify nonLiteralTail

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret nonLiteralTail

private def callTail := r"
procedure isNine(x: int) returns (r: bool)
  opaque
  ensures r == (x == 9)
{
  r := x == 9
};
procedure f(i: int) returns (r: bool)
  opaque
  ensures r == (0 <= i && i <= 3 || i == 9)
{
  stki := i;
  {
    {
      {
        if (!(0 <= stk)) then { exit skip };
        stki := i;
        if (!(stk <= 3)) then { exit merge0 };
        { stkb := true; exit merge1 }
      }skip
    }merge0;
    stkb := isNine(i)
  }merge1;
  r := stk
};
procedure main()
  opaque
{
  var a: bool := f(9);
  assert a
};
"

/--
info: procedure isNine(x: int)
  returns (r: bool)
  opaque
  ensures r == (x == 9)
{
  r := x == 9
};
procedure f(i: int)
  returns (r: bool)
  opaque
  ensures r == (0 <= i && i <= 3 || i == 9)
{
  var $stack_5: bool := false;
  {
    if !(0 <= i)
      then {
        
      }
      else {
        if !(i <= 3)
          then {
            
          }
          else {
            $stack_5 := true;
            exit merge1
          }
      };
    $stack_5 := isNine(i)
  }merge1;
  r := $stack_5
};
procedure main()
  opaque
{
  var a: bool := f(9);
  assert a
};
-/
#guard_msgs in
#eval showEliminated callTail

/-- info: verified -/
#guard_msgs in
#eval verify callTail

/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret callTail

private def cortexWarnings (source : String) : IO Unit := do
  match Cortex.resolveLaurel {} (← parse source) with
  | .ok (_, _, ms) => for m in ms do IO.println s!"{m.kind}: {m.message}"
  | .error ms => for m in ms do IO.println s!"error-branch {m.kind}: {m.message}"

private def warnedStackProgram := r"
procedure f(x: int) returns (r: int)
  opaque
  ensures old(old(x)) == x
{
  stki := x;
  r := stk
};
"

/--
info: warning: nested `old(...)` has no effect
warning: `old(...)` has no effect: the enclosing procedure does not modify the heap
-/
#guard_msgs in
#eval cortexWarnings warnedStackProgram

private def heimdallChain := r"
procedure f(c: int) returns (r: bool)
  opaque
  ensures r == ((c >= 0 && c <= 5) || (c >= 10 && c <= 15) || (c >= 20 && c <= 25))
{
  {
    {
      {
        {
          if (c < 0) then { exit L0 };
          if (c <= 5) then { exit T }
        }L0;
        {
          if (c < 10) then { exit L1 };
          if (c <= 15) then { exit T }
        }L1;
        if (c < 20) then { exit F };
        if (c > 25) then { exit F }
      }T;
      stkb := true;
      exit E
    }F;
    stkb := false
  }E;
  r := stk
};
"

/--
info: procedure f(c: int)
  returns (r: bool)
  opaque
  ensures r == (c >= 0 && c <= 5 || c >= 10 && c <= 15 || c >= 20 && c <= 25)
{
  r := !(c < 0) && c <= 5 || (!(c < 10) && c <= 15 || !(c < 20) && !(c > 25))
};
-/
#guard_msgs in
#eval showEliminated heimdallChain
/-- info: verified -/
#guard_msgs in
#eval verify heimdallChain

private def disjunctChain (bounds expect : List (Nat × Nat)) : String :=
  let plain := " || ".intercalate (expect.map fun (lo, hi) => s!"(c >= {lo} && c <= {hi})")
  let arms := ((List.range (bounds.length - 1)).zip (bounds.dropLast)).map fun (i, (lo, hi)) =>
    s!"        {"{"} if (c < {lo}) then {"{"} exit L{i} {"}"}; if (c <= {hi}) then {"{"} exit T {"}"} {"}"} L{i};"
  let last := match bounds.getLast? with
    | some (lo, hi) => s!"        if (c < {lo}) then {"{"} exit F {"}"};\n        if (c > {hi}) then {"{"} exit F {"}"}"
    | none => ""
  s!"procedure f(c: int) returns (r: bool)
  opaque
  ensures r == ({plain})
\{
  \{
    \{
      \{
{"\n".intercalate (arms ++ [last])}
    }T;
    stkb := true;
    exit E
  }F;
  stkb := false
}E;
  r := stk
};
procedure main()
  opaque
\{
  var a: bool := f(3);
  assert a
};
"

private def fifteen := (List.range 15).map fun i => (10 * i, 10 * i + 5)

/--
info: procedure f(c: int)
  returns (r: bool)
  opaque
  ensures r == (c >= 0 && c <= 5 || c >= 10 && c <= 15 || c >= 20 && c <= 25 || c >= 30 && c <= 35 || c >= 40 && c <= 45 || c >= 50 && c <= 55 || c >= 60 && c <= 65 || c >= 70 && c <= 75 || c >= 80 && c <= 85 || c >= 90 && c <= 95 || c >= 100 && c <= 105 || c >= 110 && c <= 115 || c >= 120 && c <= 125 || c >= 130 && c <= 135 || c >= 140 && c <= 145)
{
  r := !(c < 0) && c <= 5 || (!(c < 10) && c <= 15 || (!(c < 20) && c <= 25 || (!(c < 30) && c <= 35 || (!(c < 40) && c <= 45 || (!(c < 50) && c <= 55 || (!(c < 60) && c <= 65 || (!(c < 70) && c <= 75 || (!(c < 80) && c <= 85 || (!(c < 90) && c <= 95 || (!(c < 100) && c <= 105 || (!(c < 110) && c <= 115 || (!(c < 120) && c <= 125 || (!(c < 130) && c <= 135 || !(c < 140) && !(c > 145))))))))))))))
};
procedure main()
  opaque
{
  var a: bool := f(3);
  assert a
};
-/
#guard_msgs in
#eval showEliminated (disjunctChain fifteen fifteen)
/-- info: verified -/
#guard_msgs in
#eval verify (disjunctChain fifteen fifteen)
/-- info: userError: postcondition does not hold -/
#guard_msgs in
#eval verify (disjunctChain (fifteen.set 7 (70, 74)) fifteen)

private def nestedOrHeimdall := r"
procedure f(i: int) returns (r: int)
  requires {
    {
      {
        {
          {
            if (!(0 <= i)) then { exit L0 };
            if (i <= 3) then { exit T }
          }L0;
          if (!(i == 9)) then { exit F }
        }T;
        stkb := true;
        exit E
      }F;
      stkb := false
    }E;
    stk
  }
  opaque
  ensures r == i
{
  r := i
};
procedure main()
  opaque
{
  var a: int := f(2);
  assert a == 2
};
"

/--
info: procedure f(i: int)
  returns (r: int)
  requires 0 <= i && i <= 3 || i == 9
  opaque
  ensures r == i
{
  r := i
};
procedure main()
  opaque
{
  var a: int := f(2);
  assert a == 2
};
-/
#guard_msgs in
#eval showEliminated nestedOrHeimdall
/-- info: verified -/
#guard_msgs in
#eval verify nestedOrHeimdall
/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret nestedOrHeimdall

private def stackReads := r"
procedure f(c: int) returns (r: bool)
  opaque
  ensures r == (c >= 0 && c <= 5 || c >= 10 && c <= 15)
{
  {
    {
      {
        {
        stki := c;
        if (stk < 0) then { exit L0 };
        stki := c;
        if (stk <= 5) then { exit T }
      }L0;
      stki := c;
      if (stk < 10) then { exit F };
      stki := c;
      if (stk > 15) then { exit F }
    }T;
    stkb := true;
    exit E
  }F;
  stkb := false
}E;
  r := stk
};
procedure main()
  opaque
{
  var a: bool := f(12);
  assert a
};
"

/--
info: procedure f(c: int)
  returns (r: bool)
  opaque
  ensures r == (c >= 0 && c <= 5 || c >= 10 && c <= 15)
{
  r := !(c < 0) && c <= 5 || !(c < 10) && !(c > 15)
};
procedure main()
  opaque
{
  var a: bool := f(12);
  assert a
};
-/
#guard_msgs in
#eval showEliminated stackReads
/-- info: verified -/
#guard_msgs in
#eval verify stackReads
/--
info: failures: #[]
completed
-/
#guard_msgs in
#eval interpret stackReads

private def userLocalLeaf := r"
procedure g(c: int) returns (r: bool)
  opaque
{
  var hits: int := 0;
  {
    {
      {
        {
        stki := c;
        if (stk < 0) then { hits := hits + 1; exit L0 };
        stki := c;
        if (stk <= 5) then { exit T }
      }L0;
      stki := c;
      if (stk < 10) then { exit F };
      stki := c;
      if (stk > 15) then { exit F }
    }T;
    stkb := true;
    exit E
  }F;
  stkb := false
}E;
  r := stk
};
"

/--
info: procedure g(c: int)
  returns (r: bool)
  opaque
{
  var hits: int := 0;
  var $stack_10: bool := false;
  {
    {
      {
        if c < 0
          then {
            hits := hits + 1
          }
          else if c <= 5
            then exit T;
        if c < 10
          then exit F;
        if c > 15
          then exit F
      }T;
      $stack_10 := true;
      exit E
    }F;
    $stack_10 := false
  }E;
  r := $stack_10
};
-/
#guard_msgs in
#eval showEliminated userLocalLeaf

private def nestedOrTwoLeaves := r"
procedure f(i: int) returns (r: int)
  requires {
    {
      {
        {
          if (!(0 <= i)) then { exit skip };
          if (!(i <= 3)) then { exit merge0 };
          { stkb := true; exit merge1 }
        }skip;
        if (!(i == 9)) then { exit merge0 };
        { stkb := true; exit merge1 }
      }merge0;
      stkb := false
    }merge1;
    stk
  }
  opaque
  ensures r == i
{
  r := i
};
"

/--
info: procedure f(i: int)
  returns (r: int)
  requires {
  var $stack_7: bool := false;
  {
    {
      if !(0 <= i)
        then {
          
        }
        else {
          if !(i <= 3)
            then exit merge0;
          $stack_7 := true;
          exit merge1
        };
      if !(i == 9)
        then exit merge0;
      $stack_7 := true;
      exit merge1
    }merge0;
    $stack_7 := false
  }merge1;
  $stack_7
}
  opaque
  ensures r == i
{
  r := i
};
-/
#guard_msgs in
#eval showEliminated nestedOrTwoLeaves

end Strata.Laurel
