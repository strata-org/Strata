/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Before/after tests for the `CoroutineElaboration` pass (see
CoroutineElaboration.lean). Each `#strata` block is the *source* coroutine and
its caller (the "before"); the `#guard_msgs` block is the *elaborated* program
the pass produces (the "after"), printed as Laurel source.

`CoroutineElaboration` runs in two modes:

  * **Full elaboration** (`verifyCoroutine := false`, the default) — replaces
    `coroutine c` with a state-machine composite `cState` (a `$pc` control
    field, one field per input / body local / yield, plus `resume` and
    `has_next` instance procedures whose bodies are the linearized dispatch
    loop) and a spawn constructor named `c`. Callers are retargeted:
    `co: c` → `co: cState`, `resume(co)` → `co#resume()`,
    `has_next(co)` → `co#has_next()`.

  * **Caller-verification elaboration** (`verifyCoroutine := true`) — the same
    `cState` composite, but `resume`/`has_next` are left *opaque* summaries
    (relies → preconditions, guarantees → postconditions; `has_next` a constant
    `true`). The coroutine body is kept as a `c$body` procedure for YieldElim to
    verify against the declared rely/guarantee. This is the path `YieldElim`
    consumes (body rewrite + caller-side rely-heap threading).

The pass needs a resolved program (`needsResolves := true`), so each test
resolves first and then drives `coroutineElaborationPass.run`.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.CoroutineElaboration
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Resolve `program`, run `CoroutineElaboration` under `options`, and print the
    elaborated program as Laurel source in two labeled sections — the generated
    types (the `<c>State` composites) then the procedures (spawn constructors,
    rewritten callers, and `$body` copies under `verifyCoroutine`) — plus any
    diagnostics the pass emitted. `verifyCoroutine` selects the mode. -/
private def printElaborated (verifyCoroutine : Bool) (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  let options : LaurelTranslateOptions := { verifyCoroutine }
  let (elaborated, diags, _) := coroutineElaborationPass.run options result.program result.model
  IO.println "-- types --"
  for ty in elaborated.types do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format ty)))
  IO.println "-- procedures --"
  for proc in elaborated.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))
  for d in diags do
    IO.println s!"diagnostic: {d.message}"

/-- Print the elaborated program under **full elaboration** (`verifyCoroutine := false`). -/
private def printFull (program : StrataDDM.Program) : IO Unit :=
  printElaborated (verifyCoroutine := false) program

/-- Print the elaborated program under **caller-verification elaboration**
    (`verifyCoroutine := true`). -/
private def printVerify (program : StrataDDM.Program) : IO Unit :=
  printElaborated (verifyCoroutine := true) program

/-! ## Full elaboration: a value-yielding counter driven by a caller

The `counter` coroutine becomes a `counterState` composite (a `$pc` field, the
`i` local and the `x` yield promoted to fields, `resume`/`has_next` instance
procedures holding the linearized state machine) plus a spawn constructor
`counter`. The `driver`'s `var co: counter := counter()` keeps the constructor
call but the annotation is retargeted to `counterState`, and `resume(co)`
becomes `co#resume()`. -/

/--
info: -- types --
composite counterState { var $pc: int var i: int var x: intprocedure resume(self: counterState)
  returns (x: int)
  requires self#$pc != 0
  opaque
  modifies self
while(true) if self#$pc == 1
  then {
    assert self#i >= 0;
    if self#i < 3
      then self#$pc := 5
      else self#$pc := 0
  }
  else if self#$pc == 3
    then {
      self#i := self#i + 1;
      assert self#i >= 0;
      self#$pc := 1
    }
    else if self#$pc == 5
      then {
        self#x := self#i;
        self#$pc := 3;
        {
          x := self#x;
          return 
        }
      }
      else if self#$pc == 6
        then {
          self#i := 0;
          self#$pc := 1
        }
        else {
          x := self#x;
          return 
        };procedure has_next(self: counterState)
  returns (result: bool)
return self#$pc != 0; }
-- procedures --
procedure driver()
  opaque
{
  var co: counterState := counter();
  co#resume()
};
procedure counter()
  returns ($co: counterState)
  opaque
  ensures $co#$pc == 6
{
  $co := new counterState;
  $co#$pc := 6
};
-/
#guard_msgs in
#eval printFull
#strata
program Laurel;
coroutine counter() yields (x: int)
{
  var i: int := 0;
  while (i < 3)
    invariant i >= 0
  {
    x := i;
    yield;
    i := i + 1
  }
};

procedure driver()
  opaque
{
  var co: counter := counter();
  resume(co)
};
#end

/-! ## Caller-verification elaboration: opaque `resume` summary + `$body`

Under `verifyCoroutine := true` the same `echoState` composite is generated, but
`resume` is an *opaque* procedure whose precondition is the `relies` clause and
whose postcondition is the `guarantees` clause (no linearized body). The
coroutine body survives as `echo$body` for YieldElim to check against the
declared rely/guarantee. -/

/--
info: -- types --
composite echoState { var $pc: int var x: intprocedure resume(self: echoState, y: int)
  returns (x: int)
  requires y >= 0
  opaque
  ensures x >= 0;procedure has_next(self: echoState)
  returns (result: bool)
return true; }
-- procedures --
procedure driver()
  opaque
{
  var co: echoState := echo();
  co#resume(42)
};
procedure echo()
  returns ($co: echoState)
  opaque
  ensures $co#$pc == 1
{
  $co := new echoState;
  $co#$pc := 1
};
procedure echo$body()
  opaque
{
  x := 0;
  yield
};
-/
#guard_msgs in
#eval printVerify
#strata
program Laurel;
coroutine echo() yields (x: int) resumes (y: int)
  relies y >= 0
  guarantees x >= 0
{
  x := 0; yield
};

procedure driver()
  opaque
{
  var co: echo := echo();
  resume(co, 42)
};
#end

/-! ## Full elaboration: a value-receiving `resume`

`w := yield` (a value-receiving suspend) splits into two states: a suspend that
returns to the caller, and a resume state that binds the incoming resume
argument `n` into the promoted local (`self#w := n`) before continuing. The
resume argument is a parameter of the generated `resume`, not coroutine state,
so it is read as a plain local. On the caller side `z := resume(co, 7)` becomes
`z := co#resume(7)`. -/

/--
info: -- types --
composite accumulateState { var $pc: int var w: int var sum: intprocedure resume(self: accumulateState, n: int)
  returns (sum: int)
  requires self#$pc != 0
  opaque
  modifies self
while(true) if self#$pc == 2
  then {
    self#w := n;
    self#sum := self#w;
    self#$pc := 0
  }
  else if self#$pc == 4
    then {
      self#w := 0;
      self#$pc := 2;
      {
        sum := self#sum;
        return 
      }
    }
    else {
      sum := self#sum;
      return 
    };procedure has_next(self: accumulateState)
  returns (result: bool)
return self#$pc != 0; }
-- procedures --
procedure driver()
  opaque
{
  var co: accumulateState := accumulate();
  var z: int := 0;
  z := co#resume(7)
};
procedure accumulate()
  returns ($co: accumulateState)
  opaque
  ensures $co#$pc == 4
{
  $co := new accumulateState;
  $co#$pc := 4
};
-/
#guard_msgs in
#eval printFull
#strata
program Laurel;
coroutine accumulate() yields (sum: int) resumes (n: int)
{
  var w: int := 0;
  w := yield;
  sum := w
};

procedure driver()
  opaque
{
  var co: accumulate := accumulate();
  var z: int := 0;
  z := resume(co, 7)
};
#end

end Laurel
