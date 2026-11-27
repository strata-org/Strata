/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation
import StrataLaurel.Implementation.LaurelCompilationPipeline
import StrataCortex.Implementation.Pipeline
import StrataCortex.Implementation.Interpret

/-! # The Cortex translation of a Laurel program

The entry point `Cortex.translate` and its resolution: a program that uses the Stack is
resolved a second time after the stack is eliminated, with the same allowance for
constrained-type globals in an entry procedure. -/

open Strata

namespace Cortex.TranslateTest

open Strata.Laurel

/-- The locals `stk` and `stki` stand for Laurel's Stack, as in `EliminateStackTest`. -/
private def stackOf (name : Identifier) (source : FileRange) : Option Variable :=
  match name.text with
  | "stk" => some (.Stack none)
  | "stki" => some (.Stack (some ⟨.TInt, source⟩))
  | _ => none

private def toStack (program : LaurelProgram) : LaurelProgram :=
  let node (e : StmtExprMd) : StmtExprMd :=
    match e.val with
    | .Var (.Local name) => match stackOf name e.source with
      | some v => ⟨.Var v, e.source⟩
      | none => e
    | .Assign targets value =>
      ⟨.Assign (targets.map fun t => match t.val with
        | .Local name => match stackOf name t.source with
          | some v => ⟨v, t.source⟩
          | none => t
        | _ => t) value, e.source⟩
    | _ => e
  mapLaurelProgramProcedures (fun proc => mapProcedureM (m := Id) (mapStmtExpr node) proc) program

private def parse (source : String) : IO LaurelProgram :=
  return toStack (← (Strata.parseLaurelText "<cortex-translate-test>" source : IO LaurelProgram))

private def printMessages (ms : List Message) : IO Unit := do
  for m in ms do IO.println s!"{m.fileRange.range.start.byteIdx}: {m.message}"

/-- An entry procedure that reads a constrained-type global through the stack. -/
private def stackGlobal := "
constrained small = x: int where 0 <= x && x < 10 witness 0
var c: small := 3

procedure main() entry
  opaque
{
    stki := 1;
    c := c + stk;
    assert c == 4
};
"

/-- info: resolved -/
#guard_msgs in
#eval show IO Unit from do
  match Cortex.resolveLaurel {} (← parse stackGlobal) with
  | .ok _ => IO.println "resolved"
  | .error ms => printMessages ms

/-- info: Core type checking succeeded. -/
#guard_msgs in
#eval show IO Unit from do
  let (core?, ms) := Cortex.translate {} (← parse stackGlobal)
  printMessages ms
  let some core := core? | IO.println "not translated"
  match Core.typeCheck .quiet core with
  | .error e => IO.println s!"Core type checking failed: {e}"
  | .ok _ => IO.println "Core type checking succeeded."

#guard_msgs in
#eval show IO Unit from do
  match Cortex.interpretEntries (← parse stackGlobal) with
  | .error e => IO.println s!"error: {e}"
  | .ok outcome =>
    printMessages outcome.diagnostics.toList
    for (name, reason) in outcome.errors do IO.println s!"stopped: '{name}': {reason}"

/-- A stack value read from an array element keeps the value it had when it was pushed,
    across a later call that writes the element: Java's `int r = a[0] + bump(a)`. -/
private def stackReadBeforeArrayWrite := "
procedure bump(a: Array<int>)
  opaque
  modifies *
{
    a[0] := 5
};

procedure main() entry
  opaque
  modifies *
{
    var a: Array<int> := new Array<int>(1);
    stki := a[0];
    bump(a);
    var r: int := stki;
    assert r == 0
};
"

/-- info: passed -/
#guard_msgs in
#eval show IO Unit from do
  match Cortex.interpretEntries (← parse stackReadBeforeArrayWrite) with
  | .error e => IO.println s!"error: {e}"
  | .ok outcome =>
    if outcome.diagnostics.isEmpty && outcome.errors.isEmpty then IO.println "passed"
    printMessages outcome.diagnostics.toList
    for (name, reason) in outcome.errors do IO.println s!"stopped: '{name}': {reason}"

/-- The same, when the element is read by a call: a procedure that reads an array it is given
    reads the heap, so the stack value of the call is not read after the write. -/
private def stackCallReadBeforeArrayWrite := "
procedure get(a: Array<int>) returns (r: int)
{
    a[0]
};

procedure bump(a: Array<int>)
  opaque
  modifies *
{
    a[0] := 5
};

procedure main() entry
  opaque
  modifies *
{
    var a: Array<int> := new Array<int>(1);
    stki := get(a);
    bump(a);
    var r: int := stki;
    assert r == 0
};
"

/-- info: passed -/
#guard_msgs in
#eval show IO Unit from do
  match Cortex.interpretEntries (← parse stackCallReadBeforeArrayWrite) with
  | .error e => IO.println s!"error: {e}"
  | .ok outcome =>
    if outcome.diagnostics.isEmpty && outcome.errors.isEmpty then IO.println "passed"
    printMessages outcome.diagnostics.toList
    for (name, reason) in outcome.errors do IO.println s!"stopped: '{name}': {reason}"

end Cortex.TranslateTest
