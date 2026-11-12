/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation
import StrataLaurel.Implementation.LaurelCompilationPipeline
import StrataCortex.Implementation.Pipeline

/-! # The Cortex translation of a Laurel program

The entry point `Cortex.translate` and its resolution: a program that uses the Stack is
resolved a second time after the stack is eliminated, with the same allowance for
constrained-type globals in an entry procedure; and inlining is refused with CFG bodies. -/

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

#guard_msgs in
#eval show IO Unit from do
  let ms ← Cortex.verifyToMessages (← parse stackGlobal) { verifyOptions := Core.VerifyOptions.quiet }
  printMessages ms.toList

/-- info: 0: --inline-procedures works on structured bodies, which the CFG translation does not produce -/
#guard_msgs in
#eval show IO Unit from do
  let (core?, ms) := Cortex.translate {} (← parse stackGlobal) (cfg := true) (inline := ["main"])
  if core?.isSome then IO.println "translated"
  printMessages ms

end Cortex.TranslateTest
