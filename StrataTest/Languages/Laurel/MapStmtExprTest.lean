/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for the generic `mapStmtExprM` traversal. Verifies that `mapStmtExpr id`
is the identity: applying it to a parsed program produces identical output.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.Resolution

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

private def parseLaurel (input : String) : IO Program := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program => pure (resolve program).program

private def printProcs (program : Program) : IO String := do
  let mut out := ""
  for proc in program.staticProcedures do
    let s := toString (Std.Format.pretty (Std.ToFormat.format proc))
    out := out ++ s ++ "\n"
  pure out

/-- Verify `mapStmtExpr id` is the identity by comparing printed output before
    and after the transformation. -/
private def testMapStmtExprId (input : String) : IO Unit := do
  let program ← parseLaurel input
  let mapped := mapProgram (mapStmtExpr id) program
  let before ← printProcs program
  let after ← printProcs mapped
  if before == after then
    IO.println "ok: mapStmtExpr id ≡ id"
  else
    IO.println s!"MISMATCH\nbefore:\n{before}\nafter:\n{after}"

-- Exercises: IfThenElse, Block, LocalVariable, While, Return, Assign,
-- PrimitiveOp, Assert, Assume, Forall, Exists, LiteralInt, LiteralBool, Identifier.
def testProgram : String := r"
procedure test(x: int, b: bool) returns (r: int)
  requires x > 0
  opaque
  ensures r >= 0
{
  var y: int := x;
  if b then {
    y := y + 1
  } else {
    y := y - 1
  };
  while(y > 0)
    invariant y >= 0
  {
    y := y - 1
  };
  assert y == 0;
  assume y >= 0;
  var q: bool := forall(i: int) => i >= 0;
  var p: bool := exists(j: int) => j > 0;
  return y
};
"

/--
info: ok: mapStmtExpr id ≡ id
-/
#guard_msgs in
#eval! testMapStmtExprId testProgram

end Strata.Laurel
