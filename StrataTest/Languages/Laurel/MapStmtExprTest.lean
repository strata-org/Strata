/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for the generic `mapStmtExprM` traversal. Verifies that `mapStmtExpr id`
is the identity: applying it to a parsed program produces identical output.
-/
module

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseAndResolve (program : StrataDDM.Program) : IO Program := do
  let laurelProgram ← translateLaurel program
  pure (resolve laurelProgram).program

private def printProcs (program : Program) : IO String := do
  let mut out := ""
  for proc in program.staticProcedures do
    let s := toString (Std.Format.pretty (Std.ToFormat.format proc))
    out := out ++ s ++ "\n"
  pure out

/-- Verify `mapStmtExpr id` is the identity by comparing printed output before
    and after the transformation. -/
private def testMapStmtExprId (program : StrataDDM.Program) : IO Unit := do
  let parsed ← parseAndResolve program
  let mapped := mapProgram (mapStmtExpr id) parsed
  let before ← printProcs parsed
  let after ← printProcs mapped
  if before == after then
    IO.println "ok: mapStmtExpr id ≡ id"
  else
    IO.println s!"MISMATCH\nbefore:\n{before}\nafter:\n{after}"

-- Exercises: IfThenElse, Block, Var Declare, While, Return, Assign,
-- PrimitiveOp, Assert, Assume, Forall, Exists, LiteralInt, LiteralBool, Identifier.

/--
info: ok: mapStmtExpr id ≡ id
-/
#guard_msgs in
#eval! testMapStmtExprId
#strata
program Laurel;
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
#end

end Strata.Laurel
