/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the expression lifter correctly handles statement constructs
(heap-updating assignments) in non-last positions of block expressions,
by comparing the lifted Laurel against expected output.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

def blockStmtLiftingProgram : String := r"
composite Box {
  var value: int
}

procedure heapUpdateInBlockExpr(b: Box)
{
  var x: int := { b#value := b#value + 1; b#value };
  assert x == b#value;
}

procedure assertInBlockExpr()
{
  var x: int := 0;
  var y: int := { assert x == 0; x := 1; x };
  assert y == 1;
}
"

def parseLaurelAndLift (input : String) : IO Program := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program => pure (liftExpressionAssignments program)

/--
info: procedure heapUpdateInBlockExpr(b: Box) returns 
()
deterministic
{ b#value := b#value + 1; var x: int := b#value; assert x == b#value }
procedure assertInBlockExpr() returns 
()
deterministic
{ var x: int := 0; assert x == 0; x := 1; var y: int := x; assert y == 1 }
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndLift blockStmtLiftingProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

end Laurel
