/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that the expression lifter correctly handles statement constructs
(heap-updating assignments) in non-last positions of block expressions,
by comparing the lifted Laurel against expected output.
-/

meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar
meta import Strata.Languages.Laurel.LaurelToCoreTranslator
meta import Strata.Languages.Laurel.LiftImperativeExpressions

meta section

open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

def blockStmtLiftingProgram : String := r"
procedure assertInBlockExpr()
  opaque
{
  var x: int := 0;
  var y: int := { assert x == 0; x := 1; x };
  assert y == 1
};
"

def parseLaurelAndLift (input : String) : IO Program := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    let imperativeCallees := program.staticProcedures |>.map (fun p => p.name.text)
    pure (liftExpressionAssignments program model imperativeCallees)

/--
info: procedure assertInBlockExpr()
  opaque
{
  var x: int := 0;
  assert $x_0 == 0;
  var $x_0: int := x;
  x := 1;
  var y: int := {
    x
  };
  assert y == 1
};
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndLift blockStmtLiftingProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

end Laurel
end Strata
end
