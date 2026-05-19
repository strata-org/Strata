/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Idiomaticity tests for the expression lifter: pin the *shape* of the Laurel
output produced by `liftExpressionAssignments` for a few representative
input programs.

This is a quality-of-output check, not a correctness check. Programs that
must verify cleanly through the full deductive-verification pipeline live
in `StrataTest/Languages/Laurel/Examples/`; tests here only run
parse + resolve + lift and compare the printed Laurel against an
expected string.
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
procedure assertInBlockExpr()
  opaque
{
  var x: int := 0;
  var y: int := { assert x == 0; x := 1; x };
  assert y == 1
};

procedure nestedBlockInDeclInit()
  opaque
{
  var x: int := 0;
  var y: int := { var t: int := { x := 1; x }; t + 1 };
  assert y == 2
};
"

def parseLaurelAndLift (input : String) : IO Program := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    pure (liftExpressionAssignments model program)

/--
info: procedure assertInBlockExpr()
  opaque
{ var x: int := 0; assert x == 0; var $x_0: int := x; x := 1; var y: int := { x }; assert y == 1 };
procedure nestedBlockInDeclInit()
  opaque
{ var x: int := 0; var $x_0: int := x; x := 1; var t: int := { x }; var y: int := { t + 1 }; assert y == 2 };
-/
#guard_msgs in
#eval! do
  let program ← parseLaurelAndLift blockStmtLiftingProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

end Laurel
