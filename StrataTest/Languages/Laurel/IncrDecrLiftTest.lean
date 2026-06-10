/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that the EliminateIncrDecr + LiftImperativeExpressions pipeline correctly
lowers Java-style `++`/`--` operators in both prefix and postfix forms, in both
statement and expression positions, by comparing the lowered Laurel against
expected output.
-/

meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar
meta import Strata.Languages.Laurel.LaurelToCoreTranslator
meta import Strata.Languages.Laurel.EliminateIncrDecr
meta import Strata.Languages.Laurel.LiftImperativeExpressions

meta section

open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Run the parser, the EliminateIncrDecr pass, then LiftImperativeExpressions,
    so that test output reflects the Laurel form that is fed to Core. -/
def parseLowerIncrDecr (input : String) : IO Program := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    -- Step 1: eliminate IncrDecr
    let program := eliminateIncrDecr program
    -- Step 2: resolve so liftExpressionAssignments has a valid SemanticModel
    let result := resolve program
    let (program, model) := (result.program, result.model)
    pure (liftExpressionAssignments model program)

/-- Statement form: `x++;` and `--x` as statements. Prefix (`--x`) produces
    a clean assignment. Postfix (`x++`) emits the same assignment-based form as
    the expression position; the lift pass snapshots the pre-assignment value
    even though it is unused here. -/
def stmtFormProgram : String := r"
procedure stmtForm()
  opaque
{
  var x: int := 0;
  x++;
  --x
};
"

/--
info: procedure stmtForm()
  opaque
{
  var x: int := 0;
  var $x_0: int := x;
  x := x + 1;
  x := x - 1
};
-/
#guard_msgs in
#eval! do
  let program ← parseLowerIncrDecr stmtFormProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-- Prefix form in expression position: yields the new value. -/
def preIncrExprProgram : String := r"
procedure preIncrExpr()
  opaque
{
  var x: int := 0;
  var y: int := ++x + ++x;
  assert x == 2;
  assert y == 3
};
"

/--
info: procedure preIncrExpr()
  opaque
{
  var x: int := 0;
  var $x_1: int := x;
  x := x + 1;
  var $x_0: int := x;
  x := x + 1;
  var y: int := $x_0 + x;
  assert x == 2;
  assert y == 3
};
-/
#guard_msgs in
#eval! do
  let program ← parseLowerIncrDecr preIncrExprProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-- Postfix form in expression position: yields the OLD value. After the
    pipeline runs, the snapshot mechanism makes `(x++) + (x++)` evaluate to
    `0 + 1 = 1` while `x` ends up at 2 — matching Java semantics. -/
def postIncrExprProgram : String := r"
procedure postIncrExpr()
  opaque
{
  var x: int := 0;
  var y: int := x++ + x++;
  assert x == 2;
  assert y == 1
};
"

/--
info: procedure postIncrExpr()
  opaque
{
  var x: int := 0;
  var $x_1: int := x;
  x := x + 1;
  var $x_0: int := x;
  x := x + 1;
  var y: int := $x_0 - 1 + (x - 1);
  assert x == 2;
  assert y == 1
};
-/
#guard_msgs in
#eval! do
  let program ← parseLowerIncrDecr postIncrExprProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

end Laurel
end Strata
end
