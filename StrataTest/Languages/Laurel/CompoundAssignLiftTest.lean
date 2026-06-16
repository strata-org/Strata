/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that the EliminateIncrDecr + LiftImperativeExpressions pipeline correctly
lowers C-style compound assignment (`+=`, `-=`, …) by comparing the lowered
Laurel against expected output. `x op= e` lowers to `x := x op e`; in expression
position the assignment is lifted out and yields the new value.
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

/-- Parse, run EliminateIncrDecr (which also eliminates CompoundAssign), then
    LiftImperativeExpressions, so test output reflects the Laurel fed to Core. -/
def parseLowerCompoundAssign (input : String) : IO Program := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let program := eliminateIncrDecr program
    let result := resolve program
    let (program, model) := (result.program, result.model)
    pure (liftExpressionAssignments model program)

/-- Statement form: `x += 3` lowers to a clean `x := x + 3`. -/
def stmtFormProgram : String := r"
procedure stmtForm()
  opaque
{
  var x: int := 0;
  x += 3;
  x -= 1
};
"

/--
info: procedure stmtForm()
  opaque
{
  var x: int := 0;
  x := x + 3;
  x := x - 1
};
-/
#guard_msgs in
#eval! do
  let program ← parseLowerCompoundAssign stmtFormProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-- Expression position: `(x += 2)` yields the new value; the assignment is
    lifted out ahead of the use. -/
def exprFormProgram : String := r"
procedure exprForm()
  opaque
{
  var x: int := 5;
  var y: int := (x += 2);
  assert x == 7;
  assert y == 7
};
"

/--
info: procedure exprForm()
  opaque
{
  var x: int := 5;
  var $x_0: int := x;
  x := x + 2;
  var y: int := x;
  assert x == 7;
  assert y == 7
};
-/
#guard_msgs in
#eval! do
  let program ← parseLowerCompoundAssign exprFormProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-- Nested side-effecting RHS: `x += (y += 1)` lowers bottom-up. One level of
    nesting is supported. Deeper nesting (`x += (y += (z += 1))`) hits a
    pre-existing limitation of `LiftImperativeExpressions` — it errors with
    "destructive assignments … should have been lifted" — that also affects plain
    nested assignment (`x := (y := (z := 5))`) on the base, independent of compound
    assignment. Not exercised here so the test doesn't pin that broken output. -/
def nestedRhsProgram : String := r"
procedure nestedRhs()
  opaque
{
  var x: int := 1;
  var y: int := 10;
  x += (y += 1);
  assert y == 11;
  assert x == 12
};
"

/--
info: procedure nestedRhs()
  opaque
{
  var x: int := 1;
  var y: int := 10;
  var $y_0: int := y;
  y := y + 1;
  x := x + y;
  assert y == 11;
  assert x == 12
};
-/
#guard_msgs in
#eval! do
  let program ← parseLowerCompoundAssign nestedRhsProgram
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

end Laurel
end Strata
end
