/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that the expression lifter correctly hoists imperative procedure calls
out of assert and assume conditions, while leaving assignments untouched
(so they are rejected downstream).
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

private def parseLaurelAndLift (input : String) : IO Program := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    pure (liftExpressionAssignments program model ["impure", "multi_out"])

private def printLifted (input : String) : IO Unit := do
  let program ← parseLaurelAndLift input
  for proc in program.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Imperative calls in assert are lifted -/

/--
info: procedure impure(): int
{
  var x: int := 0;
  x := x + 1;
  x
};
procedure test()
{
  var $cndtn_0: int;
  $cndtn_0 := impure();
  assert $cndtn_0 == 1
};
-/
#guard_msgs in
#eval! printLifted r"
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
};
procedure test() {
  assert impure() == 1
};
"

/-! ## Assignments in assert are NOT lifted (rejected downstream) -/

/--
info: procedure test()
{
  var x: int := 0;
  var $x_0: int := x;
  x := 2;
  assert x == 2
};
-/
#guard_msgs in
#eval! printLifted r"
procedure test() {
  var x: int := 0;
  assert (x := 2) == 2
};
"

/-! ## Imperative calls in assume are lifted -/

/--
info: procedure impure(): int
{
  var x: int := 0;
  x := x + 1;
  x
};
procedure test()
{
  var $cndtn_0: int;
  $cndtn_0 := impure();
  assume $cndtn_0 == 1
};
-/
#guard_msgs in
#eval! printLifted r"
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
};
procedure test() {
  assume impure() == 1
};
"

/-! ## Multi-output calls in expression position produce a single (broken) target.
    This is intentional — multi-output calls should not appear in expression position.
    Resolution should emit a diagnostic for this case. -/

/--
info: procedure multi_out(x: int)
  returns (r: int, extra: int)
{
  r := x + 1;
  extra := x + 2
};
procedure test()
{
  var $cndtn_0: BUG_MultiValuedExpr;
  $cndtn_0 := multi_out(5);
  assert $cndtn_0 == 6
};
-/
#guard_msgs in
#eval! printLifted r"
procedure multi_out(x: int) returns (r: int, extra: int) {
  r := x + 1;
  extra := x + 2
};
procedure test() {
  assert multi_out(5) == 6
};
"

end Laurel
end Strata
end
