/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the expression lifter correctly hoists imperative procedure calls
out of assert and assume conditions, while leaving assignments untouched
(so they are rejected downstream).
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.LaurelToCoreSchemaPass
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseLaurelAndLift (program : StrataDDM.Program) : IO Program := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  pure (liftExpressionAssignments result.program result.model ["impure", "multi_out"])

private def printLifted (program : StrataDDM.Program) : IO Unit := do
  let lifted ← parseLaurelAndLift program
  for proc in lifted.staticProcedures do
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
  var $cndtn_0: int := impure();
  assert $cndtn_0 == 1
};
-/
#guard_msgs in
#eval! printLifted
#strata
program Laurel;
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
};
procedure test() {
  assert impure() == 1
};
#end

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
#eval! printLifted
#strata
program Laurel;
procedure test() {
  var x: int := 0;
  assert (x := 2) == 2
};
#end

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
  var $cndtn_0: int := impure();
  assume $cndtn_0 == 1
};
-/
#guard_msgs in
#eval! printLifted
#strata
program Laurel;
procedure impure(): int {
  var x: int := 0;
  x := x + 1;
  x
};
procedure test() {
  assume impure() == 1
};
#end

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
  var $cndtn_0: BUG_MultiValuedExpr := multi_out(5);
  assert $cndtn_0 == 6
};
-/
#guard_msgs in
#eval! printLifted
#strata
program Laurel;
procedure multi_out(x: int) returns (r: int, extra: int) {
  r := x + 1;
  extra := x + 2
};
procedure test() {
  assert multi_out(5) == 6
};
#end

end Laurel
