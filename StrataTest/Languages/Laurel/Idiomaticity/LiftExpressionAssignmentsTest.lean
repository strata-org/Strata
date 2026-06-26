/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the expression lifter (`liftExpressionAssignments`) correctly:
- handles statement constructs (heap-updating assignments) in non-last
  positions of block expressions, and
- hoists imperative procedure calls out of assert/assume conditions, while
  leaving assignments untouched (so they are rejected downstream),
by comparing the lifted Laurel against expected output.

The lifter takes a list of "root" names (procedures known to be impure /
multi-output) that drive which calls get hoisted; both `[]` and a populated
list are exercised below.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.LaurelToCoreSchemaPass
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseLaurelAndLift (roots : List String) (program : StrataDDM.Program) : IO Program := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  pure (liftExpressionAssignments result.program result.model roots)

private def printLifted (roots : List String) (program : StrataDDM.Program) : IO Unit := do
  let lifted ← parseLaurelAndLift roots program
  for proc in lifted.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Heap-updating assignments in non-last positions of a block expression -/

/--
info: procedure assertInBlockExpr()
  opaque
{
  var x: int := 0;
  assert x == 0;
  var $x_0: int := x;
  x := 1;
  var y: int := {
    x
  };
  assert y == 1
};
-/
#guard_msgs in
#eval! printLifted []
#strata
program Laurel;
procedure assertInBlockExpr()
opaque {
  var x: int := 0;
  var y: int := { assert x == 0; x := 1; x };
  assert y == 1
};
#end

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
#eval! printLifted ["impure", "multi_out"]
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
#eval! printLifted ["impure", "multi_out"]
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
#eval! printLifted ["impure", "multi_out"]
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
#eval! printLifted ["impure", "multi_out"]
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
