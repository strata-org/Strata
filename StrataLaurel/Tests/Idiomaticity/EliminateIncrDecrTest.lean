/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Idiomaticity test for `EliminateIncrDecrAndCompoundAssign`, focusing on the
increment/decrement operators (`++x`, `x++`, `--x`, `x--`). Prefix yields the new
value, postfix the old; in expression position each lowers to a block expression
(later hoisted by `LiftImperativeExpressions`, whose idiomaticity is in
`LiftExpressionAssignmentsTest`; this test pins only THIS pass's output).

Uses the shared idiomaticity driver `runPassForIdiomaticity`.
-/

import StrataLaurel.Tests.Util.TestLaurel

open Strata
open StrataTest.Util

namespace Strata.Laurel

/- Statement form: `x++` and `--x` as statements. -/
/--
info: procedure stmtForm()
  opaque
{
  var x: int := 0;
  (x := x + 1) - 1;
  x := x - 1
};
-/
#guard_msgs in
#eval runPassForIdiomaticity eliminateIncrDecrAndCompoundAssignPass <|
#strata
program Laurel;
procedure stmtForm()
  opaque
{
  var x: int := 0;
  x++;
  --x
};
#end

/- Prefix form in expression position: yields the new value. -/
/--
info: procedure preIncrExpr()
  opaque
{
  var x: int := 0;
  var y: int := (x := x + 1) + (x := x + 1);
  assert x == 2;
  assert y == 3
};
-/
#guard_msgs in
#eval runPassForIdiomaticity eliminateIncrDecrAndCompoundAssignPass <|
#strata
program Laurel;
procedure preIncrExpr()
  opaque
{
  var x: int := 0;
  var y: int := ++x + ++x;
  assert x == 2;
  assert y == 3
};
#end

/- Postfix form in expression position: yields the OLD value. -/
/--
info: procedure postIncrExpr()
  opaque
{
  var x: int := 0;
  var y: int := (x := x + 1) - 1 + ((x := x + 1) - 1);
  assert x == 2;
  assert y == 1
};
-/
#guard_msgs in
#eval runPassForIdiomaticity eliminateIncrDecrAndCompoundAssignPass <|
#strata
program Laurel;
procedure postIncrExpr()
  opaque
{
  var x: int := 0;
  var y: int := x++ + x++;
  assert x == 2;
  assert y == 1
};
#end

end Laurel
