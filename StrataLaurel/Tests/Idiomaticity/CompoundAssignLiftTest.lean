/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Idiomaticity test for `EliminateIncrDecrAndCompoundAssign`, the pass that lowers
C-style compound assignment (`+=`, `-=`, `^=`, …). `x op= e` lowers to
`x := x op e`; in expression position it lowers to a block expression yielding the
new value (that block is later hoisted by `LiftImperativeExpressions`, whose own
idiomaticity is in `LiftExpressionAssignmentsTest`; this test pins only THIS
pass's output).

Uses the shared idiomaticity driver `runPassForIdiomaticity`: parse, resolve,
run the one pass, print the result.
-/

import StrataLaurel.Tests.Util.TestLaurel

open Strata
open StrataTest.Util

namespace Strata.Laurel

/- Statement form: `x += 3` lowers to a clean `x := x + 3`. -/
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
#eval runPassForIdiomaticity eliminateIncrDecrAndCompoundAssignPass <|
#strata
program Laurel;
procedure stmtForm()
  opaque
{
  var x: int := 0;
  x += 3;
  x -= 1
};
#end

/- Expression position: `(x += 2)` lowers to a block expression that performs the
    assignment and yields the new value. (`LiftImperativeExpressions` later hoists
    the block ahead of the use; that is not this pass.) -/
/--
info: procedure exprForm()
  opaque
{
  var x: int := 5;
  var y: int := x := x + 2;
  assert x == 7;
  assert y == 7
};
-/
#guard_msgs in
#eval runPassForIdiomaticity eliminateIncrDecrAndCompoundAssignPass <|
#strata
program Laurel;
procedure exprForm()
  opaque
{
  var x: int := 5;
  var y: int := (x += 2);
  assert x == 7;
  assert y == 7
};
#end

/- Nested side-effecting RHS: `x += (y += 1)` lowers bottom-up, each compound
    assignment becoming its own block expression. -/
/--
info: procedure nestedRhs()
  opaque
{
  var x: int := 1;
  var y: int := 10;
  x := x + (y := y + 1);
  assert y == 11;
  assert x == 12
};
-/
#guard_msgs in
#eval runPassForIdiomaticity eliminateIncrDecrAndCompoundAssignPass <|
#strata
program Laurel;
procedure nestedRhs()
  opaque
{
  var x: int := 1;
  var y: int := 10;
  x += (y += 1);
  assert y == 11;
  assert x == 12
};
#end

/- String concatenation `^=` maps to the distinct `.StrConcat` operation (on
    `string`, not arithmetic on `int`): `s ^= "b"` lowers to `s := s ^ "b"`. -/
/--
info: procedure strConcatForm()
  opaque
{
  var s: string := "a";
  s := s ^ "b"
};
-/
#guard_msgs in
#eval runPassForIdiomaticity eliminateIncrDecrAndCompoundAssignPass <|
#strata
program Laurel;
procedure strConcatForm()
  opaque
{
  var s: string := "a";
  s ^= "b"
};
#end

end Laurel
