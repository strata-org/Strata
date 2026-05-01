/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ANFEncoder
import Strata.Languages.Core.DDMTransform.Translate

namespace Core.ANFEncoder.Tests

open Strata Lambda Imperative Core.ANFEncoder

private def translateCore (p : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-! ## ANFEncoder across ITE branches and condition -/

private def iteDupProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  if (x + y > 0) {
    assert (x + y >= 1);
  } else {
    assert (x + y <= 0);
  }
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__anf.0 : int := x + y;
  if ($__anf.0 > 0) {
    assert [assert_0]: $__anf.0 >= 1;
  } else {
    assert [assert_1]: $__anf.0 <= 0;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (anfEncodeProgram (translateCore iteDupProg)).2)

/-! ## No duplicates leaves body unchanged -/

private def noDupProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assume (x >= 5);
  assert (y <= 10);
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  assume [assume_0]: x >= 5;
  assert [assert_0]: y <= 10;
};
-/
#guard_msgs in
#eval IO.println (toString (anfEncodeProgram (translateCore noDupProg)).2)

/-! ## Duplicate ITE expression is lifted -/

private def iteDupExprProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert ((if x > 0 then x else y) >= 0);
  assert ((if x > 0 then x else y) <= 100);
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__anf.0 : int := if x > 0 then x else y;
  assert [assert_0]: $__anf.0 >= 0;
  assert [assert_1]: $__anf.0 <= 100;
};
-/
#guard_msgs in
#eval IO.println (toString (anfEncodeProgram (translateCore iteDupExprProg)).2)

/-! ## Subexpressions within function calls are lifted when duplicated -/

private def fnCallDupArgProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert (x + y > 0);
  assert (x + y < 100);
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__anf.0 : int := x + y;
  assert [assert_0]: $__anf.0 > 0;
  assert [assert_1]: $__anf.0 < 100;
};
-/
#guard_msgs in
#eval IO.println (toString (anfEncodeProgram (translateCore fnCallDupArgProg)).2)

/-! ## Unique subexpressions are not lifted -/

private def uniqueSubexprProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert (x + 1 > 0);
  assert (y + 2 < 100);
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  assert [assert_0]: x + 1 > 0;
  assert [assert_1]: y + 2 < 100;
};
-/
#guard_msgs in
#eval IO.println (toString (anfEncodeProgram (translateCore uniqueSubexprProg)).2)

end Core.ANFEncoder.Tests
