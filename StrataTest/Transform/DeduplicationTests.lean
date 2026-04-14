/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.Deduplication
import Strata.Languages.Core.DDMTransform.Translate

namespace Core.Deduplication.Tests

open Strata Lambda Imperative Core.Deduplication

private def translateCore (p : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-! ## Deduplication across ITE branches and condition -/

private def iteDupProg :=
#strata
program Core;
procedure test(x : int, y : int) returns () {
  if (x + y > 0) {
    assert (x + y >= 1);
  } else {
    assert (x + y <= 0);
  }
};
#end

/--
info: program Core;

procedure test (x : int, y : int) returns ()
{
  var $__t.0 : int := x + y;
  if ($__t.0 > 0) {
    assert [assert_0]: $__t.0 >= 1;
    } else {
    assert [assert_1]: $__t.0 <= 0;
    }
  };
-/
#guard_msgs in
#eval IO.println (toString (deduplicateProgram (translateCore iteDupProg)))

/-! ## No duplicates leaves body unchanged -/

private def noDupProg :=
#strata
program Core;
procedure test(x : int, y : int) returns () {
  assume (x >= 5);
  assert (y <= 10);
};
#end

/--
info: program Core;

procedure test (x : int, y : int) returns ()
{
  assume [assume_0]: x >= 5;
  assert [assert_0]: y <= 10;
  };
-/
#guard_msgs in
#eval IO.println (toString (deduplicateProgram (translateCore noDupProg)))

end Core.Deduplication.Tests
