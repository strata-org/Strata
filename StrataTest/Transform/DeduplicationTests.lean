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

/-! ## Deduplication extracts common subexpressions -/

private def dupProg :=
#strata
program Core;
procedure test(x : int, y : int) returns () {
  assume (x + y >= 5);
  assert (x + y <= 10);
};
#end

/--
info: program Core;

procedure test (x : int, y : int) returns ()
{
  var $__t.0 : int := x + y;
  assume [assume_0]: $__t.0 >= 5;
  assert [assert_0]: $__t.0 <= 10;
  };
-/
#guard_msgs in
#eval IO.println (toString (deduplicateProgram (translateCore dupProg)))

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
