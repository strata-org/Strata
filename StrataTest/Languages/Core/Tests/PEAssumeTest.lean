/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate

namespace Core.PEAssume.Tests

open Strata

private def translateCore (p : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-! ## PE emits assume statements inside ITE branches for path condition reconstruction -/

private def peAssumeProg :=
#strata
program Core;
procedure test(z : bool) returns () {
  var x : int := 0;
  var y : int := 6;
  if (z) {
    x := y;
    assert [then_check]: (x == y);
  } else {
    assert [else_check]: (x == 0);
  }
  assert [after_ite]: (x >= 0);
};
#end

/--
info: program Core;

procedure test (z : bool) returns ()
{
  var x : int := 0;
  var y : int := 6;
  if * {
    assume [|<label_ite_cond_true: z>|]: $__z0;
    x := 6;
    assert [then_check]: true;
    } else {
    assume [|<label_ite_cond_false: !z>|]: if $__z0 then false else true;
    assert [else_check]: true;
    }
  assert [after_ite]: if $__z0 then 6 else 0 >= 0;
  };
-/
#guard_msgs in
#eval do
  match typeCheckAndPartialEval .quiet (translateCore peAssumeProg) with
  | .ok (pEs, _) =>
    let (p, _) := pEs.head!
    IO.println (toString p)
  | .error e => IO.println s!"Error: {e}"

end Core.PEAssume.Tests
