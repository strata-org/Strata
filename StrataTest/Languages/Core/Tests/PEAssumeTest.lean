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

/-! ## PE handles exit statements inside nondet ITE by producing multiple paths -/

private def peExitDupProg :=
#strata
program Core;
procedure test(x : int, y : int, z : int) returns ()
spec {
  requires [pre_x]: x >= 0;
  requires [pre_y]: y >= 0;
  requires [pre_z]: z >= 0;
}
{
  assert [a]: x >= 0;
  some_block: {
    if * {
      assert [b]: y >= 0;
      exit some_block;
    } else {
      assert [c]: z >= 0;
    }
  }
  assert [d]: x + y + z >= 0;
};
#end

-- PE output: the exit causes two PE paths combined via `if *`.
-- Path 1 (exit taken): a, b, d.
-- Path 2 (fall-through): a, c, d.
/--
info: program Core;

procedure test (x : int, y : int, z : int) returns ()
spec {
  requires [pre_x]: x >= 0;
  requires [pre_y]: y >= 0;
  requires [pre_z]: z >= 0;
  } {
  if * {
    assume [pre_x]: $__x0 >= 0;
    assume [pre_y]: $__y1 >= 0;
    assume [pre_z]: $__z2 >= 0;
    assert [a]: $__x0 >= 0;
    some_block: {
      var $__nondet_cond_2 : bool;
      if (true) {
        assume [|<label_ite_cond_true: $__nondet_cond_2>|]: $__$__nondet_cond_23;
        assert [b]: $__y1 >= 0;
        exit some_block;
        }
      }
    assert [d]: $__x0 + $__y1 + $__z2 >= 0;
    } else {
    assume [pre_x]: $__x0 >= 0;
    assume [pre_y]: $__y1 >= 0;
    assume [pre_z]: $__z2 >= 0;
    assert [a]: $__x0 >= 0;
    some_block: {
      var $__nondet_cond_2 : bool;
      if (false) {
        } else {
        assume [|<label_ite_cond_false: !$__nondet_cond_2>|]: if $__$__nondet_cond_23 then false else true;
        assert [c]: $__z2 >= 0;
        }
      }
    assert [d]: $__x0 + $__y1 + $__z2 >= 0;
    }
  };
-/
#guard_msgs in
#eval do
  match typeCheckAndPartialEval .quiet (translateCore peExitDupProg) with
  | .ok (pEs, _) =>
    let (p, _) := pEs.head!
    IO.println (toString p)
  | .error e => IO.println s!"Error: {e}"

end Core.PEAssume.Tests
