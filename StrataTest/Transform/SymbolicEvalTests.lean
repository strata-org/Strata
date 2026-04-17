/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.SimpleAPI

/-! ## Symbolic evaluation phase tests -/

namespace Core.SymbolicEval.Tests

open Strata

private def translateCore (p : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-! The symbolic evaluation phase converts a program's procedures into
    obligation trees (assume/assert blocks combined with if *). -/

private def simpleProg :=
#strata
program Core;
procedure test(x : int) returns ()
spec { requires [pre]: x >= 0; }
{
  assert [a]: x >= 0;
};
#end

/--
info: program Core;

procedure obligations () returns ()
{
  assume [pre]: $__x0 >= 0;
  assert [a]: $__x0 >= 0;
  };
-/
#guard_msgs in
#eval do
  match typeCheckAndEval .quiet (translateCore simpleProg) with
  | .ok (oblProg, _) => IO.println (toString oblProg)
  | .error e => IO.println s!"Error: {e}"

/-! Comprehensive test: blocks, exits, while loops, if statements, nesting.
    Uses the full pipeline (transforms + symbolic eval) to handle loops. -/

private def comprehensiveProg :=
#strata
program Core;
procedure comprehensive(x : int, y : int) returns (r : int)
spec {
  requires [pre_x]: x >= 0;
  requires [pre_y]: y > 0;
  ensures [post]: r >= 0;
}
{
  var sum : int := 0;
  while (sum < x)
    invariant sum >= 0
    invariant sum <= x
  {
    sum := sum + 1;
  }
  result: {
    if (y > 10) {
      r := sum + y;
      assert [big_y]: r > 10;
      exit result;
    }
    r := sum;
  }
  assert [final]: r >= 0;
};
#end

/--
info: program Core;

procedure obligations () returns ()
{
  if * {
    if * {
      if * {
        if * {
          if * {
            if * {
              if * {
                if * {
                  assume [pre_x]: $__x0 >= 0;
                  assume [pre_y]: $__y1 > 0;
                  assert [entry_invariant_0_0]: true;
                  } else {
                  assume [pre_x]: $__x0 >= 0;
                  assume [pre_y]: $__y1 > 0;
                  assert [entry_invariant_0_1]: 0 <= $__x0;
                  }
                } else {
                assume [|<label_ite_cond_true: (~Int.Lt sum x)>|]: 0 < $__x0;
                assume [assume_guard_0]: $__sum3 < $__x0;
                assume [assume_invariant_0_0]: $__sum3 >= 0;
                assume [assume_invariant_0_1]: $__sum3 <= $__x0;
                assume [pre_x]: $__x0 >= 0;
                assume [pre_y]: $__y1 > 0;
                assume [assume_entry_invariant_0_1]: 0 <= $__x0;
                assert [arbitrary_iter_maintain_invariant_0_0]: $__sum3 + 1 >= 0;
                }
              } else {
              assume [|<label_ite_cond_true: (~Int.Lt sum x)>|]: 0 < $__x0;
              assume [assume_guard_0]: $__sum3 < $__x0;
              assume [assume_invariant_0_0]: $__sum3 >= 0;
              assume [assume_invariant_0_1]: $__sum3 <= $__x0;
              assume [pre_x]: $__x0 >= 0;
              assume [pre_y]: $__y1 > 0;
              assume [assume_entry_invariant_0_1]: 0 <= $__x0;
              assert [arbitrary_iter_maintain_invariant_0_1]: $__sum3 + 1 <= $__x0;
              }
            } else {
            assume [|<label_ite_cond_true: (~Int.Gt y #10)>|]: $__y1 > 10;
            assume [pre_x]: $__x0 >= 0;
            assume [pre_y]: $__y1 > 0;
            assume [assume_entry_invariant_0_1]: 0 <= $__x0;
            assume [|<label_ite_cond_true: (~Int.Lt sum x)>|]: if 0 < $__x0 then 0 < $__x0 else true;
            assume [assume_guard_0]: if 0 < $__x0 then $__sum3 < $__x0 else true;
            assume [assume_invariant_0_0]: if 0 < $__x0 then $__sum3 >= 0 else true;
            assume [assume_invariant_0_1]: if 0 < $__x0 then $__sum3 <= $__x0 else true;
            assume [not_guard_0]: if 0 < $__x0 then !($__sum4 < $__x0) else true;
            assume [invariant_0_0]: if 0 < $__x0 then $__sum4 >= 0 else true;
            assume [invariant_0_1]: if 0 < $__x0 then $__sum4 <= $__x0 else true;
            assume [|<label_ite_cond_false: !(~Int.Lt sum x)>|]: if if 0 < $__x0 then false else true then if 0 < $__x0 then false else true else true;
            assert [big_y]: if 0 < $__x0 then $__sum4 else 0 + $__y1 > 10;
            }
          } else {
          assume [|<label_ite_cond_true: (~Int.Gt y #10)>|]: $__y1 > 10;
          assume [pre_x]: $__x0 >= 0;
          assume [pre_y]: $__y1 > 0;
          assume [assume_entry_invariant_0_1]: 0 <= $__x0;
          assume [|<label_ite_cond_true: (~Int.Lt sum x)>|]: if 0 < $__x0 then 0 < $__x0 else true;
          assume [assume_guard_0]: if 0 < $__x0 then $__sum3 < $__x0 else true;
          assume [assume_invariant_0_0]: if 0 < $__x0 then $__sum3 >= 0 else true;
          assume [assume_invariant_0_1]: if 0 < $__x0 then $__sum3 <= $__x0 else true;
          assume [not_guard_0]: if 0 < $__x0 then !($__sum4 < $__x0) else true;
          assume [invariant_0_0]: if 0 < $__x0 then $__sum4 >= 0 else true;
          assume [invariant_0_1]: if 0 < $__x0 then $__sum4 <= $__x0 else true;
          assume [|<label_ite_cond_false: !(~Int.Lt sum x)>|]: if if 0 < $__x0 then false else true then if 0 < $__x0 then false else true else true;
          assert [final]: if 0 < $__x0 then $__sum4 else 0 + $__y1 >= 0;
          }
        } else {
        assume [|<label_ite_cond_true: (~Int.Gt y #10)>|]: $__y1 > 10;
        assume [pre_x]: $__x0 >= 0;
        assume [pre_y]: $__y1 > 0;
        assume [assume_entry_invariant_0_1]: 0 <= $__x0;
        assume [|<label_ite_cond_true: (~Int.Lt sum x)>|]: if 0 < $__x0 then 0 < $__x0 else true;
        assume [assume_guard_0]: if 0 < $__x0 then $__sum3 < $__x0 else true;
        assume [assume_invariant_0_0]: if 0 < $__x0 then $__sum3 >= 0 else true;
        assume [assume_invariant_0_1]: if 0 < $__x0 then $__sum3 <= $__x0 else true;
        assume [not_guard_0]: if 0 < $__x0 then !($__sum4 < $__x0) else true;
        assume [invariant_0_0]: if 0 < $__x0 then $__sum4 >= 0 else true;
        assume [invariant_0_1]: if 0 < $__x0 then $__sum4 <= $__x0 else true;
        assume [|<label_ite_cond_false: !(~Int.Lt sum x)>|]: if if 0 < $__x0 then false else true then if 0 < $__x0 then false else true else true;
        assert [post]: if 0 < $__x0 then $__sum4 else 0 + $__y1 >= 0;
        }
      } else {
      assume [|<label_ite_cond_false: !(~Int.Gt y #10)>|]: if $__y1 > 10 then false else true;
      assume [pre_x]: $__x0 >= 0;
      assume [pre_y]: $__y1 > 0;
      assume [assume_entry_invariant_0_1]: 0 <= $__x0;
      assume [|<label_ite_cond_true: (~Int.Lt sum x)>|]: if 0 < $__x0 then 0 < $__x0 else true;
      assume [assume_guard_0]: if 0 < $__x0 then $__sum3 < $__x0 else true;
      assume [assume_invariant_0_0]: if 0 < $__x0 then $__sum3 >= 0 else true;
      assume [assume_invariant_0_1]: if 0 < $__x0 then $__sum3 <= $__x0 else true;
      assume [not_guard_0]: if 0 < $__x0 then !($__sum4 < $__x0) else true;
      assume [invariant_0_0]: if 0 < $__x0 then $__sum4 >= 0 else true;
      assume [invariant_0_1]: if 0 < $__x0 then $__sum4 <= $__x0 else true;
      assume [|<label_ite_cond_false: !(~Int.Lt sum x)>|]: if if 0 < $__x0 then false else true then if 0 < $__x0 then false else true else true;
      assert [final]: if 0 < $__x0 then $__sum4 else 0 >= 0;
      }
    } else {
    assume [|<label_ite_cond_false: !(~Int.Gt y #10)>|]: if $__y1 > 10 then false else true;
    assume [pre_x]: $__x0 >= 0;
    assume [pre_y]: $__y1 > 0;
    assume [assume_entry_invariant_0_1]: 0 <= $__x0;
    assume [|<label_ite_cond_true: (~Int.Lt sum x)>|]: if 0 < $__x0 then 0 < $__x0 else true;
    assume [assume_guard_0]: if 0 < $__x0 then $__sum3 < $__x0 else true;
    assume [assume_invariant_0_0]: if 0 < $__x0 then $__sum3 >= 0 else true;
    assume [assume_invariant_0_1]: if 0 < $__x0 then $__sum3 <= $__x0 else true;
    assume [not_guard_0]: if 0 < $__x0 then !($__sum4 < $__x0) else true;
    assume [invariant_0_0]: if 0 < $__x0 then $__sum4 >= 0 else true;
    assume [invariant_0_1]: if 0 < $__x0 then $__sum4 <= $__x0 else true;
    assume [|<label_ite_cond_false: !(~Int.Lt sum x)>|]: if if 0 < $__x0 then false else true then if 0 < $__x0 then false else true else true;
    assert [post]: if 0 < $__x0 then $__sum4 else 0 >= 0;
    }
  };
-/
#guard_msgs in
#eval do
  let tcProg ← match Core.typeCheck .quiet (translateCore comprehensiveProg) with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"{e}")
  let transformed ← match Core.runTransforms tcProg [.callElim, .loopElim] with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"{e}")
  match Core.symbolicEval .quiet transformed with
  | .ok (oblProg, _) => IO.println (toString oblProg)
  | .error e => throw (IO.userError s!"{e}")

end Core.SymbolicEval.Tests
