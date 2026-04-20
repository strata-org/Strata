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

private def evalAndPrint (p : Strata.Program) : IO Unit := do
  match typeCheckAndEval .quiet (translateCore p) with
  | .ok (oblProg, _) =>
    let s := (Core.formatProgram oblProg).pretty
    -- Strip trailing newlines from program output
    let s := s.toList.reverse.dropWhile (· == '\n') |>.reverse |> String.ofList
    IO.print s
  | .error e => IO.println s!"Error: {e}"

/-! Simple test: procedure name preserved, preconditions become assumes -/

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

procedure test () returns ()
{
  assume [pre]: $__x0 >= 0;
  assert [a]: $__x0 >= 0;
  };
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint simpleProg

/-! Comprehensive test: labelled blocks, exit statements, deterministic and
    non-deterministic if statements. No loops or procedure calls. -/

private def blockExitIfProg :=
#strata
program Core;
procedure blockTest(x : int, y : int) returns (r : int)
spec {
  requires [pre_x]: x >= 0;
  requires [pre_y]: y >= 0;
  ensures [post]: r >= 0;
}
{
  outer: {
    if (x > 10) {
      r := x;
      assert [big_x]: r > 10;
      exit outer;
    }
    inner: {
      if * {
        r := y;
      } else {
        r := x + y;
      }
    }
    assert [after_inner]: r >= 0;
  }
  assert [final]: r >= 0;
};
#end

/--
info: program Core;

procedure blockTest () returns ()
{
  if * {
    if * {
      if * {
        if * {
          if * {
            assume [|<label_ite_cond_true: (~Int.Gt x #10)>|]: $__x0 > 10;
            assume [pre_x]: $__x0 >= 0;
            assume [pre_y]: $__y1 >= 0;
            assert [big_x]: $__x0 > 10;
            } else {
            assume [|<label_ite_cond_true: (~Int.Gt x #10)>|]: $__x0 > 10;
            assume [pre_x]: $__x0 >= 0;
            assume [pre_y]: $__y1 >= 0;
            assert [final]: $__x0 >= 0;
            }
          } else {
          assume [|<label_ite_cond_true: (~Int.Gt x #10)>|]: $__x0 > 10;
          assume [pre_x]: $__x0 >= 0;
          assume [pre_y]: $__y1 >= 0;
          assert [post]: $__x0 >= 0;
          }
        } else {
        assume [|<label_ite_cond_false: !(~Int.Gt x #10)>|]: if $__x0 > 10 then false else true;
        assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__$__nondet_cond_33 then $__$__nondet_cond_33 else true;
        assume [|<label_ite_cond_false: !$__nondet_cond_3>|]: if if $__$__nondet_cond_33 then false else true then if $__$__nondet_cond_33 then false else true else true;
        assume [pre_x]: $__x0 >= 0;
        assume [pre_y]: $__y1 >= 0;
        assert [after_inner]: if $__$__nondet_cond_33 then $__y1 else $__x0 + $__y1 >= 0;
        }
      } else {
      assume [|<label_ite_cond_false: !(~Int.Gt x #10)>|]: if $__x0 > 10 then false else true;
      assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__$__nondet_cond_33 then $__$__nondet_cond_33 else true;
      assume [|<label_ite_cond_false: !$__nondet_cond_3>|]: if if $__$__nondet_cond_33 then false else true then if $__$__nondet_cond_33 then false else true else true;
      assume [pre_x]: $__x0 >= 0;
      assume [pre_y]: $__y1 >= 0;
      assert [final]: if $__$__nondet_cond_33 then $__y1 else $__x0 + $__y1 >= 0;
      }
    } else {
    assume [|<label_ite_cond_false: !(~Int.Gt x #10)>|]: if $__x0 > 10 then false else true;
    assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__$__nondet_cond_33 then $__$__nondet_cond_33 else true;
    assume [|<label_ite_cond_false: !$__nondet_cond_3>|]: if if $__$__nondet_cond_33 then false else true then if $__$__nondet_cond_33 then false else true else true;
    assume [pre_x]: $__x0 >= 0;
    assume [pre_y]: $__y1 >= 0;
    assert [post]: if $__$__nondet_cond_33 then $__y1 else $__x0 + $__y1 >= 0;
    }
  };
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint blockExitIfProg

end Core.SymbolicEval.Tests
