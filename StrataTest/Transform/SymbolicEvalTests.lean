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
  match typeCheckAndBuildObligationProgram .quiet (translateCore p) with
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
procedure test(x : int)
spec { requires [pre]: x >= 0; }
{
  assert [a]: x >= 0;
};
#end

/--
info: program Core;

procedure test ()
{
  assume [pre]: x@1 >= 0;
  assert [a]: x@1 >= 0;
  };
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint simpleProg

/-! Deterministic if: condition becomes an assume on each branch -/

private def detIfProg :=
#strata
program Core;
procedure detIfTest(x : int)
spec { requires [pre]: x >= 0; }
{
  if (x > 5) {
    assert [big]: x > 5;
  } else {
    assert [small]: x <= 5;
  }
};
#end

/--
info: program Core;

procedure detIfTest ()
{
  if * {
    assume [|<label_ite_cond_true: x > 5>|]: x@1 > 5;
    assume [pre]: x@1 >= 0;
    assert [big]: x@1 > 5;
  } else {
    assume [|<label_ite_cond_false: !(x > 5)>|]: if x@1 > 5 then false else true;
    assume [pre]: x@1 >= 0;
    assert [small]: x@1 <= 5;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint detIfProg

/-! Nondeterministic if: each branch gets its own obligation path -/

private def nondetIfProg :=
#strata
program Core;
procedure nondetIfTest(x : int, out r : int)
spec {
  requires [pre]: x >= 0;
  ensures [post]: r >= 0;
}
{
  if * {
    r := x;
  } else {
    r := x + 1;
  }
};
#end

/--
info: program Core;

procedure nondetIfTest ()
{
  assume [pre]: x@1 >= 0;
  assume [|<label_ite_cond_true: $__nondet_cond_2>|]: if $__nondet_cond_2 then $__nondet_cond_2 else true;
  assume [|<label_ite_cond_false: !($__nondet_cond_2)>|]: if if $__nondet_cond_2 then false else true then if $__nondet_cond_2 then false else true else true;
  assert [post]: if $__nondet_cond_2 then x@1 else x@1 + 1 >= 0;
};
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint nondetIfProg

/-! Block exit: exit jumps to the end of the named block -/

private def blockExitProg :=
#strata
program Core;
procedure blockExitTest(x : int)
spec { requires [pre]: x >= 0; }
{
  outer: {
    if (x > 10) {
      assert [big]: x > 10;
      exit outer;
    }
    assert [small]: x <= 10;
  }
};
#end

/--
info: program Core;

procedure blockExitTest ()
{
  if * {
    assume [|<label_ite_cond_true: x > 10>|]: x@1 > 10;
    assume [pre]: x@1 >= 0;
    assert [big]: x@1 > 10;
  } else {
    assume [|<label_ite_cond_false: !(x > 10)>|]: if x@1 > 10 then false else true;
    assume [pre]: x@1 >= 0;
    assert [small]: x@1 <= 10;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint blockExitProg

/-! Combined: block exit + if + nondet (comprehensive) -/

private def blockExitIfProg :=
#strata
program Core;
procedure blockTest(x : int, y : int, out r : int)
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

procedure blockTest ()
{
  if * {
    if * {
      if * {
        if * {
          if * {
            assume [|<label_ite_cond_true: x > 10>|]: x@1 > 10;
            assume [pre_x]: x@1 >= 0;
            assume [pre_y]: y@1 >= 0;
            assert [big_x]: x@1 > 10;
          } else {
            assume [|<label_ite_cond_true: x > 10>|]: x@1 > 10;
            assume [pre_x]: x@1 >= 0;
            assume [pre_y]: y@1 >= 0;
            assert [final]: x@1 >= 0;
          }
        } else {
          assume [|<label_ite_cond_true: x > 10>|]: x@1 > 10;
          assume [pre_x]: x@1 >= 0;
          assume [pre_y]: y@1 >= 0;
          assert [post]: x@1 >= 0;
        }
      } else {
        assume [|<label_ite_cond_false: !(x > 10)>|]: if x@1 > 10 then false else true;
        assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__nondet_cond_3 then $__nondet_cond_3 else true;
        assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__nondet_cond_3 then false else true then if $__nondet_cond_3 then false else true else true;
        assume [pre_x]: x@1 >= 0;
        assume [pre_y]: y@1 >= 0;
        assert [after_inner]: if $__nondet_cond_3 then y@1 else x@1 + y@1 >= 0;
      }
    } else {
      assume [|<label_ite_cond_false: !(x > 10)>|]: if x@1 > 10 then false else true;
      assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__nondet_cond_3 then $__nondet_cond_3 else true;
      assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__nondet_cond_3 then false else true then if $__nondet_cond_3 then false else true else true;
      assume [pre_x]: x@1 >= 0;
      assume [pre_y]: y@1 >= 0;
      assert [final]: if $__nondet_cond_3 then y@1 else x@1 + y@1 >= 0;
    }
  } else {
    assume [|<label_ite_cond_false: !(x > 10)>|]: if x@1 > 10 then false else true;
    assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__nondet_cond_3 then $__nondet_cond_3 else true;
    assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__nondet_cond_3 then false else true then if $__nondet_cond_3 then false else true else true;
    assume [pre_x]: x@1 >= 0;
    assume [pre_y]: y@1 >= 0;
    assert [post]: if $__nondet_cond_3 then y@1 else x@1 + y@1 >= 0;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint blockExitIfProg

end Core.SymbolicEval.Tests
