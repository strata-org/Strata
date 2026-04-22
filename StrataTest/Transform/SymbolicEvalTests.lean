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
  assume [pre]: $__x0 >= 0;
  assert [a]: $__x0 >= 0;
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
    assume [|<label_ite_cond_true: x > 5>|]: $__x0 > 5;
    assume [pre]: $__x0 >= 0;
    assert [big]: $__x0 > 5;
  } else {
    assume [|<label_ite_cond_false: !(x > 5)>|]: if $__x0 > 5 then false else true;
    assume [pre]: $__x0 >= 0;
    assert [small]: $__x0 <= 5;
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
  assume [pre]: $__x0 >= 0;
  assume [|<label_ite_cond_true: $__nondet_cond_2>|]: if $__$__nondet_cond_22 then $__$__nondet_cond_22 else true;
  assume [|<label_ite_cond_false: !($__nondet_cond_2)>|]: if if $__$__nondet_cond_22 then false else true then if $__$__nondet_cond_22 then false else true else true;
  assert [post]: if $__$__nondet_cond_22 then $__x0 else $__x0 + 1 >= 0;
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
    assume [|<label_ite_cond_true: x > 10>|]: $__x0 > 10;
    assume [pre]: $__x0 >= 0;
    assert [big]: $__x0 > 10;
  } else {
    assume [|<label_ite_cond_false: !(x > 10)>|]: if $__x0 > 10 then false else true;
    assume [pre]: $__x0 >= 0;
    assert [small]: $__x0 <= 10;
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
            assume [|<label_ite_cond_true: x > 10>|]: $__x0 > 10;
            assume [pre_x]: $__x0 >= 0;
            assume [pre_y]: $__y1 >= 0;
            assert [big_x]: $__x0 > 10;
          } else {
            assume [|<label_ite_cond_true: x > 10>|]: $__x0 > 10;
            assume [pre_x]: $__x0 >= 0;
            assume [pre_y]: $__y1 >= 0;
            assert [final]: $__x0 >= 0;
          }
        } else {
          assume [|<label_ite_cond_true: x > 10>|]: $__x0 > 10;
          assume [pre_x]: $__x0 >= 0;
          assume [pre_y]: $__y1 >= 0;
          assert [post]: $__x0 >= 0;
        }
      } else {
        assume [|<label_ite_cond_false: !(x > 10)>|]: if $__x0 > 10 then false else true;
        assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__$__nondet_cond_33 then $__$__nondet_cond_33 else true;
        assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__$__nondet_cond_33 then false else true then if $__$__nondet_cond_33 then false else true else true;
        assume [pre_x]: $__x0 >= 0;
        assume [pre_y]: $__y1 >= 0;
        assert [after_inner]: if $__$__nondet_cond_33 then $__y1 else $__x0 + $__y1 >= 0;
      }
    } else {
      assume [|<label_ite_cond_false: !(x > 10)>|]: if $__x0 > 10 then false else true;
      assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__$__nondet_cond_33 then $__$__nondet_cond_33 else true;
      assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__$__nondet_cond_33 then false else true then if $__$__nondet_cond_33 then false else true else true;
      assume [pre_x]: $__x0 >= 0;
      assume [pre_y]: $__y1 >= 0;
      assert [final]: if $__$__nondet_cond_33 then $__y1 else $__x0 + $__y1 >= 0;
    }
  } else {
    assume [|<label_ite_cond_false: !(x > 10)>|]: if $__x0 > 10 then false else true;
    assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__$__nondet_cond_33 then $__$__nondet_cond_33 else true;
    assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__$__nondet_cond_33 then false else true then if $__$__nondet_cond_33 then false else true else true;
    assume [pre_x]: $__x0 >= 0;
    assume [pre_y]: $__y1 >= 0;
    assert [post]: if $__$__nondet_cond_33 then $__y1 else $__x0 + $__y1 >= 0;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint blockExitIfProg

end Core.SymbolicEval.Tests
