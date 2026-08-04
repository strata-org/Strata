/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.SimpleAPI
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! ## Symbolic evaluation phase tests -/

namespace Core.SymbolicEval.Tests

open Strata

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

private def evalAndPrint (p : StrataDDM.Program) : IO Unit := do
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
spec { requires [pre]: int.ge(x, 0); }
{
  assert [a]: int.ge(x, 0);
};
#end

/--
info: program Core;

procedure test ()
{
  assume [pre]: int.ge(x@1, 0);
  assert [a]: int.ge(x@1, 0);
};
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint simpleProg

/-! Deterministic if: condition becomes an assume on each branch -/

private def detIfProg :=
#strata
program Core;
procedure detIfTest(x : int)
spec { requires [pre]: int.ge(x, 0); }
{
  if (int.gt(x, 5)) {
    assert [big]: int.gt(x, 5);
  } else {
    assert [small]: int.le(x, 5);
  }
};
#end

/--
info: program Core;

procedure detIfTest ()
{
  if * {
    assume [pre]: int.ge(x@1, 0);
    assume [|<label_ite_cond_true: int.gt(x, 5)>|]: int.gt(x@1, 5);
    assert [big]: int.gt(x@1, 5);
  } else {
    assume [pre]: int.ge(x@1, 0);
    assume [|<label_ite_cond_false: !(int.gt(x, 5))>|]: if int.gt(x@1, 5) then false else true;
    assert [small]: int.le(x@1, 5);
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
  requires [pre]: int.ge(x, 0);
  ensures [post]: int.ge(r, 0);
}
{
  if * {
    r := x;
  } else {
    r := int.add(x, 1);
  }
};
#end

/--
info: program Core;

procedure nondetIfTest ()
{
  assume [pre]: int.ge(x@1, 0);
  assume [|<label_ite_cond_true: $__nondet_cond_2>|]: if $__nondet_cond_2 then $__nondet_cond_2 else true;
  assume [|<label_ite_cond_false: !($__nondet_cond_2)>|]: if if $__nondet_cond_2 then false else true then if $__nondet_cond_2 then false else true else true;
  assert [post]: int.ge(if $__nondet_cond_2 then x@1 else int.add(x@1, 1), 0);
};
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint nondetIfProg

/-! Block exit: exit jumps to the end of the named block -/

private def blockExitProg :=
#strata
program Core;
procedure blockExitTest(x : int)
spec { requires [pre]: int.ge(x, 0); }
{
  outer: {
    if (int.gt(x, 10)) {
      assert [big]: int.gt(x, 10);
      exit outer;
    }
    assert [small]: int.le(x, 10);
  }
};
#end

/--
info: program Core;

procedure blockExitTest ()
{
  if * {
    assume [pre]: int.ge(x@1, 0);
    assume [|<label_ite_cond_true: int.gt(x, 10)>|]: int.gt(x@1, 10);
    assert [big]: int.gt(x@1, 10);
  } else {
    assume [pre]: int.ge(x@1, 0);
    assume [|<label_ite_cond_false: !(int.gt(x, 10))>|]: if int.gt(x@1, 10) then false else true;
    assert [small]: int.le(x@1, 10);
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
  requires [pre_x]: int.ge(x, 0);
  requires [pre_y]: int.ge(y, 0);
  ensures [post]: int.ge(r, 0);
}
{
  outer: {
    if (int.gt(x, 10)) {
      r := x;
      assert [big_x]: int.gt(r, 10);
      exit outer;
    }
    inner: {
      if * {
        r := y;
      } else {
        r := int.add(x, y);
      }
    }
    assert [after_inner]: int.ge(r, 0);
  }
  assert [final]: int.ge(r, 0);
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
            assume [pre_x]: int.ge(x@1, 0);
            assume [pre_y]: int.ge(y@1, 0);
            assume [|<label_ite_cond_true: int.gt(x, 10)>|]: int.gt(x@1, 10);
            assert [big_x]: int.gt(x@1, 10);
          } else {
            assume [pre_x]: int.ge(x@1, 0);
            assume [pre_y]: int.ge(y@1, 0);
            assume [|<label_ite_cond_true: int.gt(x, 10)>|]: int.gt(x@1, 10);
            assert [final]: int.ge(x@1, 0);
          }
        } else {
          assume [pre_x]: int.ge(x@1, 0);
          assume [pre_y]: int.ge(y@1, 0);
          assume [|<label_ite_cond_true: int.gt(x, 10)>|]: int.gt(x@1, 10);
          assert [post]: int.ge(x@1, 0);
        }
      } else {
        assume [pre_x]: int.ge(x@1, 0);
        assume [pre_y]: int.ge(y@1, 0);
        assume [|<label_ite_cond_false: !(int.gt(x, 10))>|]: if int.gt(x@1, 10) then false else true;
        assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__nondet_cond_3 then $__nondet_cond_3 else true;
        assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__nondet_cond_3 then false else true then if $__nondet_cond_3 then false else true else true;
        assert [after_inner]: int.ge(if $__nondet_cond_3 then y@1 else int.add(x@1, y@1), 0);
      }
    } else {
      assume [pre_x]: int.ge(x@1, 0);
      assume [pre_y]: int.ge(y@1, 0);
      assume [|<label_ite_cond_false: !(int.gt(x, 10))>|]: if int.gt(x@1, 10) then false else true;
      assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__nondet_cond_3 then $__nondet_cond_3 else true;
      assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__nondet_cond_3 then false else true then if $__nondet_cond_3 then false else true else true;
      assert [final]: int.ge(if $__nondet_cond_3 then y@1 else int.add(x@1, y@1), 0);
    }
  } else {
    assume [pre_x]: int.ge(x@1, 0);
    assume [pre_y]: int.ge(y@1, 0);
    assume [|<label_ite_cond_false: !(int.gt(x, 10))>|]: if int.gt(x@1, 10) then false else true;
    assume [|<label_ite_cond_true: $__nondet_cond_3>|]: if $__nondet_cond_3 then $__nondet_cond_3 else true;
    assume [|<label_ite_cond_false: !($__nondet_cond_3)>|]: if if $__nondet_cond_3 then false else true then if $__nondet_cond_3 then false else true else true;
    assert [post]: int.ge(if $__nondet_cond_3 then y@1 else int.add(x@1, y@1), 0);
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval evalAndPrint blockExitIfProg

end Core.SymbolicEval.Tests
end
