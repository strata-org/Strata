/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify
import Strata.Languages.Core.CoreOp

/-! ## Loop elimination: deterministic guard without measure

A while loop with a deterministic guard and invariant but no decreases clause.
Loop elimination havocs assigned vars, checks invariants, and assumes
not-guard on exit — without any measure-related obligations.
-/

def LoopNoMeasurePgm :=
#strata
program C_Simp;

int procedure loopNoMeasure (n: int)
  //@pre (n >= 0);
  //@post true;
{
  var i : int;
  i = 0;
  while (i < n)
  //@invariant (i <= n)
  {
    i = i + 1;
  }
  //@assert [i_le_n] (i <= n);
  return i;
}

#end

/--
info: program Core;

procedure loopNoMeasure (n : int, out return : int)
spec {
  requires [pre]: n >= 0;
  ensures [post]: true;
  } {
  var i : int;
  i := 0;
  if (i < n) {
    first_iter_asserts: {
      assert [entry_invariant_0]: i <= n;
    }
    |arbitrary iter facts|: {
      |loop havoc|: {
        havoc i;
      }
      arbitrary_iter_assumes: {
        assume [assume_guard]: i < n;
        assume [assume_invariant_0]: i <= n;
      }
      i := i + 1;
      assert [arbitrary_iter_maintain_invariant_0]: i <= n;
    }
    |loop havoc|: {
      havoc i;
    }
    assume [not_guard]: !(i < n);
    assume [invariant_0]: i <= n;
  }
  assert [i_le_n]: i <= n;
  return := i;
};
-/
#guard_msgs in
#eval Strata.to_core (Strata.C_Simp.get_program LoopNoMeasurePgm)

/-! ## Loop elimination: nondet guard

C_Simp's parser produces deterministic guards, so we construct a
C_Simp function with a nondet loop programmatically and pass it
through `to_core` to test the nondet loop elimination path.
-/

open Strata in
open Strata.C_Simp in
private def csimpOpExpr (op : Core.CoreOp) : Expression.Expr :=
  .op () op.toString none

open Strata in
open Strata.C_Simp in
private def nondetLoopProgram : C_Simp.Program :=
  let md : Imperative.MetaData Expression := .empty
  let i : Expression.Ident := ⟨"i", ()⟩
  let n : Expression.Ident := ⟨"n", ()⟩
  let iExpr : Expression.Expr := .fvar () i none
  let nExpr : Expression.Expr := .fvar () n none
  let zero : Expression.Expr := .intConst () 0
  let one : Expression.Expr := .intConst () 1
  let intTy : Lambda.LTy := .forAll [] (.tcons "int" [])
  let iLeN : Expression.Expr := .app () (.app () (csimpOpExpr (.numeric ⟨.int, .Le⟩)) iExpr) nExpr
  let iAddOne : Expression.Expr := .app () (.app () (csimpOpExpr (.numeric ⟨.int, .Add⟩)) iExpr) one
  { funcs := [{
    name := ⟨"nondetLoop", ()⟩,
    pre := .app () (.app () (csimpOpExpr (.numeric ⟨.int, .Ge⟩)) nExpr) zero,
    post := .true (),
    ret_ty := .tcons "int" [],
    inputs := ListMap.ofList [(n, .tcons "int" [])],
    body := [
      .cmd (.init i intTy (.det zero) md),
      .loop .nondet .none [iLeN] [
        .cmd (.set i (.det iAddOne) md)
      ] md,
      .exit "return" md
    ]
  }]}

/--
info: program Core;

procedure nondetLoop (n : int, out return : int)
spec {
  requires [pre]: n >= 0;
  ensures [post]: true;
  } {
  var i : int := 0;
  loop: {
    first_iter_asserts: {
      assert [entry_invariant_0]: i <= n;
      assume [assume_entry_invariant_0]: i <= n;
    }
    if * {
      |arbitrary iter facts|: {
        |loop havoc|: {
          havoc i;
        }
        arbitrary_iter_assumes: {
          assume [assume_invariant_0]: i <= n;
        }
        i := i + 1;
        assert [arbitrary_iter_maintain_invariant_0]: i <= n;
      }
      |loop havoc|: {
        havoc i;
      }
      assume [invariant_0]: i <= n;
    }
  }
  exit return;
};
-/
#guard_msgs in
#eval Strata.to_core nondetLoopProgram
