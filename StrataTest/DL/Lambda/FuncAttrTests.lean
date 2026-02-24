/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.TypeFactory

/-!
## Tests for FuncAttr with non-zero paramIdx

Tests that `inlineIfConstr 1` correctly inlines when the second argument
is a constructor application, and does not inline when it is symbolic.
-/

namespace Lambda

open Std (ToFormat Format format)
open LExpr LTy.Syntax LExpr.SyntaxMono

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()

private def nilConstr : LConstr Unit :=
  { name := "Nil", args := [], testerName := "isNil" }

private def consConstr : LConstr Unit :=
  { name := "Cons",
    args := [("hd", .int), ("tl", .tcons "MyList" [])],
    testerName := "isCons" }

private def myListTy : LDatatype Unit :=
  { name := "MyList", typeArgs := [], constrs := [nilConstr, consConstr], constrs_ne := rfl }

-- A function with inlineIfConstr on the 2nd parameter (index 1).
-- myIsNil(dummy: int, xs: MyList) : bool  :=  isNil(xs)
-- It should inline when xs is a constructor, regardless of dummy.
private def myIsNilFunc : LFunc TestParams :=
  { name := "myIsNil",
    inputs := [("dummy", mty[int]), ("xs", .tcons "MyList" [])],
    output := mty[bool],
    body := some esM[(~isNil xs)],
    attr := #[.inlineIfConstr 1] }

-- An uninterpreted constant xs : MyList
private def xsConst : LFunc TestParams :=
  { name := "xs_sym",
    inputs := [],
    output := .tcons "MyList" [] }

-- Test: myIsNil(42, Nil) should reduce (2nd arg is constructor)
/--
info: Annotated expression:
((~myIsNil : (arrow int (arrow MyList bool))) #42 (~Nil : MyList))

---
info: #true
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[[myListTy]] #[myIsNilFunc]
    esM[((~myIsNil #42) (~Nil : MyList))]

-- Test: myIsNil(42, Cons(1, Nil)) should reduce (2nd arg is constructor)
/--
info: Annotated expression:
((~myIsNil : (arrow int (arrow MyList bool))) #42 ((~Cons : (arrow int (arrow MyList MyList))) #1 (~Nil : MyList)))

---
info: #false
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[[myListTy]] #[myIsNilFunc]
    esM[((~myIsNil #42) ((~Cons #1) (~Nil : MyList)))]

-- Test: myIsNil(42, xs_sym) should NOT reduce (2nd arg is not a constructor)
/--
info: Annotated expression:
((~myIsNil : (arrow int (arrow MyList bool))) #42 (~xs_sym : MyList))

---
info: ((~myIsNil : (arrow int (arrow MyList bool))) #42 (~xs_sym : MyList))
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[[myListTy]] #[myIsNilFunc, xsConst]
    esM[((~myIsNil #42) ~xs_sym)]

end Lambda
