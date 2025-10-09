/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr

namespace Lambda
namespace LExpr

open Std (ToFormat Format format)

-- Only desugaring needed is the .assert
def test: LExpr LTy String  :=
  let_ .topLevel "i" .none <| fun c =>
  .assume (.eq (c.v "i") (.const "0" .none)) <|
  .assert (.eq (c.v "i") (.const "1" .none)) <|
  .skip
/--
info: let _;
assume (%0 == #0) <|
assert (%0 == #1) <|
skip
-/
#guard_msgs in
#eval format test

def testWithoutIf := IfToPushPop test
/--
info: (declare-const b0 Int)
(assert (= b0 0))
(push)
(assert (not (= b0 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| testWithoutIf

-- Now assignments need to be desugared into an assumption
def test2: LExpr LTy String  :=
  let_assign .topLevel "i" _Int (.const "0" .none) <| fun c =>
  .assert (.eq (c.v "i") (.const "1" .none)) <|
  .skip
def test2WithoutIf := IfToPushPop test2
/--
info: let _ : int := #0;
pushpop (
  assume (~! (%0 == #1)) <|
  error
) <|
skip
-/
#guard_msgs in
#eval format test2WithoutIf
/--
info: PANIC at Lambda.LExpr.ToSMT Strata.DL.Lambda.LExpr:1220:9: ToSMT not supported:let _ : int := #0;
pushpop (
  assume (~! (%0 == #1)) <|
  error
) <|
skip
---
info:
-/
#guard_msgs in
#eval ToSMT .topLevel <| test2WithoutIf

def test2WithoutLetAssign := IfToPushPop <| letAssignToLetAssume <| test2
/--
info: let _ : int;
assume (%0 == #0) <|
pushpop (
  assume (~! (%0 == #1)) <|
  error
) <|
skip
-/
#guard_msgs in
#eval format test2WithoutLetAssign
/--
info: (declare-const b0 Int)
(assert (= b0 0))
(push)
(assert (not (= b0 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| test2WithoutLetAssign



def prog: LExpr LTy String :=
  let_ .topLevel "i" _Int <| fun c =>
  let_ c "j" _Int <| fun c =>
  let_ c "k" _Int <| fun c =>
  let_assign c "i0" _Int (c.v "i") <| fun c =>
  let_assign c "j0" _Int (c.v "j") <| fun c =>
  let_assign c "k0" _Int (c.v "k") <| fun c =>
  assume (.eq (plus (c.v "i") (c.v "j")) (c.v "k")) <|
  assert (.eq (c.v "i") (minus (c.v "k") (c.v "j"))) <|
  let_assign c "i" _Int (plus (c.v "i") (plus (c.v "j") (c.v "k"))) <| fun c =>
  let_assign c "j" _Int (plus (c.v "j") (c.v "k")) <| fun c =>
  assert (.eq (c.v "i") (plus (c.v "i0") (plus (c.v "j0") (c.v "k")))) <|
  assert (.eq (c.v "j") (plus (c.v "j0") (c.v "k"))) <|
  assert (.eq (c.v "j0") (minus (c.v "j") (c.v "k"))) <|
  assert (.eq (c.v "i0") (minus (minus (c.v "i") (minus (c.v "j") (c.v "k"))) (c.v "k"))) <|
  --assert (.eq (c.v "i0") (minus (c.v "i") (minus (c.v "j") (c.v "k")))) <| -- Wrong encoding of LLM !
  assert (.eq (c.v "i0") (minus (c.v "i") (c.v "j"))) <|
  assert (.eq (c.v "k") (plus (c.v "i0") (c.v "j0"))) <|
  assert (.eq (c.v "k") (plus (minus (c.v "i") (c.v "j")) (minus (c.v "j") (c.v "k")))) <|
  assert (.eq (plus (c.v "k") (c.v "k")) (c.v "i"))
  skip

/--
info: let _ : int;
let _ : int;
let _ : int;
let _ : int := %2;
let _ : int := %2;
let _ : int := %2;
assume (((~+ %5) %4) == %3) <|
assert (%5 == ((~- %3) %4)) <|
let _ : int := ((~+ %5) ((~+ %4) %3));
let _ : int := ((~+ %5) %4);
assert (%1 == ((~+ %4) ((~+ %3) %5))) <|
assert (%0 == ((~+ %3) %5)) <|
assert (%3 == ((~- %0) %5)) <|
assert (%4 == ((~- ((~- %1) ((~- %0) %5))) %5)) <|
assert (%4 == ((~- %1) %0)) <|
assert (%5 == ((~+ %4) %3)) <|
assert (%5 == ((~+ ((~- %1) %0)) ((~- %0) %5))) <|
assert (((~+ %5) %5) == %1) <|
skip
-/
#guard_msgs in
#eval format prog

/--
info: let _ : int;
let _ : int;
let _ : int;
let _ : int;
assume (%0 == %3) <|
let _ : int;
assume (%0 == %3) <|
let _ : int;
assume (%0 == %3) <|
assume (((~+ %5) %4) == %3) <|
assert (%5 == ((~- %3) %4)) <|
let _ : int;
assume (%0 == ((~+ %6) ((~+ %5) %4))) <|
let _ : int;
assume (%0 == ((~+ %6) %5)) <|
assert (%1 == ((~+ %4) ((~+ %3) %5))) <|
assert (%0 == ((~+ %3) %5)) <|
assert (%3 == ((~- %0) %5)) <|
assert (%4 == ((~- ((~- %1) ((~- %0) %5))) %5)) <|
assert (%4 == ((~- %1) %0)) <|
assert (%5 == ((~+ %4) %3)) <|
assert (%5 == ((~+ ((~- %1) %0)) ((~- %0) %5))) <|
assert (((~+ %5) %5) == %1) <|
skip
-/
#guard_msgs in
#eval format <| letAssignToLetAssume <| prog

/--
info: let _ : int;
let _ : int;
let _ : int;
let _ : int;
assume (%0 == %3) <|
let _ : int;
assume (%0 == %3) <|
let _ : int;
assume (%0 == %3) <|
assume (((~+ %5) %4) == %3) <|
pushpop (
  assume (~! (%5 == ((~- %3) %4))) <|
  error
) <|
let _ : int;
assume (%0 == ((~+ %6) ((~+ %5) %4))) <|
let _ : int;
assume (%0 == ((~+ %6) %5)) <|
pushpop (
  assume (~! (%1 == ((~+ %4) ((~+ %3) %5)))) <|
  error
) <|
pushpop (
  assume (~! (%0 == ((~+ %3) %5))) <|
  error
) <|
pushpop (
  assume (~! (%3 == ((~- %0) %5))) <|
  error
) <|
pushpop (
  assume (~! (%4 == ((~- ((~- %1) ((~- %0) %5))) %5))) <|
  error
) <|
pushpop (
  assume (~! (%4 == ((~- %1) %0))) <|
  error
) <|
pushpop (
  assume (~! (%5 == ((~+ %4) %3))) <|
  error
) <|
pushpop (
  assume (~! (%5 == ((~+ ((~- %1) %0)) ((~- %0) %5)))) <|
  error
) <|
pushpop (
  assume (~! (((~+ %5) %5) == %1)) <|
  error
) <|
skip
-/
#guard_msgs in
#eval format <| IfToPushPop <| letAssignToLetAssume <| prog
/--
info: (declare-const b0 Int)
(declare-const b1 Int)
(declare-const b2 Int)
(declare-const b3 Int)
(assert (= b3 b0))
(declare-const b4 Int)
(assert (= b4 b1))
(declare-const b5 Int)
(assert (= b5 b2))
(assert (= (+ b0 b1) b2))
(push)
(assert (not (= b0 (- b2 b1))))
(check-sat)
(pop)
(declare-const b6 Int)
(assert (= b6 (+ b0 (+ b1 b2))))
(declare-const b7 Int)
(assert (= b7 (+ b1 b2)))
(push)
(assert (not (= b6 (+ b3 (+ b4 b2)))))
(check-sat)
(pop)
(push)
(assert (not (= b7 (+ b4 b2))))
(check-sat)
(pop)
(push)
(assert (not (= b4 (- b7 b2))))
(check-sat)
(pop)
(push)
(assert (not (= b3 (- (- b6 (- b7 b2)) b2))))
(check-sat)
(pop)
(push)
(assert (not (= b3 (- b6 b7))))
(check-sat)
(pop)
(push)
(assert (not (= b2 (+ b3 b4))))
(check-sat)
(pop)
(push)
(assert (not (= b2 (+ (- b6 b7) (- b7 b2)))))
(check-sat)
(pop)
(push)
(assert (not (= (+ b2 b2) b6)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| IfToPushPop <| letAssignToLetAssume <| prog

def debugIf: LExpr LTy String :=
  let_assign .topLevel "i" _Int (.const "0" .none) <| fun c =>
  if_ c (.const "true" .none) ["i"] (
    then_ := fun exit c =>
      let_assign c "i" _Int (.const "1" .none) <| fun c =>
      exit c
  ) (
    else_ := fun exit c =>
      exit c
  ) (
    endif := fun c =>
    .assert (.eq (c.v "i") (.const "1" .none)) <|
    .skip
  )


def debugSubst: LExpr LTy String :=
    .ite (.const "true" .none)
      (.app (.abs .none (.app (.bvar 1) (.bvar 0 ))) (.const "1" .none))
      (.app (.bvar 0) (.const "0" .none))
def replacement: LExpr LTy String := (.abs .none (.assert (.eq (.bvar 0) (.const "1" .none)) .skip))

/-- info: (if #true then let _ := #1; (%1 %0) else (%0 #0)) -/
#guard_msgs in
#eval format <| debugSubst
/--
info: (if #true then let _ := #1; let _ := %0; assert (%0 == #1) <| skip else let _ := #0; assert (%0 == #1) <| skip)
-/
#guard_msgs in
#eval format <| subst replacement debugSubst

def test_simplify: LExpr LTy String :=
  .app (.abs .none (.app (.bvar 1) (.bvar 0))) (.const "1" .none)

/--
info: let _ := #1;
(%1 %0)
-/
#guard_msgs in
#eval format test_simplify

/--info: (%0 #1)-/
#guard_msgs in
#eval format (simplify test_simplify)


/--
info: let _ : int := #0;
((λ (if #true then let _ : int := #1; (%1 %0) else (%0 %1)))) <| λ
assert (%0 == #1) <|
skip
-/
#guard_msgs in
#eval format debugIf
/--
info: let _ : int;
assume (%0 == #0) <|
let _;
assume (%0 == (λ assert (%0 == #1) <| skip)) <|
(if #true then let _ : int; assume (%0 == #1) <| (%1 %0) else (%0 %1))
-/
#guard_msgs in
#eval format <| letAssignToLetAssume <| debugIf
/--
info: ((λ (if #true then (%0 #1) else (%0 #0)))) <| λ
assert (%0 == #1) <|
skip
-/
#guard_msgs in
#eval format <| simplify <| debugIf
/--
info: (if #true then let _ := #1; assert (%0 == #1) <| skip else let _ := #0; assert (%0 == #1) <| skip)
-/
#guard_msgs in
#eval format <| inlineContinuations <| simplify <| debugIf
/-- info: (if #true then assert (#1 == #1) <| skip else assert (#0 == #1) <| skip) -/
#guard_msgs in
#eval format <| simplify <| inlineContinuations <| simplify <| debugIf
/--
info: (push)
(assert true)
(push)
(assert (not (= 1 1)))
(check-sat)
(pop)

(pop)
(assert (not true))
(push)
(assert (not (= 0 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| IfToPushPop <| simplify <| inlineContinuations <| simplify <| debugIf

def implies (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "=>" .none) a) b
def and (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "&&" .none) a) b
def ge (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op ">=" .none) a) b
def lt (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "<" .none) a) b
def le (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "<=" .none) a) b
def gt (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op ">" .none) a) b
def or (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "||" .none) a) b

/- progs with joining conditionals and automatic detection of variables being modified -/
/-var discount: bool;
var superDiscount: bool;
var price: int;
var price0: int := price;
var discountAmount: int;
var quantity: int;
assume discountAmount > 0;
assume price > 0;
if discount {
  price := price - discountAmount;
}
if superDiscount && price > discountAmount {
  price := price - discountAmount;
}
assert !discount ==> price > 0;
assert discountAmount < price0 ==> price > 0;
if price < price0 {
  if !discount {
    assert superDiscount;
  }
  assert discount || superDiscount;
}
assert price < price0 ==> (discount || superDiscount)
assert price < 0 ==> discount && discountAmount > price;
if price > price0 {
  assert false;
  assume false; // ok
}-/
def progIfStmt: LExpr LTy String :=
  let_ .topLevel "superDiscount" _Bool <| fun c =>
  let_ c "discount" _Bool <| fun c =>
  let_ c "price" _Int <| fun c =>
  let_assign c "price0" _Int (c.v "price") <| fun c =>
  let_ c "discountAmount" _Int <| fun c =>
  let_ c "quantity" _Int <| fun c =>
  .assume (.app (.app (.op ">" .none) (c.v "discountAmount")) (.const "0" .none)) <|
  .assume (.app (.app (.op ">" .none) (c.v "price")) (.const "0" .none)) <|
  if_ c (c.v "discount") ["price"] (
    then_ := fun exit c =>
      let_assign c "price" _Int (minus (c.v "price") (c.v "discountAmount")) <| fun c =>
      exit c) (
    else_ := fun exit c => exit c) (
    endif := fun c =>
  if_ c (.and (c.v "superDiscount") (.app (.app (.op ">" .none) (c.v "price")) (c.v "discountAmount"))) ["price"] (
    then_ := fun exit c =>
      let_assign c "price" _Int (minus (c.v "price") (c.v "discountAmount")) <| fun c =>
      exit c) (
    else_ := fun exit c => exit c) (
    endif := fun c =>
  .assert (implies (not (c.v "discount")) (gt (c.v "price") (.const "0" .none))) <|
  .assert (implies (lt (c.v "discountAmount") (c.v "price0")) (gt (c.v "price") (.const "0" .none))) <|
  if_ c (lt (c.v "price") (c.v "price0")) [] (
    then_ := fun exit c =>
      (if_ c (not (c.v "discount")) [] (
        then_ := fun exit c =>
          .assert (c.v "superDiscount") <|
          exit c) (
        else_ := fun exit c => exit c) (
        endif := fun c =>
      .assert (or (c.v "discount") (c.v "superDiscount")) <|
      exit c))) (
    else_ := fun exit c => exit c) (
    endif := fun c =>
  .assert (implies (lt (c.v "price") (c.v "price0")) (or (c.v "discount") (c.v "superDiscount"))) <|
  .assert (implies (lt (c.v "price") (.const "0" .none)) (and (c.v "discount") (gt (c.v "discountAmount") (c.v "price")))) <|
  if_ c (gt (c.v "price") (c.v "price0")) [] (
    then_ := fun exit c =>
      .assert (.const "false" .none) <|
      .assume (.const "false" .none) <|
      exit c) (
    else_ := fun exit c => exit c) (
    endif := fun _ => skip
  ))))

/--
info: let _ : bool;
let _ : bool;
let _ : int;
let _ : int := %0;
let _ : int;
let _ : int;
assume ((~> %1) #0) <|
assume ((~> %3) #0) <|
((λ (if %4 then let _ : int := ((~- %4) %2); (%1 %0) else (%0 %4)))) <| λ
((λ (if ((~&& %6) ((~> %0) %2)) then let _ : int := ((~- %1) %3); (%1 %0) else (%0 %1)))) <| λ
assert ((~=> (~! %6)) ((~> %0) #0)) <|
assert ((~=> ((~< %3) %4)) ((~> %0) #0)) <|
((λ (if ((~< %0) %4) then ((λ (if (~! %7) then assert %9 <| %0 else %0))) <| assert ((~|| %7) %8) <| %0 else %0))) <|
assert ((~=> ((~< %0) %4)) ((~|| %6) %7)) <|
assert ((~=> ((~< %0) #0)) ((~&& %6) ((~> %3) %0))) <|
((λ (if ((~> %0) %4) then assert #false <| assume #false <| %0 else %0))) <|
skip
-/
#guard_msgs in
#eval format progIfStmt


/--
info: let _ : bool;
let _ : bool;
let _ : int;
let _ : int;
let _ : int;
assume ((~> %1) #0) <|
assume ((~> %2) #0) <|
(if %2 then let _ : int := ((~- %2) %1);
   let _ := %0;
   ((λ (if ((~&& %5) ((~> %0) %3)) then let _ : int := ((~- %1) %3); (%1 %0) else (%0 %1)))) <| λ
   assert ((~=> (~! %5)) ((~> %0) #0)) <|
   assert ((~=> ((~< %3) %4)) ((~> %0) #0)) <|
   ((λ (if ((~< %0) %4) then ((λ (if (~! %7) then assert %8 <| %0 else %0))) <| assert ((~|| %6) %7) <| %0 else %0))) <|
   assert ((~=> ((~< %0) %4)) ((~|| %5) %6)) <|
   assert ((~=> ((~< %0) #0)) ((~&& %5) ((~> %3) %0))) <|
   ((λ (if ((~> %0) %4) then assert #false <| assume #false <| %0 else %0))) <|
   skip
 else let _ := %2;
   ((λ (if ((~&& %4) ((~> %0) %2)) then let _ : int := ((~- %1) %2); (%1 %0) else (%0 %1)))) <| λ
   assert ((~=> (~! %4)) ((~> %0) #0)) <|
   assert ((~=> ((~< %2) %3)) ((~> %0) #0)) <|
   ((λ (if ((~< %0) %3) then ((λ (if (~! %6) then assert %7 <| %0 else %0))) <| assert ((~|| %5) %6) <| %0 else %0))) <|
   assert ((~=> ((~< %0) %3)) ((~|| %4) %5)) <|
   assert ((~=> ((~< %0) #0)) ((~&& %4) ((~> %2) %0))) <|
   ((λ (if ((~> %0) %3) then assert #false <| assume #false <| %0 else %0))) <|
   skip)
-/
#guard_msgs in
#eval format (progIfStmt |>
      inlineContinuations
    )

/--
info: let _ : bool;
let _ : bool;
let _ : int;
let _ : int;
let _ : int;
assume ((~> %1) #0) <|
assume ((~> %2) #0) <|
(if %2 then let _ : int := ((~- %2) %1);
   (if ((~&& %3) ((~> (λ assert ((~=> (~! %3)) ((~> %0) #0)) <|
        assert ((~=> ((~< %1) %2)) ((~> %0) #0)) <|
        ((λ (if ((~< %0) %2) then ((λ (if (~! %5) then assert %6 <| %0 else %0))) <|
            assert ((~|| %4) %5) <|
            %0
          else %0))) <|
        assert ((~=> ((~< %0) %2)) ((~|| %3) %4)) <|
        assert ((~=> ((~< %0) #0)) ((~&& %3) ((~> %1) %0))) <|
        ((λ (if ((~> %0) %2) then assert #false <| assume #false <| %0 else %0))) <|
        skip)) %1)) then let _ : int := ((~- %0) %1);
      let _ := %0;
      assert ((~=> (~! %4)) ((~> %0) #0)) <|
      assert ((~=> ((~< %2) %3)) ((~> %0) #0)) <|
      ((λ (if ((~< %0) %3) then ((λ (if (~! %6) then assert %7 <| %0 else %0))) <|
          assert ((~|| %5) %6) <|
          %0
        else %0))) <|
      assert ((~=> ((~< %0) %3)) ((~|| %4) %5)) <|
      assert ((~=> ((~< %0) #0)) ((~&& %4) ((~> %2) %0))) <|
      ((λ (if ((~> %0) %3) then assert #false <| assume #false <| %0 else %0))) <|
      skip
    else let _ := %0;
      assert ((~=> (~! %3)) ((~> %0) #0)) <|
      assert ((~=> ((~< %1) %2)) ((~> %0) #0)) <|
      ((λ (if ((~< %0) %2) then ((λ (if (~! %5) then assert %6 <| %0 else %0))) <|
          assert ((~|| %4) %5) <|
          %0
        else %0))) <|
      assert ((~=> ((~< %0) %2)) ((~|| %3) %4)) <|
      assert ((~=> ((~< %0) #0)) ((~&& %3) ((~> %1) %0))) <|
      ((λ (if ((~> %0) %2) then assert #false <| assume #false <| %0 else %0))) <|
      skip)
 else (if ((~&& %2) ((~> (λ assert ((~=> (~! %2)) ((~> %0) #0)) <|
        assert ((~=> ((~< %2) %1)) ((~> %0) #0)) <|
        ((λ (if ((~< %0) %3) then ((λ (if (~! %4) then assert %5 <| %0 else %0))) <|
            assert ((~|| %3) %4) <|
            %0
          else %0))) <|
        assert ((~=> ((~< %0) %1)) ((~|| %2) %3)) <|
        assert ((~=> ((~< %0) #0)) ((~&& %2) ((~> %2) %0))) <|
        ((λ (if ((~> %0) %3) then assert #false <| assume #false <| %0 else %0))) <|
        skip)) %0)) then let _ : int := ((~- %1) %0);
      let _ := %0;
      assert ((~=> (~! %3)) ((~> %0) #0)) <|
      assert ((~=> ((~< %3) %2)) ((~> %0) #0)) <|
      ((λ (if ((~< %0) %4) then ((λ (if (~! %5) then assert %6 <| %0 else %0))) <|
          assert ((~|| %4) %5) <|
          %0
        else %0))) <|
      assert ((~=> ((~< %0) %2)) ((~|| %3) %4)) <|
      assert ((~=> ((~< %0) #0)) ((~&& %3) ((~> %3) %0))) <|
      ((λ (if ((~> %0) %4) then assert #false <| assume #false <| %0 else %0))) <|
      skip
    else let _ := %1;
      assert ((~=> (~! %2)) ((~> %0) #0)) <|
      assert ((~=> ((~< %2) %1)) ((~> %0) #0)) <|
      ((λ (if ((~< %0) %3) then ((λ (if (~! %4) then assert %5 <| %0 else %0))) <|
          assert ((~|| %3) %4) <|
          %0
        else %0))) <|
      assert ((~=> ((~< %0) %1)) ((~|| %2) %3)) <|
      assert ((~=> ((~< %0) #0)) ((~&& %2) ((~> %2) %0))) <|
      ((λ (if ((~> %0) %3) then assert #false <| assume #false <| %0 else %0))) <|
      skip))
-/
#guard_msgs in
#eval format (progIfStmt |>
      inlineContinuations |>
      inlineContinuations
    )
/--info-/
#guard_msgs in
#eval! progIfStmt |>
      inlineContinuations |>
      inlineContinuations |>
      inlineContinuations |>
      inlineContinuations |>
      inlineContinuations |>
      inlineContinuations |>
      inlineContinuations |>
      letAssignToLetAssume |>
      IfToPushPop |>
      ToSMT .topLevel

end LExpr
end Lambda
