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
info: let %;
assume (%0 == #0) <|
assert (%0 == #1) <|
skip
-/
#guard_msgs in
#eval format test

def testWithoutIf := ifToPushPop test
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
def test2WithoutIf := ifToPushPop test2
/--
info: let % : int := #0;
pushpop (
  assume (~! (%0 == #1)) <|
  error
) <|
skip
-/
#guard_msgs in
#eval format test2WithoutIf
/--
info: PANIC at Lambda.LExpr.ToSMT Strata.DL.Lambda.LExpr:1225:9: ToSMT not supported:let % : int := #0;
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

def test2WithoutLetAssign := ifToPushPop <| letAssignToLetAssume <| test2
/--
info: let % : int;
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
info: let % : int;
let % : int;
let % : int;
let % : int := %2;
let % : int := %2;
let % : int := %2;
assume (((~+ %5) %4) == %3) <|
assert (%5 == ((~- %3) %4)) <|
let % : int := ((~+ %5) ((~+ %4) %3));
let % : int := ((~+ %5) %4);
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
info: let % : int;
let % : int;
let % : int;
let % : int;
assume (%0 == %3) <|
let % : int;
assume (%0 == %3) <|
let % : int;
assume (%0 == %3) <|
assume (((~+ %5) %4) == %3) <|
assert (%5 == ((~- %3) %4)) <|
let % : int;
assume (%0 == ((~+ %6) ((~+ %5) %4))) <|
let % : int;
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
info: let % : int;
let % : int;
let % : int;
let % : int;
assume (%0 == %3) <|
let % : int;
assume (%0 == %3) <|
let % : int;
assume (%0 == %3) <|
assume (((~+ %5) %4) == %3) <|
pushpop (
  assume (~! (%5 == ((~- %3) %4))) <|
  error
) <|
let % : int;
assume (%0 == ((~+ %6) ((~+ %5) %4))) <|
let % : int;
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
#eval format <| ifToPushPop <| letAssignToLetAssume <| prog
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
#eval ToSMT .topLevel <| ifToPushPop <| letAssignToLetAssume <| prog

-- Proof or test that letAssignToLetAssume preserves semantics.

def debugSubst: LExpr LTy String :=
    .ite (.const "true" .none)
      (.app (.abs .none (.app (.bvar 1) (.bvar 0 ))) (.const "1" .none))
      (.app (.bvar 0) (.const "0" .none))
def replacement: LExpr LTy String := (.abs .none (.assert (.eq (.bvar 0) (.const "1" .none)) .skip))

/-- info: (if #true then let % := #1; (%1 %0) else (%0 #0)) -/
#guard_msgs in
#eval format <| debugSubst
/--
info: (if #true then let % := #1; let % := %0; assert (%0 == #1) <| skip else let % := #0; assert (%0 == #1) <| skip)
-/
#guard_msgs in
#eval format <| subst replacement debugSubst

def test_simplify: LExpr LTy String :=
  .app (.abs .none (.app (.bvar 1) (.bvar 0))) (.const "1" .none)

/--
info: let % := #1;
(%1 %0)
-/
#guard_msgs in
#eval format test_simplify

/--info: (%0 #1)-/
#guard_msgs in
#eval format (simplify test_simplify)


def debugIf: LExpr LTy String :=
  let_ .topLevel "b" _Bool <| fun c =>
  let_assign c "i" _Int (.const "0" .none) <| fun c =>
  if_ c ["i"] (fun c => c.v "b") (
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

/--
info: let % : bool;
let % : int := #0;
((λ (if %2 then let % : int := #1; (%1 %0) else (%0 %1)))) <| λ
assert (%0 == #1) <|
skip
-/
#guard_msgs in
#eval format debugIf
/--
info: let % : bool;
let % : int;
assume (%0 == #0) <|
let %;
assume (%0 == (λ assert (%0 == #1) <| skip)) <|
(if %2 then let % : int; assume (%0 == #1) <| (%1 %0) else (%0 %1))
-/
#guard_msgs in
#eval format <| letAssignToLetAssume <| debugIf
-- Let's forget about converting a let assign to let assume until the end of the pipeline, otherwe we miss very useful inlinings.
-- Also, we currently lack determinism detection.

/--
info: let % : bool;
((λ (if %1 then (%0 #1) else (%0 #0)))) <| λ
assert (%0 == #1) <|
skip
-/
#guard_msgs in
#eval format <| simplify <| debugIf
/--
info: let % : bool;
let % : int := #0;
(if %1 then let % : int := #1; let % := %0; assert (%0 == #1) <| skip else let % := %0; assert (%0 == #1) <| skip)
-/
#guard_msgs in
#eval format <| inlineContinuations <| debugIf
/--
info: (declare-const b0 Bool)
(declare-const b1 Int)
(assert (= b1 0))
(push)
(assert b0)
(declare-const b2 Int)
(assert (= b2 1))
(declare-const b3 Int)
(assert (= b3 b2))
(push)
(assert (not (= b3 1)))
(check-sat)
(pop)

(pop)
(assert (not b0))
(declare-const b2 Int)
(assert (= b2 b1))
(push)
(assert (not (= b2 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| ifToPushPop <| letAssignToLetAssume <| inlineContinuations <| debugIf
/--
info: let % : bool;
(if %0 then assert (#1 == #1) <| skip else assert (#0 == #1) <| skip)
-/
#guard_msgs in
#eval format <| simplify <| inlineContinuations <| simplify <| debugIf
/--
info: (declare-const b0 Bool)
(push)
(assert b0)
(push)
(assert (not (= 1 1)))
(check-sat)
(pop)

(pop)
(assert (not b0))
(push)
(assert (not (= 0 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| ifToPushPop <| simplify <| inlineContinuations <| simplify <| debugIf

def implies (a b: LExpr LTy String) := LExpr.app (LExpr.app (LExpr.op "==>" .none) a) b
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
  if_ c ["price"] (fun c => c.v "discount") (
    then_ := fun exit c =>
      let_assign c "price" _Int (minus (c.v "price") (c.v "discountAmount")) <| fun c =>
      exit c) (
    else_ := fun exit c => exit c) (
    endif := fun c =>
  if_ c ["price"] (fun c => .and (c.v "superDiscount") (.app (.app (.op ">" .none) (c.v "price")) (c.v "discountAmount"))) (
    then_ := fun exit c =>
      let_assign c "price" _Int (minus (c.v "price") (c.v "discountAmount")) <| fun c =>
      exit c) (
    else_ := fun exit c => exit c) (
    endif := fun c =>
  .assert (implies (not (c.v "discount")) (gt (c.v "price") (.const "0" .none))) <|
  .assert (implies (lt (c.v "discountAmount") (c.v "price0")) (gt (c.v "price") (.const "0" .none))) <|
  if_ c [] (fun c => lt (c.v "price") (c.v "price0")) (
    then_ := fun exit c =>
      (if_ c [] (fun c => not (c.v "discount")) (
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
  if_ c [] (fun c => gt (c.v "price") (c.v "price0")) (
    then_ := fun exit c =>
      .assert (.const "false" .none) <|
      .assume (.const "false" .none) <|
      exit c) (
    else_ := fun exit c => exit c) (
    endif := fun _ => skip
  ))))

/--
info: let % : bool;
let % : bool;
let % : int;
let % : int := %0;
let % : int;
let % : int;
assume ((~> %1) #0) <|
assume ((~> %3) #0) <|
((λ (if %5 then let % : int := ((~- %4) %2); (%1 %0) else (%0 %4)))) <| λ
((λ (if ((~&& %7) ((~> %1) %3)) then let % : int := ((~- %1) %3); (%1 %0) else (%0 %1)))) <| λ
assert ((~==> (~! %6)) ((~> %0) #0)) <|
assert ((~==> ((~< %3) %4)) ((~> %0) #0)) <|
((λ (if ((~< %1) %5) then ((λ (if (~! %8) then assert %9 <| %0 else %0))) <| assert ((~|| %7) %8) <| %0 else %0))) <|
assert ((~==> ((~< %0) %4)) ((~|| %6) %7)) <|
assert ((~==> ((~< %0) #0)) ((~&& %6) ((~> %3) %0))) <|
((λ (if ((~> %1) %5) then assert #false <| assume #false <| %0 else %0))) <|
skip
-/
#guard_msgs in
#eval format progIfStmt

/--
info: let % : bool;
let % : bool;
let % : int;
let % : int := %0;
let % : int;
let % : int;
assume ((~> %1) #0) <|
assume ((~> %3) #0) <|
(if %4 then let % : int := ((~- %3) %1);
   let % := %0;
   (if ((~&& %7) ((~> %0) %3)) then let % : int := ((~- %0) %3);
      let % := %0;
      assert ((~==> (~! %8)) ((~> %0) #0)) <|
      assert ((~==> ((~< %5) %6)) ((~> %0) #0)) <|
      (if ((~< %0) %6) then (if (~! %8) then assert %9 <|
            assert ((~|| %8) %9) <|
            assert ((~==> ((~< %0) %6)) ((~|| %8) %9)) <|
            assert ((~==> ((~< %0) #0)) ((~&& %8) ((~> %5) %0))) <|
            (if ((~> %0) %6) then assert #false <| assume #false <| skip else skip)
          else assert ((~|| %8) %9) <|
            assert ((~==> ((~< %0) %6)) ((~|| %8) %9)) <|
            assert ((~==> ((~< %0) #0)) ((~&& %8) ((~> %5) %0))) <|
            (if ((~> %0) %6) then assert #false <| assume #false <| skip else skip))
       else assert ((~==> ((~< %0) %6)) ((~|| %8) %9)) <|
         assert ((~==> ((~< %0) #0)) ((~&& %8) ((~> %5) %0))) <|
         (if ((~> %0) %6) then assert #false <| assume #false <| skip else skip))
    else let % := %0;
      assert ((~==> (~! %7)) ((~> %0) #0)) <|
      assert ((~==> ((~< %4) %5)) ((~> %0) #0)) <|
      (if ((~< %0) %5) then (if (~! %7) then assert %8 <|
            assert ((~|| %7) %8) <|
            assert ((~==> ((~< %0) %5)) ((~|| %7) %8)) <|
            assert ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0))) <|
            (if ((~> %0) %5) then assert #false <| assume #false <| skip else skip)
          else assert ((~|| %7) %8) <|
            assert ((~==> ((~< %0) %5)) ((~|| %7) %8)) <|
            assert ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0))) <|
            (if ((~> %0) %5) then assert #false <| assume #false <| skip else skip))
       else assert ((~==> ((~< %0) %5)) ((~|| %7) %8)) <|
         assert ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0))) <|
         (if ((~> %0) %5) then assert #false <| assume #false <| skip else skip)))
 else let % := %3;
   (if ((~&& %6) ((~> %0) %2)) then let % : int := ((~- %0) %2);
      let % := %0;
      assert ((~==> (~! %7)) ((~> %0) #0)) <|
      assert ((~==> ((~< %4) %5)) ((~> %0) #0)) <|
      (if ((~< %0) %5) then (if (~! %7) then assert %8 <|
            assert ((~|| %7) %8) <|
            assert ((~==> ((~< %0) %5)) ((~|| %7) %8)) <|
            assert ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0))) <|
            (if ((~> %0) %5) then assert #false <| assume #false <| skip else skip)
          else assert ((~|| %7) %8) <|
            assert ((~==> ((~< %0) %5)) ((~|| %7) %8)) <|
            assert ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0))) <|
            (if ((~> %0) %5) then assert #false <| assume #false <| skip else skip))
       else assert ((~==> ((~< %0) %5)) ((~|| %7) %8)) <|
         assert ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0))) <|
         (if ((~> %0) %5) then assert #false <| assume #false <| skip else skip))
    else let % := %0;
      assert ((~==> (~! %6)) ((~> %0) #0)) <|
      assert ((~==> ((~< %3) %4)) ((~> %0) #0)) <|
      (if ((~< %0) %4) then (if (~! %6) then assert %7 <|
            assert ((~|| %6) %7) <|
            assert ((~==> ((~< %0) %4)) ((~|| %6) %7)) <|
            assert ((~==> ((~< %0) #0)) ((~&& %6) ((~> %3) %0))) <|
            (if ((~> %0) %4) then assert #false <| assume #false <| skip else skip)
          else assert ((~|| %6) %7) <|
            assert ((~==> ((~< %0) %4)) ((~|| %6) %7)) <|
            assert ((~==> ((~< %0) #0)) ((~&& %6) ((~> %3) %0))) <|
            (if ((~> %0) %4) then assert #false <| assume #false <| skip else skip))
       else assert ((~==> ((~< %0) %4)) ((~|| %6) %7)) <|
         assert ((~==> ((~< %0) #0)) ((~&& %6) ((~> %3) %0))) <|
         (if ((~> %0) %4) then assert #false <| assume #false <| skip else skip))))
-/
#guard_msgs in
#eval format (progIfStmt |>
      inlineContinuations
    )

/--
info: let % : bool;
let % : bool;
let % : int;
let % : int;
assume (%0 == %1) <|
let % : int;
let % : int;
assume ((~> %1) #0) <|
assume ((~> %3) #0) <|
pushpop (
  assume %4 <|
  let % : int;
  assume (%0 == ((~- %4) %2)) <|
  let %;
  assume (%0 == %1) <|
  pushpop (
    assume ((~&& %7) ((~> %0) %3)) <|
    let % : int;
    assume (%0 == ((~- %1) %4)) <|
    let %;
    assume (%0 == %1) <|
    pushpop (
      assume (~! ((~==> (~! %8)) ((~> %0) #0))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< %5) %6)) ((~> %0) #0))) <|
      error
    ) <|
    pushpop (
      assume ((~< %0) %6) <|
      pushpop (
        assume (~! %8) <|
        pushpop (
          assume (~! %9) <|
          error
        ) <|
        pushpop (
          assume (~! ((~|| %8) %9)) <|
          error
        ) <|
        pushpop (
          assume (~! ((~==> ((~< %0) %6)) ((~|| %8) %9))) <|
          error
        ) <|
        pushpop (
          assume (~! ((~==> ((~< %0) #0)) ((~&& %8) ((~> %5) %0)))) <|
          error
        ) <|
        pushpop (
          assume ((~> %0) %6) <|
          pushpop (
            assume (~! #false) <|
            error
          ) <|
          assume #false <|
          skip
        ) <|
        assume (~! ((~> %0) %6)) <|
        skip
      ) <|
      assume (~! (~! %8)) <|
      pushpop (
        assume (~! ((~|| %8) %9)) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< %0) %6)) ((~|| %8) %9))) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< %0) #0)) ((~&& %8) ((~> %5) %0)))) <|
        error
      ) <|
      pushpop (
        assume ((~> %0) %6) <|
        pushpop (
          assume (~! #false) <|
          error
        ) <|
        assume #false <|
        skip
      ) <|
      assume (~! ((~> %0) %6)) <|
      skip
    ) <|
    assume (~! ((~< %0) %6)) <|
    pushpop (
      assume (~! ((~==> ((~< %0) %6)) ((~|| %8) %9))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< %0) #0)) ((~&& %8) ((~> %5) %0)))) <|
      error
    ) <|
    pushpop (
      assume ((~> %0) %6) <|
      pushpop (
        assume (~! #false) <|
        error
      ) <|
      assume #false <|
      skip
    ) <|
    assume (~! ((~> %0) %6)) <|
    skip
  ) <|
  assume (~! ((~&& %7) ((~> %0) %3))) <|
  let %;
  assume (%0 == %1) <|
  pushpop (
    assume (~! ((~==> (~! %7)) ((~> %0) #0))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< %4) %5)) ((~> %0) #0))) <|
    error
  ) <|
  pushpop (
    assume ((~< %0) %5) <|
    pushpop (
      assume (~! %7) <|
      pushpop (
        assume (~! %8) <|
        error
      ) <|
      pushpop (
        assume (~! ((~|| %7) %8)) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< %0) %5)) ((~|| %7) %8))) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0)))) <|
        error
      ) <|
      pushpop (
        assume ((~> %0) %5) <|
        pushpop (
          assume (~! #false) <|
          error
        ) <|
        assume #false <|
        skip
      ) <|
      assume (~! ((~> %0) %5)) <|
      skip
    ) <|
    assume (~! (~! %7)) <|
    pushpop (
      assume (~! ((~|| %7) %8)) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< %0) %5)) ((~|| %7) %8))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0)))) <|
      error
    ) <|
    pushpop (
      assume ((~> %0) %5) <|
      pushpop (
        assume (~! #false) <|
        error
      ) <|
      assume #false <|
      skip
    ) <|
    assume (~! ((~> %0) %5)) <|
    skip
  ) <|
  assume (~! ((~< %0) %5)) <|
  pushpop (
    assume (~! ((~==> ((~< %0) %5)) ((~|| %7) %8))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0)))) <|
    error
  ) <|
  pushpop (
    assume ((~> %0) %5) <|
    pushpop (
      assume (~! #false) <|
      error
    ) <|
    assume #false <|
    skip
  ) <|
  assume (~! ((~> %0) %5)) <|
  skip
) <|
assume (~! %4) <|
let %;
assume (%0 == %4) <|
pushpop (
  assume ((~&& %6) ((~> %0) %2)) <|
  let % : int;
  assume (%0 == ((~- %1) %3)) <|
  let %;
  assume (%0 == %1) <|
  pushpop (
    assume (~! ((~==> (~! %7)) ((~> %0) #0))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< %4) %5)) ((~> %0) #0))) <|
    error
  ) <|
  pushpop (
    assume ((~< %0) %5) <|
    pushpop (
      assume (~! %7) <|
      pushpop (
        assume (~! %8) <|
        error
      ) <|
      pushpop (
        assume (~! ((~|| %7) %8)) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< %0) %5)) ((~|| %7) %8))) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0)))) <|
        error
      ) <|
      pushpop (
        assume ((~> %0) %5) <|
        pushpop (
          assume (~! #false) <|
          error
        ) <|
        assume #false <|
        skip
      ) <|
      assume (~! ((~> %0) %5)) <|
      skip
    ) <|
    assume (~! (~! %7)) <|
    pushpop (
      assume (~! ((~|| %7) %8)) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< %0) %5)) ((~|| %7) %8))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0)))) <|
      error
    ) <|
    pushpop (
      assume ((~> %0) %5) <|
      pushpop (
        assume (~! #false) <|
        error
      ) <|
      assume #false <|
      skip
    ) <|
    assume (~! ((~> %0) %5)) <|
    skip
  ) <|
  assume (~! ((~< %0) %5)) <|
  pushpop (
    assume (~! ((~==> ((~< %0) %5)) ((~|| %7) %8))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< %0) #0)) ((~&& %7) ((~> %4) %0)))) <|
    error
  ) <|
  pushpop (
    assume ((~> %0) %5) <|
    pushpop (
      assume (~! #false) <|
      error
    ) <|
    assume #false <|
    skip
  ) <|
  assume (~! ((~> %0) %5)) <|
  skip
) <|
assume (~! ((~&& %6) ((~> %0) %2))) <|
let %;
assume (%0 == %1) <|
pushpop (
  assume (~! ((~==> (~! %6)) ((~> %0) #0))) <|
  error
) <|
pushpop (
  assume (~! ((~==> ((~< %3) %4)) ((~> %0) #0))) <|
  error
) <|
pushpop (
  assume ((~< %0) %4) <|
  pushpop (
    assume (~! %6) <|
    pushpop (
      assume (~! %7) <|
      error
    ) <|
    pushpop (
      assume (~! ((~|| %6) %7)) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< %0) %4)) ((~|| %6) %7))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< %0) #0)) ((~&& %6) ((~> %3) %0)))) <|
      error
    ) <|
    pushpop (
      assume ((~> %0) %4) <|
      pushpop (
        assume (~! #false) <|
        error
      ) <|
      assume #false <|
      skip
    ) <|
    assume (~! ((~> %0) %4)) <|
    skip
  ) <|
  assume (~! (~! %6)) <|
  pushpop (
    assume (~! ((~|| %6) %7)) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< %0) %4)) ((~|| %6) %7))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< %0) #0)) ((~&& %6) ((~> %3) %0)))) <|
    error
  ) <|
  pushpop (
    assume ((~> %0) %4) <|
    pushpop (
      assume (~! #false) <|
      error
    ) <|
    assume #false <|
    skip
  ) <|
  assume (~! ((~> %0) %4)) <|
  skip
) <|
assume (~! ((~< %0) %4)) <|
pushpop (
  assume (~! ((~==> ((~< %0) %4)) ((~|| %6) %7))) <|
  error
) <|
pushpop (
  assume (~! ((~==> ((~< %0) #0)) ((~&& %6) ((~> %3) %0)))) <|
  error
) <|
pushpop (
  assume ((~> %0) %4) <|
  pushpop (
    assume (~! #false) <|
    error
  ) <|
  assume #false <|
  skip
) <|
assume (~! ((~> %0) %4)) <|
skip
-/
#guard_msgs in
#eval format (progIfStmt |>
      inlineContinuations |>
      letAssignToLetAssume |>
      ifToPushPop
    )

-- TODO: It does not type check yet, there are replacements that are wrong. Need to try smaller examples first.
-- HOWEVER: We have a path to soundness as we can prove that this program has the same error reporting as the original one.

/--
info: (declare-const b0 Bool)
(declare-const b1 Bool)
(declare-const b2 Int)
(declare-const b3 Int)
(assert (= b3 b2))
(declare-const b4 Int)
(declare-const b5 Int)
(assert (> b4 0))
(assert (> b2 0))
(push)
(assert b1)
(declare-const b6 Int)
(assert (= b6 (- b2 b4)))
(declare-const b7 Int)
(assert (= b7 b6))
(push)
(assert (and b0 (> b7 b4)))
(declare-const b8 Int)
(assert (= b8 (- b7 b4)))
(declare-const b9 Int)
(assert (= b9 b8))
(push)
(assert (not (=> (not b1) (> b9 0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b4 b3) (> b9 0))))
(check-sat)
(pop)
(push)
(assert (< b9 b3))
(push)
(assert (not b1))
(push)
(assert (not b0))
(check-sat)
(pop)
(push)
(assert (not (or b1 b0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< b9 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b9 0) (and b1 (> b4 b9)))))
(check-sat)
(pop)
(push)
(assert (> b9 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b9 b3)))

(pop)
(assert (not (not b1)))
(push)
(assert (not (or b1 b0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< b9 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b9 0) (and b1 (> b4 b9)))))
(check-sat)
(pop)
(push)
(assert (> b9 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b9 b3)))

(pop)
(assert (not (< b9 b3)))
(push)
(assert (not (=> (< b9 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b9 0) (and b1 (> b4 b9)))))
(check-sat)
(pop)
(push)
(assert (> b9 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b9 b3)))

(pop)
(assert (not (and b0 (> b7 b4))))
(declare-const b8 Int)
(assert (= b8 b7))
(push)
(assert (not (=> (not b1) (> b8 0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b4 b3) (> b8 0))))
(check-sat)
(pop)
(push)
(assert (< b8 b3))
(push)
(assert (not b1))
(push)
(assert (not b0))
(check-sat)
(pop)
(push)
(assert (not (or b1 b0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 0) (and b1 (> b4 b8)))))
(check-sat)
(pop)
(push)
(assert (> b8 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b8 b3)))

(pop)
(assert (not (not b1)))
(push)
(assert (not (or b1 b0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 0) (and b1 (> b4 b8)))))
(check-sat)
(pop)
(push)
(assert (> b8 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b8 b3)))

(pop)
(assert (not (< b8 b3)))
(push)
(assert (not (=> (< b8 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 0) (and b1 (> b4 b8)))))
(check-sat)
(pop)
(push)
(assert (> b8 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b8 b3)))

(pop)
(assert (not b1))
(declare-const b6 Int)
(assert (= b6 b2))
(push)
(assert (and b0 (> b6 b4)))
(declare-const b7 Int)
(assert (= b7 (- b6 b4)))
(declare-const b8 Int)
(assert (= b8 b7))
(push)
(assert (not (=> (not b1) (> b8 0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b4 b3) (> b8 0))))
(check-sat)
(pop)
(push)
(assert (< b8 b3))
(push)
(assert (not b1))
(push)
(assert (not b0))
(check-sat)
(pop)
(push)
(assert (not (or b1 b0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 0) (and b1 (> b4 b8)))))
(check-sat)
(pop)
(push)
(assert (> b8 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b8 b3)))

(pop)
(assert (not (not b1)))
(push)
(assert (not (or b1 b0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 0) (and b1 (> b4 b8)))))
(check-sat)
(pop)
(push)
(assert (> b8 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b8 b3)))

(pop)
(assert (not (< b8 b3)))
(push)
(assert (not (=> (< b8 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b8 0) (and b1 (> b4 b8)))))
(check-sat)
(pop)
(push)
(assert (> b8 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b8 b3)))

(pop)
(assert (not (and b0 (> b6 b4))))
(declare-const b7 Int)
(assert (= b7 b6))
(push)
(assert (not (=> (not b1) (> b7 0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b4 b3) (> b7 0))))
(check-sat)
(pop)
(push)
(assert (< b7 b3))
(push)
(assert (not b1))
(push)
(assert (not b0))
(check-sat)
(pop)
(push)
(assert (not (or b1 b0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< b7 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b7 0) (and b1 (> b4 b7)))))
(check-sat)
(pop)
(push)
(assert (> b7 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b7 b3)))

(pop)
(assert (not (not b1)))
(push)
(assert (not (or b1 b0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< b7 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b7 0) (and b1 (> b4 b7)))))
(check-sat)
(pop)
(push)
(assert (> b7 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b7 b3)))

(pop)
(assert (not (< b7 b3)))
(push)
(assert (not (=> (< b7 b3) (or b1 b0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< b7 0) (and b1 (> b4 b7)))))
(check-sat)
(pop)
(push)
(assert (> b7 b3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> b7 b3)))
-/
#guard_msgs in
#eval ToSMT .topLevel (progIfStmt |>
      inlineContinuations |>
      letAssignToLetAssume |>
      ifToPushPop
    )


def progIfStmtDebug: LExpr LTy String :=
  let_ .topLevel "discount" _Bool <| fun c =>
  let_ c "price" _Int <| fun c =>
  let_ c "discountAmount" _Int <| fun c =>
  if_ c ["price"] (fun c => c.v "discount") (
    then_ := fun exit c =>
      let_assign c "price" _Int (minus (c.v "price") (c.v "discountAmount")) <| fun c =>
      exit c) (
    else_ := fun exit c => exit c) (
    endif := fun c =>
  .assert (implies (not (c.v "discount")) (gt (c.v "price") (.const "0" .none))) <|
  skip)

/-
info: let b0% : bool;
let b1% : int;
let b2% : int;
((λb3 (if b0%3 then let b4% : int := ((~- b1%2) b2%1); (b3%1 b4%0) else (%0 %2)))) <| λb3
assert ((~==> (~! b0%3)) ((~> b3%0) #0)) <|
skip
-/
#eval format (progIfStmtDebug
      --|> inlineContinuations
      --|> letAssignToLetAssume
      --|> ifToPushPop
    )

/-
info: let b0% : bool;
let b1% : int;
let b2% : int;
((λb3 (
  if b0%3 then
    let b4% : int := ((~- b1%2) b2%1);
    (b3%1 b4%0)
  else
    (%0 %2)))) <| λb3. assert ((~==> (~! b0%3)) ((~> b3%0) #0)) skip
-/

/-
info: let b0% : bool;
let b1% : int;
let b2% : int;

  if b0%3 then
    let b4% : int := ((~- b1%2) b2%1);
    (b3%1 b4%0)
  else
    (%0 %2)))) <| λb3. assert ((~==> (~! b0%3)) ((~> b3%0) #0)) skip
-/



/-
info: let b0% : bool;
let b1% : int;
let b2% : int;
(((if b0%2 then
  let b3% : int := ((~- b1%1) b2%0);
  ((λb4: Int. assert ((~==> (~! b0%3)) ((~> b4%0) #0))) b3%0) else (%0 %2))))
skip
-/

/-
info: let b0% : bool;
let b1% : int;
let b2% : int;
(if b0%2 then let b3% : int := ((~- b1%1) b2%0);
   let b4% := b3%0;
   assert ((~==> (~! b1%3)) ((~> b4%0) #0)) <|
   skip
 else let b4% := b2%1;
   assert ((~==> (~! b1%2)) ((~> b4%0) #0)) <|
   skip)
-/
#eval format (progIfStmtDebug
      |> inlineContinuations
      --|> letAssignToLetAssume
      --|> ifToPushPop
    )

/--
info: (declare-const b0 Bool)
(declare-const b1 Int)
(declare-const b2 Int)
(push)
(assert b0)
(declare-const b3 Int)
(assert (= b3 (- b1 b2)))
(declare-const b4 Int)
(assert (= b4 b3))
(push)
(assert (not (=> (not b0) (> b4 0))))
(check-sat)
(pop)

(pop)
(assert (not b0))
(declare-const b3 Int)
(assert (= b3 b1))
(push)
(assert (not (=> (not b0) (> b3 0))))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel (progIfStmtDebug |>
      inlineContinuations |>
      letAssignToLetAssume |>
      ifToPushPop
    )

inductive StmtExpr (I: Type): Type where
/- Statement like -/
  | IfThenElse (cond : StmtExpr I) (thenBranch : StmtExpr I) (elseBranch : Option (StmtExpr I))
  | Block (statements : List (StmtExpr I)) (label : Option I)
  | Exit (target: I)
  /- The initializer must be set if this StmtExpr is pure -/
  | LocalVariable (name : I) (type : LTy) (initializer : Option (StmtExpr I))
  | Assign (target value : StmtExpr I)
  | Assert (condition: StmtExpr I)
  | Assume (condition: StmtExpr I)
  | LiteralInt (i: Int)
  | Identifier (name: I)
deriving Repr

mutual
partial def translateToNLExprList
  (c: Context String)
  (frameBVars: List (String × Nat))
  (continueClosure: Option (LExpr LTy String))
  (remaining: List (StmtExpr String)): LExpr LTy String :=
  match remaining with
  | .Assume condition :: remaining =>
    .assume (translateToNLExpr c condition) (translateToNLExprList c frameBVars continueClosure remaining)
  | [] =>
    match continueClosure with
    | .some v => frameBVars.foldr (fun (name, index) acc => .app acc (.bvar index)) v
    | .none => .skip
  | _ => panic!("Could not do that")

partial def translateToNLExpr (c: Context String) (s: StmtExpr String): LExpr LTy String :=
  match s with
  | .Assume condition =>
    translateToNLExprList c [] .none [s]
  | .Block statements optLabel => -- Translated to a continuation
      let blockLabel :=
        match optLabel with
        | .some label => label
        | .none => "exit"
      let c := c.add blockLabel
      (.abs .none <| translateToNLExprList c (.some (c.v blockLabel)) statements)
  | .LiteralInt i => .const (toString f!"{i}") .none
  | .Identifier name => c.v name
  | _ => panic!("could not do that")
end
/-
var i := 1;
l: {
  // We can't just detect a variable by name
  //
  i := 2;
  var i := 3; // New variable
  i := 4;
  exit l;
}
assert i == 2; // Can be proved

-/
#eval translateToNLExpr .topLevel

end LExpr
end Lambda
