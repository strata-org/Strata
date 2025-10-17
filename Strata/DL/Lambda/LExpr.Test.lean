/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr

namespace Lambda
namespace LExpr

open Std (ToFormat Format format)

/-- info: (((m %2) %1) %0) -/
#guard_msgs in
#eval format <| applyToBvars (fvar "m" .none) 3

-- Only desugaring needed is the .assert
def test: LExpr LTy String  :=
  let_ .topLevel "i" .none <| fun c =>
  .assume (.eq (c.v "i") (.const "0" .none)) <|
  .assert (.eq (c.v "i") (.const "1" .none)) <|
  .skip
/--
info: let λi;
assume (i%0 == #0) <|
assert (i%0 == #1) <|
skip
-/
#guard_msgs in
#eval format test

def testWithoutIf := ifToPushPop test
/--
info: (declare-const i@0 Int)
(assert (= i@0 0))
(push)
(assert (not (= i@0 1)))
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
info: let λi : int := #0;
pushpop (
  assume (~! (i%0 == #1)) <|
  error
) <|
skip
-/
#guard_msgs in
#eval format test2WithoutIf
/--
info: PANIC at Lambda.LExpr.ToSMT Strata.DL.Lambda.LExpr:1378:9: ToSMT not supported:let λi : int := #0;
pushpop (
  assume (~! (i%0 == #1)) <|
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
info: let λi : int;
assume (i%0 == #0) <|
pushpop (
  assume (~! (i%0 == #1)) <|
  error
) <|
skip
-/
#guard_msgs in
#eval format test2WithoutLetAssign
/--
info: (declare-const i@0 Int)
(assert (= i@0 0))
(push)
(assert (not (= i@0 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| test2WithoutLetAssign


/-var i;
  var j;
  var k;
  var i0 := i;
  var j0 := j;
  var k0 := k;
  assume i + j == k;
  assert i == k - j;
  i := i + j + k;
  j := j + k;
  assert i == i0 + j0 + k;
  assert j == j0 + k;
  assert j0 == j - k
  assert i0 == i - (j - k) - k;
  assert i0 == i - j;
  assert k == i0 + j0;
  assert k == (i - j) + (j - k);
  assert k + k == i;-/
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
-- Would be nice to find a monadic style where the context is threaded automatically

/--
info: let λi : int;
let λj : int;
let λk : int;
let λi0 : int := i%2;
let λj0 : int := j%2;
let λk0 : int := k%2;
assume (((~+ i%5) j%4) == k%3) <|
assert (i%5 == ((~- k%3) j%4)) <|
let λi : int := ((~+ i%5) ((~+ j%4) k%3));
let λj : int := ((~+ j%5) k%4);
assert (i%1 == ((~+ i0%4) ((~+ j0%3) k%5))) <|
assert (j%0 == ((~+ j0%3) k%5)) <|
assert (j0%3 == ((~- j%0) k%5)) <|
assert (i0%4 == ((~- ((~- i%1) ((~- j%0) k%5))) k%5)) <|
assert (i0%4 == ((~- i%1) j%0)) <|
assert (k%5 == ((~+ i0%4) j0%3)) <|
assert (k%5 == ((~+ ((~- i%1) j%0)) ((~- j%0) k%5))) <|
assert (((~+ k%5) k%5) == i%1) <|
skip
-/
#guard_msgs in
#eval format prog

/--
info: let λi : int;
let λj : int;
let λk : int;
let λi0 : int;
assume (i0%0 == i%3) <|
let λj0 : int;
assume (j0%0 == j%3) <|
let λk0 : int;
assume (k0%0 == k%3) <|
assume (((~+ i%5) j%4) == k%3) <|
assert (i%5 == ((~- k%3) j%4)) <|
let λi : int;
assume (i%0 == ((~+ i%6) ((~+ j%5) k%4))) <|
let λj : int;
assume (j%0 == ((~+ j%6) k%5)) <|
assert (i%1 == ((~+ i0%4) ((~+ j0%3) k%5))) <|
assert (j%0 == ((~+ j0%3) k%5)) <|
assert (j0%3 == ((~- j%0) k%5)) <|
assert (i0%4 == ((~- ((~- i%1) ((~- j%0) k%5))) k%5)) <|
assert (i0%4 == ((~- i%1) j%0)) <|
assert (k%5 == ((~+ i0%4) j0%3)) <|
assert (k%5 == ((~+ ((~- i%1) j%0)) ((~- j%0) k%5))) <|
assert (((~+ k%5) k%5) == i%1) <|
skip
-/
#guard_msgs in
#eval format <| letAssignToLetAssume <| prog

/--
info: let λi : int;
let λj : int;
let λk : int;
let λi0 : int;
assume (i0%0 == i%3) <|
let λj0 : int;
assume (j0%0 == j%3) <|
let λk0 : int;
assume (k0%0 == k%3) <|
assume (((~+ i%5) j%4) == k%3) <|
pushpop (
  assume (~! (i%5 == ((~- k%3) j%4))) <|
  error
) <|
let λi : int;
assume (i%0 == ((~+ i%6) ((~+ j%5) k%4))) <|
let λj : int;
assume (j%0 == ((~+ j%6) k%5)) <|
pushpop (
  assume (~! (i%1 == ((~+ i0%4) ((~+ j0%3) k%5)))) <|
  error
) <|
pushpop (
  assume (~! (j%0 == ((~+ j0%3) k%5))) <|
  error
) <|
pushpop (
  assume (~! (j0%3 == ((~- j%0) k%5))) <|
  error
) <|
pushpop (
  assume (~! (i0%4 == ((~- ((~- i%1) ((~- j%0) k%5))) k%5))) <|
  error
) <|
pushpop (
  assume (~! (i0%4 == ((~- i%1) j%0))) <|
  error
) <|
pushpop (
  assume (~! (k%5 == ((~+ i0%4) j0%3))) <|
  error
) <|
pushpop (
  assume (~! (k%5 == ((~+ ((~- i%1) j%0)) ((~- j%0) k%5)))) <|
  error
) <|
pushpop (
  assume (~! (((~+ k%5) k%5) == i%1)) <|
  error
) <|
skip
-/
#guard_msgs in
#eval format <| ifToPushPop <| letAssignToLetAssume <| prog
/--
info: (declare-const i@0 Int)
(declare-const j@1 Int)
(declare-const k@2 Int)
(declare-const i0@3 Int)
(assert (= i0@3 i@0))
(declare-const j0@4 Int)
(assert (= j0@4 j@1))
(declare-const k0@5 Int)
(assert (= k0@5 k@2))
(assert (= (+ i@0 j@1) k@2))
(push)
(assert (not (= i@0 (- k@2 j@1))))
(check-sat)
(pop)
(declare-const i@6 Int)
(assert (= i@6 (+ i@0 (+ j@1 k@2))))
(declare-const j@7 Int)
(assert (= j@7 (+ j@1 k@2)))
(push)
(assert (not (= i@6 (+ i0@3 (+ j0@4 k@2)))))
(check-sat)
(pop)
(push)
(assert (not (= j@7 (+ j0@4 k@2))))
(check-sat)
(pop)
(push)
(assert (not (= j0@4 (- j@7 k@2))))
(check-sat)
(pop)
(push)
(assert (not (= i0@3 (- (- i@6 (- j@7 k@2)) k@2))))
(check-sat)
(pop)
(push)
(assert (not (= i0@3 (- i@6 j@7))))
(check-sat)
(pop)
(push)
(assert (not (= k@2 (+ i0@3 j0@4))))
(check-sat)
(pop)
(push)
(assert (not (= k@2 (+ (- i@6 j@7) (- j@7 k@2)))))
(check-sat)
(pop)
(push)
(assert (not (= (+ k@2 k@2) i@6)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| ifToPushPop <| letAssignToLetAssume <| prog

-- Proof or test that letAssignToLetAssume preserves semantics.

def debugSubst: LExpr LTy String :=
    .ite (.const "true" .none)
      (.app (.abs "i" .none (.app (.bvar 1) (.bvar 0 ))) (.const "1" .none))
      (.app (.bvar 0) (.const "0" .none))
def replacement: LExpr LTy String := (.abs "j" .none (.assert (.eq (.bvar 0) (.const "1" .none)) .skip))

/-- info: (if #true then let λi := #1; (%1 i%0) else (%0 #0)) -/
#guard_msgs in
#eval format <| debugSubst
/--
info: (if #true then let λi := #1; let λj := i%0; assert (j%0 == #1) <| skip else let λj := #0; assert (j%0 == #1) <| skip)
-/
#guard_msgs in
#eval format <| subst replacement debugSubst

def test_simplify: LExpr LTy String :=
  .app (.abs "i" .none (.app (.bvar 1) (.bvar 0))) (.const "1" .none)

/--
info: let λi := #1;
(%1 i%0)
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
      assign c "i" _Int (.const "1" .none) <| fun c =>
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
info: let λb : bool;
let λi : int := #0;
((λ@endif (if b%2 then let λi : int := #1; (@endif%1 i%0) else (@endif%0 i%1)))) <| λi
assert (i%0 == #1) <|
skip
-/
#guard_msgs in
#eval format debugIf
/--
info: let λb : bool;
let λi : int;
assume (i%0 == #0) <|
let λ@endif;
assume (@endif%0 == (λi assert (i%0 == #1) <| skip)) <|
(if b%2 then let λi : int; assume (i%0 == #1) <| (@endif%1 i%0) else (@endif%0 i%1))
-/
#guard_msgs in
#eval format <| letAssignToLetAssume <| debugIf
-- This is not working, we need to beta expand continuations, otherwise we won't be able to convert to SMT
-- Also, we currently lack determinism detection.

/--
info: let λb : bool;
((λ@endif (if b%1 then (@endif%0 #1) else (@endif%0 #0)))) <| λi
assert (i%0 == #1) <|
skip
-/
#guard_msgs in
#eval format <| simplify <| debugIf
/--
info: let λb : bool;
let λi : int := #0;
(if b%1 then let λi : int := #1;
   let λi := i%0;
   assert (i%0 == #1) <|
   skip
 else let λi := i%0;
   assert (i%0 == #1) <|
   skip)
-/
#guard_msgs in
#eval format <| inlineContinuations <| debugIf
/--
info: (declare-const b@0 Bool)
(declare-const i@1 Int)
(assert (= i@1 0))
(push)
(assert b@0)
(declare-const i@2 Int)
(assert (= i@2 1))
(declare-const i@3 Int)
(assert (= i@3 i@2))
(push)
(assert (not (= i@3 1)))
(check-sat)
(pop)
(pop)
(assert (not b@0))
(declare-const i@2 Int)
(assert (= i@2 i@1))
(push)
(assert (not (= i@2 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| ifToPushPop <| letAssignToLetAssume <| inlineContinuations <| debugIf
/--
info: let λb : bool;
(if b%0 then assert (#1 == #1) <| skip else assert (#0 == #1) <| skip)
-/
#guard_msgs in
#eval format <| simplify <| inlineContinuations <| simplify <| debugIf
/--
info: (declare-const b@0 Bool)
(push)
(assert b@0)
(push)
(assert (not (= 1 1)))
(check-sat)
(pop)
(pop)
(assert (not b@0))
(push)
(assert (not (= 0 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <| ifToPushPop <| simplify <| inlineContinuations <| simplify <| debugIf

-- HIGHLIGHT
/-
var i: int;
if i != 1 {
  i := 1
  var i := 2
}
assert i == 1
-/
def ifWithLocalVar: LExpr LTy String :=
  let c := .topLevel
  let_ c "i" _Int <| fun c =>
  if_ c c.frame (fun c => neq (c.v "i") (.const "1" .none)) (
  then_ := fun exit c =>
    assign c "i" _Int (.const "1" .none) <| fun c: Context String =>
    let_assign c "i" _Int (.const "2" .none) <| fun c =>
    exit c) (
  else_ := fun exit c =>
    exit c) <| fun c =>
  assert (eq (c.v "i") (.const "1" .none)) skip

/--
info: (declare-const i@0 Int)
(push)
(assert (distinct i@0 1))
(declare-const i@1 Int)
(assert (= i@1 1))
(declare-const i@2 Int)
(assert (= i@2 2))
(declare-const i@3 Int)
(assert (= i@3 i@0))
(push)
(assert (not (= i@3 1)))
(check-sat)
(pop)
(pop)
(assert (not (distinct i@0 1)))
(declare-const i@1 Int)
(assert (= i@1 i@0))
(push)
(assert (not (= i@1 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <|
      ifToPushPop <|
      letAssignToLetAssume <|
      inlineContinuations <|
      ifWithLocalVar

-- Debug issue
/-
var i: int;
if i == 1 {
  var i := 2
}
assert i == 1
-/
def ifWithLocalVar2: LExpr LTy String :=
  let c := .topLevel
  let_ c "i" _Int <| fun c =>
  if_ c c.frame (fun c => neq (c.v "i") (.const "1" .none)) (
  then_ := fun exit c =>
    let_assign c "i" _Int (.const "2" .none) <| fun c =>
    exit c) (
  else_ := fun exit c =>
    exit c) <| fun c =>
  assert (eq (c.v "i") (.const "1" .none)) skip

/--
info: let λi : int;
((λ@endif (if ((~!= i%1) #1) then let λi : int := #2; (@endif%1 i%2) else (@endif%0 i%1)))) <| λi
assert (i%0 == #1) <|
skip
-/
#guard_msgs in
#eval format ifWithLocalVar2

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
info: let λsuperDiscount : bool;
let λdiscount : bool;
let λprice : int;
let λprice0 : int := price%0;
let λdiscountAmount : int;
let λquantity : int;
assume ((~> discountAmount%1) #0) <|
assume ((~> price%3) #0) <|
((λ@endif (if discount%5 then let λprice : int := ((~- price%4) discountAmount%2);
    (@endif%1 price%5)
  else (@endif%0 price%4)))) <| λprice
((λ@endif (if ((~&& superDiscount%7) ((~> price%1) discountAmount%3)) then let λprice : int := ((~- price%1) discountAmount%3);
    (@endif%1 price%2)
  else (@endif%0 price%1)))) <| λprice
assert ((~==> (~! discount%6)) ((~> price%0) #0)) <|
assert ((~==> ((~< discountAmount%3) price0%4)) ((~> price%0) #0)) <|
((λ@endif (if ((~< price%1) price0%5) then ((λ@endif (if (~! discount%8) then assert superDiscount%9 <|
        @endif%0
      else @endif%0))) <|
    assert ((~|| discount%7) superDiscount%8) <|
    @endif%0
  else @endif%0))) <|
assert ((~==> ((~< price%0) price0%4)) ((~|| discount%6) superDiscount%7)) <|
assert ((~==> ((~< price%0) #0)) ((~&& discount%6) ((~> discountAmount%3) price%0))) <|
((λ@endif (if ((~> price%1) price0%5) then assert #false <| assume #false <| @endif%0 else @endif%0))) <|
skip
-/
#guard_msgs in
#eval format progIfStmt

/--
info: let λsuperDiscount : bool;
let λdiscount : bool;
let λprice : int;
let λprice0 : int := price%0;
let λdiscountAmount : int;
let λquantity : int;
assume ((~> discountAmount%1) #0) <|
assume ((~> price%3) #0) <|
(if discount%4 then let λprice : int := ((~- price%3) discountAmount%1);
   let λprice := price%4;
   (if ((~&& superDiscount%7) ((~> price%0) discountAmount%3)) then let λprice : int := ((~- price%0) discountAmount%3);
      let λprice := price%1;
      assert ((~==> (~! discount%8)) ((~> price%0) #0)) <|
      assert ((~==> ((~< discountAmount%5) price0%6)) ((~> price%0) #0)) <|
      (if ((~< price%0) price0%6) then (if (~! discount%8) then assert superDiscount%9 <|
            assert ((~|| discount%8) superDiscount%9) <|
            assert ((~==> ((~< price%0) price0%6)) ((~|| discount%8) superDiscount%9)) <|
            assert ((~==> ((~< price%0) #0)) ((~&& discount%8) ((~> discountAmount%5) price%0))) <|
            (if ((~> price%0) price0%6) then assert #false <| assume #false <| skip else skip)
          else assert ((~|| discount%8) superDiscount%9) <|
            assert ((~==> ((~< price%0) price0%6)) ((~|| discount%8) superDiscount%9)) <|
            assert ((~==> ((~< price%0) #0)) ((~&& discount%8) ((~> discountAmount%5) price%0))) <|
            (if ((~> price%0) price0%6) then assert #false <| assume #false <| skip else skip))
       else assert ((~==> ((~< price%0) price0%6)) ((~|| discount%8) superDiscount%9)) <|
         assert ((~==> ((~< price%0) #0)) ((~&& discount%8) ((~> discountAmount%5) price%0))) <|
         (if ((~> price%0) price0%6) then assert #false <| assume #false <| skip else skip))
    else let λprice := price%0;
      assert ((~==> (~! discount%7)) ((~> price%0) #0)) <|
      assert ((~==> ((~< discountAmount%4) price0%5)) ((~> price%0) #0)) <|
      (if ((~< price%0) price0%5) then (if (~! discount%7) then assert superDiscount%8 <|
            assert ((~|| discount%7) superDiscount%8) <|
            assert ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8)) <|
            assert ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0))) <|
            (if ((~> price%0) price0%5) then assert #false <| assume #false <| skip else skip)
          else assert ((~|| discount%7) superDiscount%8) <|
            assert ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8)) <|
            assert ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0))) <|
            (if ((~> price%0) price0%5) then assert #false <| assume #false <| skip else skip))
       else assert ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8)) <|
         assert ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0))) <|
         (if ((~> price%0) price0%5) then assert #false <| assume #false <| skip else skip)))
 else let λprice := price%3;
   (if ((~&& superDiscount%6) ((~> price%0) discountAmount%2)) then let λprice : int := ((~- price%0) discountAmount%2);
      let λprice := price%1;
      assert ((~==> (~! discount%7)) ((~> price%0) #0)) <|
      assert ((~==> ((~< discountAmount%4) price0%5)) ((~> price%0) #0)) <|
      (if ((~< price%0) price0%5) then (if (~! discount%7) then assert superDiscount%8 <|
            assert ((~|| discount%7) superDiscount%8) <|
            assert ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8)) <|
            assert ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0))) <|
            (if ((~> price%0) price0%5) then assert #false <| assume #false <| skip else skip)
          else assert ((~|| discount%7) superDiscount%8) <|
            assert ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8)) <|
            assert ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0))) <|
            (if ((~> price%0) price0%5) then assert #false <| assume #false <| skip else skip))
       else assert ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8)) <|
         assert ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0))) <|
         (if ((~> price%0) price0%5) then assert #false <| assume #false <| skip else skip))
    else let λprice := price%0;
      assert ((~==> (~! discount%6)) ((~> price%0) #0)) <|
      assert ((~==> ((~< discountAmount%3) price0%4)) ((~> price%0) #0)) <|
      (if ((~< price%0) price0%4) then (if (~! discount%6) then assert superDiscount%7 <|
            assert ((~|| discount%6) superDiscount%7) <|
            assert ((~==> ((~< price%0) price0%4)) ((~|| discount%6) superDiscount%7)) <|
            assert ((~==> ((~< price%0) #0)) ((~&& discount%6) ((~> discountAmount%3) price%0))) <|
            (if ((~> price%0) price0%4) then assert #false <| assume #false <| skip else skip)
          else assert ((~|| discount%6) superDiscount%7) <|
            assert ((~==> ((~< price%0) price0%4)) ((~|| discount%6) superDiscount%7)) <|
            assert ((~==> ((~< price%0) #0)) ((~&& discount%6) ((~> discountAmount%3) price%0))) <|
            (if ((~> price%0) price0%4) then assert #false <| assume #false <| skip else skip))
       else assert ((~==> ((~< price%0) price0%4)) ((~|| discount%6) superDiscount%7)) <|
         assert ((~==> ((~< price%0) #0)) ((~&& discount%6) ((~> discountAmount%3) price%0))) <|
         (if ((~> price%0) price0%4) then assert #false <| assume #false <| skip else skip))))
-/
#guard_msgs in
#eval format (progIfStmt |>
      inlineContinuations
    )

/--
info: let λsuperDiscount : bool;
let λdiscount : bool;
let λprice : int;
let λprice0 : int;
assume (price0%0 == price%1) <|
let λdiscountAmount : int;
let λquantity : int;
assume ((~> discountAmount%1) #0) <|
assume ((~> price%3) #0) <|
pushpop (
  assume discount%4 <|
  let λprice : int;
  assume (price%0 == ((~- price%4) discountAmount%2)) <|
  let λprice;
  assume (price%0 == price%5) <|
  pushpop (
    assume ((~&& superDiscount%7) ((~> price%0) discountAmount%3)) <|
    let λprice : int;
    assume (price%0 == ((~- price%1) discountAmount%4)) <|
    let λprice;
    assume (price%0 == price%2) <|
    pushpop (
      assume (~! ((~==> (~! discount%8)) ((~> price%0) #0))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< discountAmount%5) price0%6)) ((~> price%0) #0))) <|
      error
    ) <|
    pushpop (
      assume ((~< price%0) price0%6) <|
      pushpop (
        assume (~! discount%8) <|
        pushpop (
          assume (~! superDiscount%9) <|
          error
        ) <|
        pushpop (
          assume (~! ((~|| discount%8) superDiscount%9)) <|
          error
        ) <|
        pushpop (
          assume (~! ((~==> ((~< price%0) price0%6)) ((~|| discount%8) superDiscount%9))) <|
          error
        ) <|
        pushpop (
          assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%8) ((~> discountAmount%5) price%0)))) <|
          error
        ) <|
        pushpop (
          assume ((~> price%0) price0%6) <|
          pushpop (
            assume (~! #false) <|
            error
          ) <|
          assume #false <|
          skip
        ) <|
        assume (~! ((~> price%0) price0%6)) <|
        skip
      ) <|
      assume (~! (~! discount%8)) <|
      pushpop (
        assume (~! ((~|| discount%8) superDiscount%9)) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< price%0) price0%6)) ((~|| discount%8) superDiscount%9))) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%8) ((~> discountAmount%5) price%0)))) <|
        error
      ) <|
      pushpop (
        assume ((~> price%0) price0%6) <|
        pushpop (
          assume (~! #false) <|
          error
        ) <|
        assume #false <|
        skip
      ) <|
      assume (~! ((~> price%0) price0%6)) <|
      skip
    ) <|
    assume (~! ((~< price%0) price0%6)) <|
    pushpop (
      assume (~! ((~==> ((~< price%0) price0%6)) ((~|| discount%8) superDiscount%9))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%8) ((~> discountAmount%5) price%0)))) <|
      error
    ) <|
    pushpop (
      assume ((~> price%0) price0%6) <|
      pushpop (
        assume (~! #false) <|
        error
      ) <|
      assume #false <|
      skip
    ) <|
    assume (~! ((~> price%0) price0%6)) <|
    skip
  ) <|
  assume (~! ((~&& superDiscount%7) ((~> price%0) discountAmount%3))) <|
  let λprice;
  assume (price%0 == price%1) <|
  pushpop (
    assume (~! ((~==> (~! discount%7)) ((~> price%0) #0))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< discountAmount%4) price0%5)) ((~> price%0) #0))) <|
    error
  ) <|
  pushpop (
    assume ((~< price%0) price0%5) <|
    pushpop (
      assume (~! discount%7) <|
      pushpop (
        assume (~! superDiscount%8) <|
        error
      ) <|
      pushpop (
        assume (~! ((~|| discount%7) superDiscount%8)) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8))) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0)))) <|
        error
      ) <|
      pushpop (
        assume ((~> price%0) price0%5) <|
        pushpop (
          assume (~! #false) <|
          error
        ) <|
        assume #false <|
        skip
      ) <|
      assume (~! ((~> price%0) price0%5)) <|
      skip
    ) <|
    assume (~! (~! discount%7)) <|
    pushpop (
      assume (~! ((~|| discount%7) superDiscount%8)) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0)))) <|
      error
    ) <|
    pushpop (
      assume ((~> price%0) price0%5) <|
      pushpop (
        assume (~! #false) <|
        error
      ) <|
      assume #false <|
      skip
    ) <|
    assume (~! ((~> price%0) price0%5)) <|
    skip
  ) <|
  assume (~! ((~< price%0) price0%5)) <|
  pushpop (
    assume (~! ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0)))) <|
    error
  ) <|
  pushpop (
    assume ((~> price%0) price0%5) <|
    pushpop (
      assume (~! #false) <|
      error
    ) <|
    assume #false <|
    skip
  ) <|
  assume (~! ((~> price%0) price0%5)) <|
  skip
) <|
assume (~! discount%4) <|
let λprice;
assume (price%0 == price%4) <|
pushpop (
  assume ((~&& superDiscount%6) ((~> price%0) discountAmount%2)) <|
  let λprice : int;
  assume (price%0 == ((~- price%1) discountAmount%3)) <|
  let λprice;
  assume (price%0 == price%2) <|
  pushpop (
    assume (~! ((~==> (~! discount%7)) ((~> price%0) #0))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< discountAmount%4) price0%5)) ((~> price%0) #0))) <|
    error
  ) <|
  pushpop (
    assume ((~< price%0) price0%5) <|
    pushpop (
      assume (~! discount%7) <|
      pushpop (
        assume (~! superDiscount%8) <|
        error
      ) <|
      pushpop (
        assume (~! ((~|| discount%7) superDiscount%8)) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8))) <|
        error
      ) <|
      pushpop (
        assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0)))) <|
        error
      ) <|
      pushpop (
        assume ((~> price%0) price0%5) <|
        pushpop (
          assume (~! #false) <|
          error
        ) <|
        assume #false <|
        skip
      ) <|
      assume (~! ((~> price%0) price0%5)) <|
      skip
    ) <|
    assume (~! (~! discount%7)) <|
    pushpop (
      assume (~! ((~|| discount%7) superDiscount%8)) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0)))) <|
      error
    ) <|
    pushpop (
      assume ((~> price%0) price0%5) <|
      pushpop (
        assume (~! #false) <|
        error
      ) <|
      assume #false <|
      skip
    ) <|
    assume (~! ((~> price%0) price0%5)) <|
    skip
  ) <|
  assume (~! ((~< price%0) price0%5)) <|
  pushpop (
    assume (~! ((~==> ((~< price%0) price0%5)) ((~|| discount%7) superDiscount%8))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%7) ((~> discountAmount%4) price%0)))) <|
    error
  ) <|
  pushpop (
    assume ((~> price%0) price0%5) <|
    pushpop (
      assume (~! #false) <|
      error
    ) <|
    assume #false <|
    skip
  ) <|
  assume (~! ((~> price%0) price0%5)) <|
  skip
) <|
assume (~! ((~&& superDiscount%6) ((~> price%0) discountAmount%2))) <|
let λprice;
assume (price%0 == price%1) <|
pushpop (
  assume (~! ((~==> (~! discount%6)) ((~> price%0) #0))) <|
  error
) <|
pushpop (
  assume (~! ((~==> ((~< discountAmount%3) price0%4)) ((~> price%0) #0))) <|
  error
) <|
pushpop (
  assume ((~< price%0) price0%4) <|
  pushpop (
    assume (~! discount%6) <|
    pushpop (
      assume (~! superDiscount%7) <|
      error
    ) <|
    pushpop (
      assume (~! ((~|| discount%6) superDiscount%7)) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< price%0) price0%4)) ((~|| discount%6) superDiscount%7))) <|
      error
    ) <|
    pushpop (
      assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%6) ((~> discountAmount%3) price%0)))) <|
      error
    ) <|
    pushpop (
      assume ((~> price%0) price0%4) <|
      pushpop (
        assume (~! #false) <|
        error
      ) <|
      assume #false <|
      skip
    ) <|
    assume (~! ((~> price%0) price0%4)) <|
    skip
  ) <|
  assume (~! (~! discount%6)) <|
  pushpop (
    assume (~! ((~|| discount%6) superDiscount%7)) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< price%0) price0%4)) ((~|| discount%6) superDiscount%7))) <|
    error
  ) <|
  pushpop (
    assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%6) ((~> discountAmount%3) price%0)))) <|
    error
  ) <|
  pushpop (
    assume ((~> price%0) price0%4) <|
    pushpop (
      assume (~! #false) <|
      error
    ) <|
    assume #false <|
    skip
  ) <|
  assume (~! ((~> price%0) price0%4)) <|
  skip
) <|
assume (~! ((~< price%0) price0%4)) <|
pushpop (
  assume (~! ((~==> ((~< price%0) price0%4)) ((~|| discount%6) superDiscount%7))) <|
  error
) <|
pushpop (
  assume (~! ((~==> ((~< price%0) #0)) ((~&& discount%6) ((~> discountAmount%3) price%0)))) <|
  error
) <|
pushpop (
  assume ((~> price%0) price0%4) <|
  pushpop (
    assume (~! #false) <|
    error
  ) <|
  assume #false <|
  skip
) <|
assume (~! ((~> price%0) price0%4)) <|
skip
-/
#guard_msgs in
#eval format (progIfStmt |>
      inlineContinuations |>
      letAssignToLetAssume |>
      ifToPushPop
    )

/--
info: (declare-const superDiscount@0 Bool)
(declare-const discount@1 Bool)
(declare-const price@2 Int)
(declare-const price0@3 Int)
(assert (= price0@3 price@2))
(declare-const discountAmount@4 Int)
(declare-const quantity@5 Int)
(assert (> discountAmount@4 0))
(assert (> price@2 0))
(push)
(assert discount@1)
(declare-const price@6 Int)
(assert (= price@6 (- price@2 discountAmount@4)))
(declare-const price@7 Int)
(assert (= price@7 price@2))
(push)
(assert (and superDiscount@0 (> price@7 discountAmount@4)))
(declare-const price@8 Int)
(assert (= price@8 (- price@7 discountAmount@4)))
(declare-const price@9 Int)
(assert (= price@9 price@7))
(push)
(assert (not (=> (not discount@1) (> price@9 0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< discountAmount@4 price0@3) (> price@9 0))))
(check-sat)
(pop)
(push)
(assert (< price@9 price0@3))
(push)
(assert (not discount@1))
(push)
(assert (not superDiscount@0))
(check-sat)
(pop)
(push)
(assert (not (or discount@1 superDiscount@0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@9 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@9 0) (and discount@1 (> discountAmount@4 price@9)))))
(check-sat)
(pop)
(push)
(assert (> price@9 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@9 price0@3)))

(pop)
(assert (not (not discount@1)))
(push)
(assert (not (or discount@1 superDiscount@0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@9 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@9 0) (and discount@1 (> discountAmount@4 price@9)))))
(check-sat)
(pop)
(push)
(assert (> price@9 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@9 price0@3)))

(pop)
(assert (not (< price@9 price0@3)))
(push)
(assert (not (=> (< price@9 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@9 0) (and discount@1 (> discountAmount@4 price@9)))))
(check-sat)
(pop)
(push)
(assert (> price@9 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@9 price0@3)))

(pop)
(assert (not (and superDiscount@0 (> price@7 discountAmount@4))))
(declare-const price@8 Int)
(assert (= price@8 price@7))
(push)
(assert (not (=> (not discount@1) (> price@8 0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< discountAmount@4 price0@3) (> price@8 0))))
(check-sat)
(pop)
(push)
(assert (< price@8 price0@3))
(push)
(assert (not discount@1))
(push)
(assert (not superDiscount@0))
(check-sat)
(pop)
(push)
(assert (not (or discount@1 superDiscount@0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 0) (and discount@1 (> discountAmount@4 price@8)))))
(check-sat)
(pop)
(push)
(assert (> price@8 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@8 price0@3)))

(pop)
(assert (not (not discount@1)))
(push)
(assert (not (or discount@1 superDiscount@0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 0) (and discount@1 (> discountAmount@4 price@8)))))
(check-sat)
(pop)
(push)
(assert (> price@8 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@8 price0@3)))

(pop)
(assert (not (< price@8 price0@3)))
(push)
(assert (not (=> (< price@8 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 0) (and discount@1 (> discountAmount@4 price@8)))))
(check-sat)
(pop)
(push)
(assert (> price@8 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@8 price0@3)))

(pop)
(assert (not discount@1))
(declare-const price@6 Int)
(assert (= price@6 price@2))
(push)
(assert (and superDiscount@0 (> price@6 discountAmount@4)))
(declare-const price@7 Int)
(assert (= price@7 (- price@6 discountAmount@4)))
(declare-const price@8 Int)
(assert (= price@8 price@6))
(push)
(assert (not (=> (not discount@1) (> price@8 0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< discountAmount@4 price0@3) (> price@8 0))))
(check-sat)
(pop)
(push)
(assert (< price@8 price0@3))
(push)
(assert (not discount@1))
(push)
(assert (not superDiscount@0))
(check-sat)
(pop)
(push)
(assert (not (or discount@1 superDiscount@0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 0) (and discount@1 (> discountAmount@4 price@8)))))
(check-sat)
(pop)
(push)
(assert (> price@8 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@8 price0@3)))

(pop)
(assert (not (not discount@1)))
(push)
(assert (not (or discount@1 superDiscount@0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 0) (and discount@1 (> discountAmount@4 price@8)))))
(check-sat)
(pop)
(push)
(assert (> price@8 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@8 price0@3)))

(pop)
(assert (not (< price@8 price0@3)))
(push)
(assert (not (=> (< price@8 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@8 0) (and discount@1 (> discountAmount@4 price@8)))))
(check-sat)
(pop)
(push)
(assert (> price@8 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@8 price0@3)))

(pop)
(assert (not (and superDiscount@0 (> price@6 discountAmount@4))))
(declare-const price@7 Int)
(assert (= price@7 price@6))
(push)
(assert (not (=> (not discount@1) (> price@7 0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< discountAmount@4 price0@3) (> price@7 0))))
(check-sat)
(pop)
(push)
(assert (< price@7 price0@3))
(push)
(assert (not discount@1))
(push)
(assert (not superDiscount@0))
(check-sat)
(pop)
(push)
(assert (not (or discount@1 superDiscount@0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@7 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@7 0) (and discount@1 (> discountAmount@4 price@7)))))
(check-sat)
(pop)
(push)
(assert (> price@7 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@7 price0@3)))

(pop)
(assert (not (not discount@1)))
(push)
(assert (not (or discount@1 superDiscount@0)))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@7 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@7 0) (and discount@1 (> discountAmount@4 price@7)))))
(check-sat)
(pop)
(push)
(assert (> price@7 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@7 price0@3)))

(pop)
(assert (not (< price@7 price0@3)))
(push)
(assert (not (=> (< price@7 price0@3) (or discount@1 superDiscount@0))))
(check-sat)
(pop)
(push)
(assert (not (=> (< price@7 0) (and discount@1 (> discountAmount@4 price@7)))))
(check-sat)
(pop)
(push)
(assert (> price@7 price0@3))
(push)
(assert (not false))
(check-sat)
(pop)
(assert false)

(pop)
(assert (not (> price@7 price0@3)))
-/
#guard_msgs in
#eval ToSMT .topLevel (progIfStmt |>
      inlineContinuations |>
      letAssignToLetAssume |>
      ifToPushPop
    )

-- HIGHLIGHT: Simple inout procedure
/-
procedure f(inout counter) {
  counter := 2;
}
let counter: Int := 3;
f(counter);
assert counter == 2
-/
def procedureCallDebug: LExpr LTy String :=
  let c := .topLevel
  procedure c "f" [("counter", _Int), ("f#out", .none)] (fun c =>
    assign c "counter" _Int (.const "2" .none) <| fun c =>
    .app (c.v "f#out") (c.v "counter")
  ) <| fun c =>
  let_assign c "counter" _Int (.const "3" .none) <| fun c =>
  call1_1 c "f" (c.v "counter") "counter" <| fun c =>
  assert (eq (c.v "counter") (.const "2" .none)) <|
  skip

/--
info: let λf := (λcounter:int (λf#out let λcounter : int := #2; (f#out%1 counter%0)));
let λcounter : int := #3;
((f%1 counter%0) (λcounter assert (counter%0 == #2) <| skip))
-/
#guard_msgs in
#eval format procedureCallDebug

-- Note how the 3 does not even appear in the final SMT file !
/--
info: (declare-const counter@0 Int)
(assert (= counter@0 2))
(push)
(assert (not (= counter@0 2)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <|
      ifToPushPop <|
      letAssignToLetAssume <|
      inlineContinuations <|
      simplify <|
      inlineContinuations <|
      procedureCallDebug

/-
procedure f(inout counter) {
  let inc: Int := *;
  assume 0 <= inc <= 2
  counter := counter + inc;
}
let counter: Int := 3;
f(counter);
f(counter)
assert 3 <= counter <= 7
assert counter == 3 || counter == 5 || counter == 7  // Cannot be prove with true non-determinism
-/
def procedureCall: LExpr LTy String :=
  let c := .topLevel
  procedure c "f" (("counter", _Int) :: ("f_return", .none) :: []) (fun c =>
    let_ c "inc" _Int <| fun c =>
    assume (and (le (.const "0" .none) (c.v "inc")) (le (c.v "inc") (.const "2" .none))) <|
    assign c "counter" _Int (plus (c.v "counter") (c.v "inc")) <| fun c =>
    call1 c "f_return" (c.v "counter")
  ) <| fun c =>
  let_assign c "counter" _Int (.const "3" .none) <| fun c =>
  call1_1 c "f" (c.v "counter") (out := "counter") <| fun c =>
  call1_1 c "f" (c.v "counter") (out := "counter") <| fun c =>
  assert (and (le (.const "3" .none) (c.v "counter")) (le (c.v "counter") (.const "7" .none))) <|
  assert (or (or (eq (c.v "counter") (.const "3" .none))
                 (eq (c.v "counter") (.const "5" .none)))
             (eq (c.v "counter") (.const "3" .none)))
  skip

-- HIGHLIGHT
/--
info: let λf := (λcounter:int (λf_return let λinc : int;
    assume ((~&& ((~<= #0) inc%0)) ((~<= inc%0) #2)) <|
    let λcounter : int := ((~+ counter%2) inc%0);
    (f_return%2 counter%0)));
let λcounter : int := #3;
((f%1 counter%0) (λcounter ((f%2 counter%0) (λcounter assert ((~&& ((~<= #3) counter%0)) ((~<= counter%0) #7)) <|
    assert ((~|| ((~|| (counter%0 == #3)) (counter%0 == #5))) (counter%0 == #3)) <|
    skip))))
-/
#guard_msgs in
#eval format procedureCall


/--
info: (declare-const inc@0 Int)
(assert (and (<= 0 inc@0) (<= inc@0 2)))
(declare-const counter@1 Int)
(assert (= counter@1 (+ 3 inc@0)))
(declare-const inc@2 Int)
(assert (and (<= 0 inc@2) (<= inc@2 2)))
(declare-const counter@3 Int)
(assert (= counter@3 (+ counter@1 inc@2)))
(push)
(assert (not (and (<= 3 counter@3) (<= counter@3 7))))
(check-sat)
(pop)
(push)
(assert (not (or (or (= counter@3 3) (= counter@3 5)) (= counter@3 3))))
(check-sat)
(pop)
-/
#guard_msgs in
#eval ToSMT .topLevel <|
      ifToPushPop <|
      letAssignToLetAssume <|
      simplify <|
      inlineContinuations <|
      simplify <|
      inlineContinuations <|
      procedureCall

-- HIGHLIGHT: api use case
/-Error because does not start with "arn:":
  iam.simulate_principal_policy(PolicySourceArn='user/someone')

  -- We need to be able to have symbol types.
  -- Methods in python have one argument which contains all the arguments. Above, the argument is passed as
  -- [PolicySourceArn := 'user/someone']
  -- Similarly, objects are lambdas accepting a symbol and returning procedures.
  -- We need to define a fix point however if some procedures are mutually recursive.
-/
def apiProg :=
  let c := .topLevel
  procedure c "iam.simulate_principal_policy" (("PolicySourceArn", _String) :: ("out", .none) :: []) (fun c =>
    assert (
      opcall2 "regexmatch"
        (c.v "PolicySourceArn")
        (opcall2 "regexconcat"
          (opcall1 "regexfromstring" (.const "\"arn:\"" _String))
          (opcall1 "regexstar" (.op "regexallchar" .none)))) <|
    call1 c "out" (.choose _Int)) <| fun c =>
  call1_1 c "iam.simulate_principal_policy" (.const "\"user/policy\"" _String) "out_discard" <| fun c =>
  call1_1 c "iam.simulate_principal_policy" (.const "\"arn:policy\"" _String) "out_discard" <| fun _ =>
  skip

/--
info: (set-logic QF_S)
(push)
(assert (not (str.in_re "user/policy" (re.++ (str.to_re "arn:") (re.* re.allchar)))))
(check-sat)
(pop)
(declare-const out_discard@0 Int)
(push)
(assert (not (str.in_re "arn:policy" (re.++ (str.to_re "arn:") (re.* re.allchar)))))
(check-sat)
(pop)
(declare-const out_discard@1 Int)
-/
#guard_msgs in
#eval Format.append f!"(set-logic QF_S){Format.line}" <| ToSMT .topLevel <|
      ifToPushPop <|
      letAssignToLetAssume <|
      simplify <|
      inlineContinuations <|
      simplify <|
      inlineContinuations <|
      apiProg


-- HIGHLIGHT: Abstractions from methods to contracts

/-
function f(i: int) returns (j: int)
  requires 0 <= i
  ensures i < j
{
  i + 1
}
var out := f 2
assert 2 < out  -- Can prove
assert out == 3 -- Can't prove with rewriting
-/
def method_with_contracts: LExpr LTy String :=
  let c := .topLevel
  procedure c "f" [("i", _Int)] (fun c =>
    .assert (le (.const "0" .none) (c.v "i")) <|
    c.ensures .none (plus (c.v "i") (.const "1" .none)) <| fun c =>
      c.procedure_lambda "j" _Int (fun c => lt (c.v "i") (c.v "j"))
  ) <| fun c =>
  let_assign c "f_out" _Int (call1 c "f" (.const "2" .none)) <| fun c =>
  assert (lt (.const "2" .none) (c.v "f_out")) -- can't prove
  <|
  assert (.eq (c.v "f_out") (.const "3" .none)) -- can't prove
  skip


/--
info: let λf := (λi:int assert ((~<= #0) i%0) <|
   let λres := ((~+ i%0) #1);
   assert let λj : int := res%0;
   ((~< i%2) j%0) <|
   res%0);
let λf_out : int := (f%0 #2);
assert ((~< #2) f_out%0) <|
assert (f_out%0 == #3) <|
skip
-/
#guard_msgs in
#eval format <|
  method_with_contracts

-- Now we split the implementation from the contract
/--
info: let λf := let λi : int;
  assume ((~<= #0) i%0) <|
  let λres := ((~+ i%0) #1);
  assert let λj : int := res%0;
  ((~< i%2) j%0) <|
  res%0;
let λf := (λi:int assert ((~<= #0) i%0) <| let λres; assume let λj : int := res%0; ((~< i%2) j%0) <| res%0);
let λf_out : int := (f%0 #2);
assert ((~< #2) f_out%0) <|
assert (f_out%0 == #3) <|
skip
-/
#guard_msgs in
#eval format <|
  replaceByContract <|
  method_with_contracts

-- HIGHLIGHT: This is the generated code for verifying both the function contract and its inlining.
-- Notably, out of the four asserts, the last one is not verified (sat) because the contract is more abstract
/--
info: (declare-const i@0 Int)
(assert (<= 0 i@0))
(declare-const res@1 Int)
(assert (= res@1 (+ i@0 1)))
(push)
(assert (not (< i@0 res@1)))
(check-sat)
(pop)
(push)
(assert (not (<= 0 2)))
(check-sat)
(pop)
(declare-const res@2 Int)
(assert (< 2 res@2))
(push)
(assert (not (< 2 res@2)))
(check-sat)
(pop)
(push)
(assert (not (= res@2 3)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval --format <|
  ToSMT .topLevel <|
  ifToPushPop <|
  letAssignToLetAssume <|
  simplify <|
  functionBodiesToVerification <|
  simplify <|
  inlineContinuations <|
  replaceByContract <|
  method_with_contracts
-- TODO: Go to the SMT level for full demo.
-- Need to detect f is not used so we convert it to pushpop just to verify it does not crash

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
/-
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
      let c := c.add_declare blockLabel
      (.abs .none <| translateToNLExprList c (.some (c.v blockLabel)) statements)
  | .LiteralInt i => .const (toString f!"{i}") .none
  | .Identifier name => c.v name
  | _ => panic!("could not do that")
end
-/
-- #eval translateToNLExpr .topLevel

end LExpr
end Lambda
