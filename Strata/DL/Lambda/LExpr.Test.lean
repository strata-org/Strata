/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr

namespace Lambda
namespace LExpr

open Std (ToFormat Format format)

def noInfo := Info.mk ""

def extract (res: Except String (LExpr LTy String)): LExpr LTy String :=
  match res with
  | .ok e => e
  | .error s => .const ("Error: " ++ s) .none

def build (builder: Stmt LTy String): LExpr LTy String :=
  let res := builder (λ_ => .ok .skip) .topLevel
  extract res

def buildExpr (builder: CELExpr LTy String): LExpr LTy String :=
  let res := builder .topLevel
  extract res

def is_fun_1 (name: String) (inType: CELExpr LTy String) (outType: CELExpr LTy String):=
  (quant_ .all "x" .none (var "x") (implies_ (app_ inType (var "x")) (app_ outType (app_ (var name) (var "x")))))

def is_fun_2 (name: String) (inType1 inType2: CELExpr LTy String) (outType: CELExpr LTy String):=
  (quant_ .all "y" .none (var "y") (implies_ (app_ inType2 (var "y")) (quant_ .all "x" .none (var "x") (implies_ (app_ inType1 (var "x")) (app_ outType (app_ (app_ (var name) (var "x")) (var "y")))))))

-- Arguments quantified are reversed.
def is_fun_n (name: String) (inTypes: List (CELExpr LTy String)) (outType: CELExpr LTy String): CELExpr LTy String :=
  let inside: Nat × CELExpr LTy String :=
    inTypes.foldl (λ(n, acc) _ =>
      (n + 1, app_ acc (λ_ => return .bvar n))
    ) (0, var name)
  let outside :=
    (0, app_ outType inside.snd) |>
      inTypes.foldl (λ(n, acc) inType =>
        let nameArg := s!"x{n}"
        (n + 1, quant_ .all nameArg .none (var nameArg) (implies_ (app_ inType (var nameArg)) acc))
      )
  outside.2

def smtSort :=
  let is_seq := app_ (var "Seq")
  let assume_seq := assume_ ∘ is_seq
  build <|
  let_ "Seq" (.some (LTy.forAll ["t"] (.arrow (.ftvar "t") .bool)))
  ∘ let_ "Seq@Empty" .none
  ∘ assume_seq (var "Seq@Empty")
  ∘ let_ "Seq@Length" .none
  ∘ assume_ (is_fun_1 "Seq@Length" (var "Seq") (fvar_ "Int" .none))
  ∘ assume_ (eq_ (app_ (var "Seq@Length") (var "Seq@Empty")) (const_ "0" .none))
  ∘ let_ "Seq@Concat" .none
  ∘ assume_ (is_fun_2 "Seq@Concat" (var "Seq") (var "Seq") (var "Seq"))
  ∘ assume_ (
    quant_ .all "s1" .none (var "s1") <|
      assume_seq (var "s1") <|
      quant_ .all "s2" .none (app_ (app_ (var "Seq@Concat") (var "s1")) (var "s2")) <|
        assume_seq (var "s2") <|
        eq_ (app_ (var "Seq@Length") (app_ (app_ (var "Seq@Concat") (var "s1")) (var "s2")))
         (plus_ (app_ (var "Seq@Length") (var "s1"))  (app_ (var "Seq@Length") (var "s2")))
  )
  ∘ assert_ (
    eq_ (app_ (var "Seq@Length") (app_ (app_ (var "Seq@Concat") (var "Seq@Empty")) (var "Seq@Empty"))) (const_ "0" .none)
  ) noInfo
  ∘ skip_

/--
info: let λSeq : ∀[t]. (arrow t bool);
let λSeq@Empty;
assume (Seq%1 Seq@Empty%0) <|
let λSeq@Length;
assume (∀ ((~==> (Seq%3 %0)) (Int (Seq@Length%1 %0)))) <|
assume ((Seq@Length%0 Seq@Empty%1) == #0) <|
let λSeq@Concat;
assume (∀ ((~==> (Seq%4 %0)) (∀ ((~==> (Seq%5 %0)) (Seq%5 ((Seq@Concat%2 %0) %1)))))) <|
assume (∀ assume (Seq%4 %0) <|
 (∀ assume (Seq%5 %0) <| ((Seq@Length%3 ((Seq@Concat%2 %1) %0)) == ((~+ (Seq@Length%3 %1)) (Seq@Length%3 %0))))) <|
assert ((Seq@Length%1 ((Seq@Concat%0 Seq@Empty%2) Seq@Empty%2)) == #0) <|
skip
-/
#guard_msgs in
#eval! format <| smtSort

/--
info: (declare-sort Seq@0)
(declare-const Seq@Empty@1 Seq@0)
(declare-fun Seq@Length@2 (Seq@0) Int)
(assert (= (Seq@Length@2 Seq@Empty@1) 0))
(declare-fun Seq@Concat@3 (Seq@0 Seq@0) Seq@0)
(assert (forall ((x4 Seq@0) (x5 Seq@0)) (! (= (Seq@Length@2 (Seq@Concat@3 x4 x5)) (+ (Seq@Length@2 x4) (Seq@Length@2 x5))) :pattern ((Seq@Concat@3 x4 x5)))))
(push)
(assert (not (= (Seq@Length@2 (Seq@Concat@3 Seq@Empty@1 Seq@Empty@1)) 0)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval! format <|
  ToSMT .topLevel <|
  ifToPushPop <|
  smtSort

def inlineDef :=
  let_assign "f" .none (abs_ "x" .none (plus_ (var "x") (const_ "1" .none)))
  ∘ (
  let_assign "g" .none (abs_ "y" .none (plus_ (app_ (var "f") (var "y")) (app_ (var "f") (app_ (var "f") (var "y"))))))
  <| (app_ (var "g") (const_ "2" .none))

/--
info: let λf := (λx ((~+ x%0) #1));
((λg (g%0 #2))) <| λy
((~+ (f%1 y%0)) (f%1 (f%1 y%0)))
-/
#guard_msgs in
#eval! format <|
  buildExpr <|
  inlineDef

/-- info: ((~+ ((~+ #2) #1)) ((~+ ((~+ #2) #1)) #1)) -/
#guard_msgs in
#eval! format <|
  inline_fun_defs <|
  inline_fun_defs <|
  buildExpr <|
  inlineDef

/--datatype Option = Some value cont | None
   let x := Some a 2
   assert x.isSome
   assert x.value == a
-/
def opt := Datatype "Option" [
  ("Some", [("value", _Int), ("cont", _Int)]),
  ("None", [])
] ∘ let_assign "x" .none (app_ (app_ (var "Option.Some") (fvar_ "a" .none)) (const_ "2" .none))
  ∘ assert_ (app_ (var "Option.@IsSome") (var "x")) noInfo
  ∘ assert_ (eq_ (app_ (var "Option.Some.value") (var "x")) (fvar_ "a" .none)) noInfo
  |> build

/-- info: skip -/
#guard_msgs in
#eval! format <|
  simplify <|
  simplify <|
  simplify <|
  simplify <|
  simplify <|
  simplify <|
  opt

def testInlineFunDefs :=
  buildExpr <|
  let_assign "f" .none (abs_ "x" .none (plus_ (var "x") (var "x")))
  <| (plus_ (app_ (var "f") (const_ "0" .none)) (app_ (var "f") (choose_ .none)))

/-- info: ((~+ ((~+ #0) #0)) let λx; ((~+ x%0) x%0)) -/
#guard_msgs in
#eval! format <|
       inline_fun_defs <|
       testInlineFunDefs

def py := buildExpr <|
Datatype "Val" [
  ("ValInt", [("value", _Int)]),
  ("None", [])
] <| (app_ (var "Val.@IsValInt") (app_ (var "Val.ValInt") (const_ "1" .none)))

/-- info: (#true : bool) -/
#guard_msgs in
#eval! format <|
       inline_fun_defs <|
       inline_fun_defs <|
       inline_fun_defs <|
       inline_fun_defs <|
       inline_fun_defs <|
       inline_fun_defs <|
       py

/--
info: assume (#true : bool) <|
skip
-/
#guard_msgs in
#eval! format <| assumeAssertOfNotSMTExpr <| build <| assume_ (λ_ => return build <| let_assign "a" .none (const_ "1" .none))

def fib: CELExpr LTy String :=
  app_ (op_ "fix" .none) <|
  abs_ "continue" _Int <|
    abs_ "n" _Int <|
      ite_ (le_ (var "n") (const_ "1" .none))
        (var "n")
        (plus_ (app_ (var "continue") (minus_ (var "n") (const_ "1" .none)))
              (app_ (var "continue") (minus_ (var "n") (const_ "2" .none))))

-- Ugly but it works !
/--
info: (λn:int (if ((~<= n%0) #1) then n%0
  else ((~+ ((~fix (λcontinue:int (λn:int (if ((~<= n%0) #1) then n%0
           else ((~+ (continue%1 ((~- n%0) #1))) (continue%1 ((~- n%0) #2))))))) ((~- n%0) #1))) ((~fix (λcontinue:int (λn:int (if ((~<= n%0) #1) then n%0
          else ((~+ (continue%1 ((~- n%0) #1))) (continue%1 ((~- n%0) #2))))))) ((~- n%0) #2)))))
-/
#guard_msgs in
#eval! format <|
    unroll_fix 1 <|
    buildExpr <|
    fib

def fib_apply: LExpr LTy String := buildExpr <|
  let_assign "f" .none fib
  <| app_ (var "f") (const_ "1" .none)

-- Much nicer unrolling, which makes it possible to replace `f` by an uninterpreted function if necessary
/--
info: let λf := (~fix (λcontinue:int (λn:int (if ((~<= n%0) #1) then n%0
      else ((~+ (continue%1 ((~- n%0) #1))) (continue%1 ((~- n%0) #2)))))));
let λn : int := #1;
(if ((~<= n%0) #1) then n%0 else ((~+ (f%1 ((~- n%0) #1))) (f%1 ((~- n%0) #2))))
-/
#guard_msgs in
#eval! format <|
    unroll_fix_named 1 <|
    fib_apply

def r := (record [
    ("length", .const "3" .none),
    ("id", .abs .none .none (.bvar 0)),
  ])

def prog := buildExpr <|
  let_assign "c" .none (record_ [
    ("length", const_ "3" .none),
    ("id", abs_ "x" .none (var "x")),
  ]) <|
  ((var "c") |> select_ "length")

/--
info: let λc := {
    length: #3,
    id: (λx x%0)
  };
(c%0 #length)
-/
#guard_msgs in
#eval! format <| prog

/--
info: let λb : bool;
((λ@endif (if b%1 then let λi : int := #2; (@endif%1 #()) else (@endif%0 #())))) <| λ
assert #true <|
skip
-/
#guard_msgs in
#eval! format <| build <|
  let_ "b" _Bool
  ∘ if_ [] (var "b")
    (then_ := let_assign "i" _Int (const_ "2" .none))
    (else_ := skip_)
  ∘ assert_ (const_ "true" .none) noInfo

/- Motivating
var i: Int;
var b: Bool;
label o:
if b {
  i := i + i;
}
assert b ==> i - i@o == i@o
-/

def progMotivating: LExpr LTy String :=
  let_ "i" _Int
  ∘ (let_ "b" _Bool)
  ∘ (label "previous")
  ∘ if_ ["i"] (var "b")
      (then_ := assign "i" _Int (plus_ (var "i") (var "i")))
      (else_ := skip_)
  ∘ (
      let var_old := varAt "previous"
      assert_ (
      implies_ (var "b") (eq_ (minus_ (var "i") (var_old "i"))
      (var_old "i"))) noInfo)
  |>build

/--
info: (declare-const i@0 Int)
(declare-const b@1 Bool)
(push)
(assert b@1)
(push)
(assert (not (=> b@1 (= (- (+ i@0 i@0) i@0) i@0))))
(check-sat)
(pop)
(pop)
(assert (not b@1))
(push)
(assert (not (=> b@1 (= (- i@0 i@0) i@0))))
(check-sat)
(pop)
-/
#guard_msgs in
#eval
  format <|
  ToSMT .topLevel <|
  ifToPushPop <|
  letAssignToLetAssume <|
  simplify <|
  inlineContinuations <|
  progMotivating

/-- info: %0 -/
#guard_msgs in
#eval! format <|
   buildExpr <|
  (λk c => k (c.declare "i"))
  ∘ (label (TypeType := LTy) (Identifier := String) "init")
  <| (varAt "init" "i")

/-- info: %1 -/
#guard_msgs in
#eval!  format <|
   buildExpr <|
  (λk c => k (c.declare "i"))
  ∘ (label (TypeType := LTy) (Identifier := String) "init")
  ∘ (λk c => k (c.declare "i"))
  <| (varAt "init" "i")

-- Only desugaring needed is the .assert
def test: LExpr LTy String  :=
  let_ "i" .none
  ∘ assume_ (eq_ (var "i") (const_ "0" .none))
  ∘ assert_ (eq_ (var "i") (const_ "1" .none)) noInfo
  |> build
/--
info: let λi;
assume (i%0 == #0) <|
assert (i%0 == #1) <|
skip
-/
#guard_msgs in
#eval! format test

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
#eval! ToSMT .topLevel <| testWithoutIf

-- Now assignments need to be desugared into an assumption
def test2: LExpr LTy String  :=
  let_assign "i" _Int (const_ "0" .none)
  ∘ assert_ (eq_ (var "i") (const_ "1" .none)) noInfo
  |> build
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
#eval! format test2WithoutIf

-- This one panics but I'm not sure how to capture it
--#guard_msgs in
--#eval! ToSMT .topLevel <| test2WithoutIf

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
#eval! format test2WithoutLetAssign
/--
info: (declare-const i@0 Int)
(assert (= i@0 0))
(push)
(assert (not (= i@0 1)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval! ToSMT .topLevel <| test2WithoutLetAssign

/-var i;
  var j;
  var k;
  var k0 := k;
  label init:
  assume i + j == k;
  assert i == k - j;
  i := i + j + k;
  j := j + k;
  assert i == i@init + j@init + k;
  assert j == j@init + k;
  assert j@init == j - k
  assert i@init == i - (j - k) - k;
  assert i@init == i - j;
  assert k == i@init + j@init;
  assert k == (i - j) + (j - k);
  assert k + k == i;-/
def progArith: LExpr LTy String :=
  let_ "i" _Int
  ∘ let_ "j" _Int
  ∘ let_ "k" _Int
  ∘ let_assign "k0" _Int (var "k")
  ∘ label "init"
  ∘ assume_ (eq_ (plus_ (var "i") (var "j")) (var "k"))
  ∘ assert_ (eq_ (var "i") (minus_ (var "k") (var "j"))) noInfo
  ∘ let_assign "i" _Int (plus_ (var "i") (plus_ (var "j") (var "k")))
  ∘ let_assign "j" _Int (plus_ (var "j") (var "k"))
  ∘ assert_ (eq_ (var "i") (plus_ (varAt "init" "i") (plus_ (varAt "init" "j") (var "k")))) noInfo
  ∘ assert_ (eq_ (var "j") (plus_ (varAt "init" "j") (var "k"))) noInfo
  ∘ assert_ (eq_ (varAt "init" "j") (minus_ (var "j") (var "k"))) noInfo
  ∘ assert_ (eq_ (varAt "init" "i") (minus_ (minus_ (var "i") (minus_ (var "j") (var "k"))) (var "k"))) noInfo
  --assert (.eq (varAt "init" "i") (minus (var "i") (minus (var "j") (var "k")))) <| -- Wrong encoding of LLM !
  ∘ assert_ (eq_ (varAt "init" "i") (minus_ (var "i") (var "j"))) noInfo
  ∘ assert_ (eq_ (var "k") (plus_ (varAt "init" "i") (varAt "init" "j"))) noInfo
  ∘ assert_ (eq_ (var "k") (plus_ (minus_ (var "i") (var "j")) (minus_ (var "j") (var "k")))) noInfo
  ∘ assert_ (eq_ (plus_ (var "k") (var "k")) (var "i")) noInfo
  |> build
-- Would be nice to find a monadic style where the context is threaded automatically

/--
info: let λi : int;
let λj : int;
let λk : int;
let λk0 : int := k%0;
assume (((~+ i%3) j%2) == k%1) <|
assert (i%3 == ((~- k%1) j%2)) <|
let λi : int := ((~+ i%3) ((~+ j%2) k%1));
let λj : int := ((~+ j%3) k%2);
assert (i%1 == ((~+ i%5) ((~+ j%4) k%3))) <|
assert (j%0 == ((~+ j%4) k%3)) <|
assert (j%4 == ((~- j%0) k%3)) <|
assert (i%5 == ((~- ((~- i%1) ((~- j%0) k%3))) k%3)) <|
assert (i%5 == ((~- i%1) j%0)) <|
assert (k%3 == ((~+ i%5) j%4)) <|
assert (k%3 == ((~+ ((~- i%1) j%0)) ((~- j%0) k%3))) <|
assert (((~+ k%3) k%3) == i%1) <|
skip
-/
#guard_msgs in
#eval! format progArith

/--
info: let λi : int;
let λj : int;
let λk : int;
let λk0 : int;
assume (k0%0 == k%1) <|
assume (((~+ i%3) j%2) == k%1) <|
assert (i%3 == ((~- k%1) j%2)) <|
let λi : int;
assume (i%0 == ((~+ i%4) ((~+ j%3) k%2))) <|
let λj : int;
assume (j%0 == ((~+ j%4) k%3)) <|
assert (i%1 == ((~+ i%5) ((~+ j%4) k%3))) <|
assert (j%0 == ((~+ j%4) k%3)) <|
assert (j%4 == ((~- j%0) k%3)) <|
assert (i%5 == ((~- ((~- i%1) ((~- j%0) k%3))) k%3)) <|
assert (i%5 == ((~- i%1) j%0)) <|
assert (k%3 == ((~+ i%5) j%4)) <|
assert (k%3 == ((~+ ((~- i%1) j%0)) ((~- j%0) k%3))) <|
assert (((~+ k%3) k%3) == i%1) <|
skip
-/
#guard_msgs in
#eval! format <| letAssignToLetAssume <| progArith

/--
info: let λi : int;
let λj : int;
let λk : int;
let λk0 : int;
assume (k0%0 == k%1) <|
assume (((~+ i%3) j%2) == k%1) <|
pushpop (
  assume (~! (i%3 == ((~- k%1) j%2))) <|
  error
) <|
let λi : int;
assume (i%0 == ((~+ i%4) ((~+ j%3) k%2))) <|
let λj : int;
assume (j%0 == ((~+ j%4) k%3)) <|
pushpop (
  assume (~! (i%1 == ((~+ i%5) ((~+ j%4) k%3)))) <|
  error
) <|
pushpop (
  assume (~! (j%0 == ((~+ j%4) k%3))) <|
  error
) <|
pushpop (
  assume (~! (j%4 == ((~- j%0) k%3))) <|
  error
) <|
pushpop (
  assume (~! (i%5 == ((~- ((~- i%1) ((~- j%0) k%3))) k%3))) <|
  error
) <|
pushpop (
  assume (~! (i%5 == ((~- i%1) j%0))) <|
  error
) <|
pushpop (
  assume (~! (k%3 == ((~+ i%5) j%4))) <|
  error
) <|
pushpop (
  assume (~! (k%3 == ((~+ ((~- i%1) j%0)) ((~- j%0) k%3)))) <|
  error
) <|
pushpop (
  assume (~! (((~+ k%3) k%3) == i%1)) <|
  error
) <|
skip
-/
#guard_msgs in
#eval! format <| ifToPushPop <| letAssignToLetAssume <| progArith
/--
info: (declare-const i@0 Int)
(declare-const j@1 Int)
(declare-const k@2 Int)
(declare-const k0@3 Int)
(assert (= k0@3 k@2))
(assert (= (+ i@0 j@1) k@2))
(push)
(assert (not (= i@0 (- k@2 j@1))))
(check-sat)
(pop)
(declare-const i@4 Int)
(assert (= i@4 (+ i@0 (+ j@1 k@2))))
(declare-const j@5 Int)
(assert (= j@5 (+ j@1 k@2)))
(push)
(assert (not (= i@4 (+ i@0 (+ j@1 k@2)))))
(check-sat)
(pop)
(push)
(assert (not (= j@5 (+ j@1 k@2))))
(check-sat)
(pop)
(push)
(assert (not (= j@1 (- j@5 k@2))))
(check-sat)
(pop)
(push)
(assert (not (= i@0 (- (- i@4 (- j@5 k@2)) k@2))))
(check-sat)
(pop)
(push)
(assert (not (= i@0 (- i@4 j@5))))
(check-sat)
(pop)
(push)
(assert (not (= k@2 (+ i@0 j@1))))
(check-sat)
(pop)
(push)
(assert (not (= k@2 (+ (- i@4 j@5) (- j@5 k@2)))))
(check-sat)
(pop)
(push)
(assert (not (= (+ k@2 k@2) i@4)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval! ToSMT .topLevel <| ifToPushPop <| letAssignToLetAssume <| progArith

-- Proof or test that letAssignToLetAssume preserves semantics.

def debugSubst: LExpr LTy String :=
    .ite (.const "true" .none)
      (.app (.abs "i" .none (.app (.bvar 1) (.bvar 0 ))) (.const "1" .none))
      (.app (.bvar 0) (.const "0" .none))
def replacement: LExpr LTy String := (.abs "j" .none (.assert (.eq (.bvar 0) (.const "1" .none)) noInfo .skip))

/-- info: (if #true then let λi := #1; (%1 i%0) else (%0 #0)) -/
#guard_msgs in
#eval! format <| debugSubst
/--
info: (if #true then let λi := #1; let λj := i%0; assert (j%0 == #1) <| skip else let λj := #0; assert (j%0 == #1) <| skip)
-/
#guard_msgs in
#eval! format <| subst replacement debugSubst

def test_simplify: LExpr LTy String :=
  .app (.abs "i" .none (.app (.bvar 1) (.bvar 0))) (.const "1" .none)

/--
info: let λi := #1;
(%1 i%0)
-/
#guard_msgs in
#eval! format test_simplify

/--info: (%0 #1)-/
#guard_msgs in
#eval! format (simplify test_simplify)

def debugIf: LExpr LTy String :=
  let_ "b" _Bool
  ∘ let_assign "i" _Int (const_ "0" .none)
  ∘ if_ ["i"] (var "b")
      (then_ := assign "i" _Int (const_ "1" .none))
      (else_ := skip_)
  ∘ assert_ (eq_ (var "i") (const_ "1" .none)) noInfo
  |> build

/--
info: let λb : bool;
let λi : int := #0;
((λ@endif (if b%2 then let λi : int := #1; (@endif%1 i%0) else (@endif%0 i%1)))) <| λi
assert (i%0 == #1) <|
skip
-/
#guard_msgs in
#eval! format debugIf
/--
info: let λb : bool;
let λi : int;
assume (i%0 == #0) <|
let λ@endif;
assume (@endif%0 == (λi assert (i%0 == #1) <| skip)) <|
(if b%2 then let λi : int; assume (i%0 == #1) <| (@endif%1 i%0) else (@endif%0 i%1))
-/
#guard_msgs in
#eval! format <| letAssignToLetAssume <| debugIf
-- This is not working, we need to beta expand continuations, otherwise we won't be able to convert to SMT
-- Also, we currently lack determinism detection.

/--
info: let λb : bool;
(if b%0 then let λi := #1; assert (i%0 == #1) <| skip else let λi := #0; assert (i%0 == #1) <| skip)
-/
#guard_msgs in
#eval! format <| simplify <| debugIf
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
#eval! format <| inlineContinuations <| debugIf
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
#eval! ToSMT .topLevel <| ifToPushPop <| letAssignToLetAssume <| inlineContinuations <| debugIf
/--
info: let λb : bool;
(if b%0 then assert (#1 == #1) <| skip else assert (#0 == #1) <| skip)
-/
#guard_msgs in
#eval! format <| simplify <| inlineContinuations <| simplify <| debugIf
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
#eval! ToSMT .topLevel <| ifToPushPop <| simplify <| inlineContinuations <| simplify <| debugIf

-- HIGHLIGHT
/-
var b: Bool;
var i: int;
if b {
  i := 1
  var i := i + 2;
  assert i == 3;
}
assert b ==> i == 1
-/
def ifWithLocalVar: LExpr LTy String :=
  let_ "b" _Bool
  ∘ let_ "i" _Int
  ∘ if_ ["i"] (var "b")
      (then_ :=
        assign "i" _Int (const_ "1" .none)
        ∘ let_assign "i" _Int (plus_ (var "i") (const_ "2" .none))
        ∘ assert_ (eq_ (var "i") (const_ "3" .none)) noInfo
      )
      (else_ := skip_)
  ∘ assert_ (implies_ (var "b") (eq_ (var "i") (const_ "1" .none))) noInfo
  |> build


/--
info: let λb : bool;
let λi : int;
((λ@endif (if b%2 then let λi : int := #1;
    let λi : int := ((~+ i%0) #2);
    assert (i%0 == #3) <|
    (@endif%2 i%1)
  else (@endif%0 i%1)))) <| λi
assert ((~==> b%2) (i%0 == #1)) <|
skip
-/
#guard_msgs in
#eval! format <|
  ifWithLocalVar

/--
info: (declare-const b@0 Bool)
(declare-const i@1 Int)
(push)
(assert b@0)
(declare-const i@2 Int)
(assert (= i@2 1))
(declare-const i@3 Int)
(assert (= i@3 (+ i@2 2)))
(push)
(assert (not (= i@3 3)))
(check-sat)
(pop)
(declare-const i@4 Int)
(assert (= i@4 i@2))
(push)
(assert (not (=> b@0 (= i@4 1))))
(check-sat)
(pop)
(pop)
(assert (not b@0))
(declare-const i@2 Int)
(assert (= i@2 i@1))
(push)
(assert (not (=> b@0 (= i@2 1))))
(check-sat)
(pop)
-/
#guard_msgs in
#eval! ToSMT .topLevel <|
      ifToPushPop <|
      letAssignToLetAssume <|
      inlineContinuations <|
      ifWithLocalVar

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
  let_ "superDiscount" _Bool
  ∘ (let_ "discount" _Bool)
  ∘ (let_ "price" _Int)
  ∘ (let_assign "price0" _Int (var "price"))
  ∘ (let_ "discountAmount" _Int)
  ∘ (let_ "quantity" _Int)
  ∘ (assume_ (gt_ (var "discountAmount") (const_ "0" .none)))
  ∘ (assume_ (gt_ (var "price") (const_ "0" .none)))
  ∘ (
    if_ ["price"] (var "discount")
      (then_ := let_assign "price" _Int (minus_ (var "price") (var "discountAmount")))
      (else_ := skip_)
  )
  ∘ (
    if_ ["price"] (and_ (var "superDiscount") (gt_ (var "price") (var "discountAmount")))
      (then_ := let_assign "price" _Int (minus_ (var "price") (var "discountAmount")))
      (else_ := skip_)
  )
  ∘ assert_ (implies_ (not_ (var "discount")) (gt_ (var "price") (const_ "0" .none))) noInfo
  ∘ assert_ (implies_ (lt_ (var "discountAmount") (var "price0")) (gt_ (var "price") (const_ "0" .none))) noInfo
  ∘ (
    if_ [] (lt_ (var "price") (var "price0"))
      (then_ :=
        if_ [] (not_ (var "discount"))
          (then_ := assert_ (var "superDiscount") noInfo)
          (else_ := skip_)
        ∘ assert_ (or_ (var "discount") (var "superDiscount")) noInfo
      )
      (else_ := skip_)
  )
  ∘ assert_ (implies_ (lt_ (var "price") (var "price0")) (or_ (var "discount") (var "superDiscount"))) noInfo
  ∘ assert_ (implies_ (lt_ (var "price") (const_ "0" .none)) (and_ (var "discount") (gt_ (var "discountAmount") (var "price")))) noInfo
  ∘ (
    if_ [] (gt_ (var "price") (var "price0"))
      (then_ :=
        assert_ (const_ "false" .none) noInfo
        ∘ (assume_ (const_ "false" .none))
      )
      (else_ := skip_)
  )
  |> build

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
let λ@endif := (λ assert ((~==> ((~< price%1) price0%5)) ((~|| discount%7) superDiscount%8)) <|
   assert ((~==> ((~< price%1) #0)) ((~&& discount%7) ((~> discountAmount%4) price%1))) <|
   ((λ@endif (if ((~> price%2) price0%6) then assert #false <|
       assume #false <|
       (@endif%0 #())
     else (@endif%0 #())))) <| λ
   skip);
(if ((~< price%1) price0%5) then ((λ@endif (if (~! discount%8) then assert superDiscount%9 <|
       (@endif%0 #())
     else (@endif%0 #())))) <| λ
   assert ((~|| discount%8) superDiscount%9) <|
   (@endif%1 #())
 else (@endif%0 #()))
-/
#guard_msgs in
#eval! format progIfStmt

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
#eval! format (progIfStmt |>
      inlineContinuations |> inlineContinuations
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
#eval! format (progIfStmt |>
      inlineContinuations |>
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
#eval! ToSMT .topLevel (progIfStmt |>
      inlineContinuations |>
      inlineContinuations |>
      letAssignToLetAssume |>
      ifToPushPop
    )

/-
let b: bool;
let i := 1;
label before:
let continueWith := procedure(i) returns (i) {
  if b {
    i := *;
    assume i - i@before == 3;
  } else {
    i := i + 2;
  }
}
if b {
  i := continueWith(i)
} else {
  i := continueWith(i + 1)
}
assert i == i@before + 3
-/
def progInlineProc: LExpr LTy String :=
  let_ "b" _Bool
  ∘ let_assign "i" _Int (const_ "1" .none)
  ∘ label "before"
  ∘ procedure "continueWith" [("i", _Int), ("continueWith_return", .none)] (
      if_ ["i"] (var "b")
        (then_ :=
          assign "i" _Int (choose_ _Int)
          ∘ (assume_ (eq_ (minus_ (var "i") (varAt "before" "i")) (const_ "3" .none)))
        )
        (else_ := assign "i" _Int (plus_ (var "i") (const_ "2" .none)))
      <| (call1 "continueWith_return" (var "i"))
    )
  ∘ if_ ["i"] (var "b")
      (then_ := call1_1 "continueWith" (var "i") (out := "i"))
      (else_ := call1_1 "continueWith" (plus_ (var "i") (const_ "1" .none)) (out := "i"))
  ∘ assert_ (eq_ (var "i") (plus_ (varAt "before" "i") (const_ "3" .none))) noInfo
  |> build

/--
info: (declare-const b@0 Bool)
(push)
(assert b@0)
(push)
(assert b@0)
(declare-const i@1 Int)
(assert (= (- i@1 1) 3))
(push)
(assert (not (= i@1 (+ 1 3))))
(check-sat)
(pop)
(pop)
(assert (not b@0))
(push)
(assert (not (= (+ 1 2) (+ 1 3))))
(check-sat)
(pop)
(pop)
(assert (not b@0))
(push)
(assert b@0)
(declare-const i@1 Int)
(assert (= (- i@1 1) 3))
(push)
(assert (not (= i@1 (+ 1 3))))
(check-sat)
(pop)
(pop)
(assert (not b@0))
(push)
(assert (not (= (+ (+ 1 1) 2) (+ 1 3))))
(check-sat)
(pop)
-/
#guard_msgs in
#eval! format <|
  ToSMT .topLevel <|
  ifToPushPop <|
  letAssignToLetAssume <|
  simplify <|
  simplify <|
  inlineContinuations <|
  progInlineProc

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
  procedure "f" [("counter", _Int), ("f#out", .none)] (
    assign "counter" _Int (const_ "2" .none)
    <| (app_ (var "f#out") (var "counter"))
  )
  ∘ let_assign "counter" _Int (const_ "3" .none)
  ∘ call1_1 "f" (var "counter") "counter"
  ∘ assert_ (eq_ (var "counter") (const_ "2" .none)) noInfo
  |> build

/--
info: let λf := (λcounter:int (λf#out let λcounter : int := #2; (f#out%1 counter%0)));
let λcounter : int := #3;
((f%1 counter%0) (λcounter assert (counter%0 == #2) <| skip))
-/
#guard_msgs in
#eval! format procedureCallDebug

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
#eval! ToSMT .topLevel <|
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
assert counter == 3 || counter == 5 || counter == 7  // Cannot be proved with true non-determinism
-/
def procedureCall: LExpr LTy String :=
  procedure "f" (("counter", _Int) :: ("f_return", .none) :: []) (
    let_ "inc" _Int
    ∘ (assume_ (and_ (le_ (const_ "0" .none) (var "inc")) (le_ (var "inc") (const_ "2" .none))))
    ∘ (assign "counter" _Int (plus_ (var "counter") (var "inc")))
    <| (call1 "f_return" (var "counter"))
  )
  ∘ let_assign "counter" _Int (const_ "3" .none)
  ∘ call1_1 "f" (var "counter") (out := "counter")
  ∘ call1_1 "f" (var "counter") (out := "counter")
  ∘ assert_ (and_ (le_ (const_ "3" .none) (var "counter")) (le_ (var "counter") (const_ "7" .none))) noInfo
  ∘ assert_ (or_ (or_ (eq_ (var "counter") (const_ "3" .none))
                                (eq_ (var "counter") (const_ "5" .none)))
                           (eq_ (var "counter") (const_ "3" .none))) noInfo
  |> build

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
#eval! format procedureCall


/--
info: (declare-const inc@0 Int)
(assert (and (<= 0 inc@0) (<= inc@0 2)))
(declare-const inc@1 Int)
(assert (and (<= 0 inc@1) (<= inc@1 2)))
(push)
(assert (not (and (<= 3 (+ (+ 3 inc@0) inc@1)) (<= (+ (+ 3 inc@0) inc@1) 7))))
(check-sat)
(pop)
(push)
(assert (not (or (or (= (+ (+ 3 inc@0) inc@1) 3) (= (+ (+ 3 inc@0) inc@1) 5)) (= (+ (+ 3 inc@0) inc@1) 3))))
(check-sat)
(pop)
-/
#guard_msgs in
#eval! ToSMT .topLevel <|
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
  procedure "iam.simulate_principal_policy" (("PolicySourceArn", _String) :: ("out", .none) :: []) (
    assert_ (
      opcall2 "regexmatch"
        (var "PolicySourceArn")
        (opcall2 "regexconcat"
          (opcall1 "regexfromstring" (const_ "\"arn:\"" _String))
          (opcall1 "regexstar" (op_ "regexallchar" .none))))
    noInfo <| (call1 "out" (choose_ _Int))
  )
  ∘ call1_1 "iam.simulate_principal_policy" (const_ "\"user/policy\"" _String) "out_discard"
  ∘ call1_1 "iam.simulate_principal_policy" (const_ "\"arn:policy\"" _String) "out_discard"
  |> build

/--
info: let λiam.simulate_principal_policy := (λPolicySourceArn:string (λout assert ((~regexmatch PolicySourceArn%1) ((~regexconcat (~regexfromstring (#"arn:" : string))) (~regexstar ~regexallchar))) <|
    (out%0 ((* : int)))));
((iam.simulate_principal_policy%0 (#"user/policy" : string)) (λout_discard ((iam.simulate_principal_policy%1 (#"arn:policy" : string)) (λout_discard skip))))
-/
#guard_msgs in
#eval! format apiProg
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
#eval! Format.append f!"(set-logic QF_S){Format.line}" <| ToSMT .topLevel <|
      ifToPushPop <|
      letAssignToLetAssume <|
      simplify <|
      inlineContinuations <|
      simplify <|
      inlineContinuations <|
      apiProg


-- HIGHLIGHT: Abstractions from methods to contracts

/-
procedure f(i: int) returns (j: int)
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
  procedure "f" [("i", _Int)] (
    assert_ (le_ (const_ "0" .none) (var "i")) noInfo
    <| (ensures_ .none (plus_ (var "i") (const_ "1" .none)) (abs_ "j" _Int (lt_ (var "i") (var "j"))) noInfo)
  )
  ∘ let_assign "f_out" _Int (call1 "f" (const_ "2" .none))
  ∘ assert_ (lt_ (const_ "2" .none) (var "f_out")) noInfo -- can prove
  ∘ assert_ (eq_ (var "f_out") (const_ "3" .none)) noInfo -- can't prove
  |> build


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
#eval! format <|
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
#eval! format <|
  replaceByContract <|
  method_with_contracts

-- HIGHLIGHT: This is the generated code for verifying both the function contract and its inlining.
-- Notably, out of the four asserts, the last one is not verified (sat) because the contract is more abstract
/--
info: (declare-const i@0 Int)
(assert (<= 0 i@0))
(push)
(assert (not (< i@0 (+ i@0 1))))
(check-sat)
(pop)
(push)
(assert (not (<= 0 2)))
(check-sat)
(pop)
(declare-const res@1 Int)
(assert (< 2 res@1))
(push)
(assert (not (< 2 res@1)))
(check-sat)
(pop)
(push)
(assert (not (= res@1 3)))
(check-sat)
(pop)
-/
#guard_msgs in
#eval! --format <|
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
      let c := c.declare blockLabel
      (.abs .none <| translateToNLExprList c (.some (var blockLabel)) statements)
  | .LiteralInt i => .const (toString f!"{i}") .none
  | .Identifier name => var name
  | _ => panic!("could not do that")
end
-/
-- #eval! translateToNLExpr .topLevel

end LExpr
end Lambda
