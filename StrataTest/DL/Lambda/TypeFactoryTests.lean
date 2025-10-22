/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.IntBoolFactory
import Strata.DL.Lambda.TypeFactory

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)
open LExpr LTy

def getStrs (n: Nat) : List String :=
  List.map (fun x => "e" ++ toString x) (List.range n)

-- Utilities
def strConst (s: String) : LExpr LMonoTy String := .const s (.some .string)
def intConst (n: Nat) : LExpr LMonoTy String := .const (toString n) (.some .int)

/-
We write the tests as pattern matches, even though we use eliminators
-/

-- Test 1: Enum

/-
type day = Su | M | T | W | Th | F | Sa

match W with
| Su => 0
| M => 1
| T => 2
| W => 3
| Th => 4
| F => 5
| Sa => 6
end ==> 3

-/

def weekTy : LDatatype String := {name := "Day", typeArgs := [], constrs := List.map (fun x => {name := x, args := []}) ["Su", "M", "T", "W", "Th", "F", "Sa"]}

/--
info: Annotated expression:
(((((((((~DayElim : (arrow Day (arrow int (arrow int (arrow int (arrow int (arrow int (arrow int (arrow int int))))))))) (~W : Day)) (#0 : int)) (#1 : int)) (#2 : int)) (#3 : int)) (#4 : int)) (#5 : int)) (#6 : int))

---
info: (#3 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval getStrs #[weekTy]  Factory.default ((LExpr.op "DayElim" .none).appMulti (.op "W" (.some (.tcons "Day" [])) :: (List.range 7).map intConst))


-- Test 2: Polymorphic tuples

/-
type Tup a b = Prod a b

fst e = match e with | (x, y) => x
snd e = match e with | (x, y) => y

fst (3, "a") ==> 3
snd (3, "a") ==> "a"
fst (snd ("a", (1, "b"))) ==> 1

-/

def tupTy : LDatatype String := {name := "Tup", typeArgs := ["a", "b"], constrs := [{name := "Prod", args := [("x", .ftvar "a"), ("y", .ftvar "b")]}]}

def fst (e: LExpr LMonoTy String) := (LExpr.op "TupElim" .none).appMulti [e, .abs .none (.abs .none (.bvar 1))]

def snd (e: LExpr LMonoTy String) := (LExpr.op "TupElim" .none).appMulti [e, .abs .none (.abs .none (.bvar 0))]

def prod (e1 e2: LExpr LMonoTy String) : LExpr LMonoTy String := (LExpr.op "Prod" .none).appMulti [e1, e2]

/--
info: Annotated expression:
(((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string int)) int))) (((~Prod : (arrow int (arrow string (Tup int string)))) (#3 : int)) (#a : string))) (λ (λ %1)))

---
info: (#3 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval getStrs #[tupTy]  Factory.default (fst (prod (intConst 3) (strConst "a")))

/--
info: Annotated expression:
(((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string string)) string))) (((~Prod : (arrow int (arrow string (Tup int string)))) (#3 : int)) (#a : string))) (λ (λ %0)))

---
info: (#a : string)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval getStrs #[tupTy]  Factory.default (snd (prod (intConst 3) (strConst "a")))


/--
info: Annotated expression:
(((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string int)) int))) (((~TupElim : (arrow (Tup string (Tup int string)) (arrow (arrow string (arrow (Tup int string) (Tup int string))) (Tup int string)))) (((~Prod : (arrow string (arrow (Tup int string) (Tup string (Tup int string))))) (#a : string)) (((~Prod : (arrow int (arrow string (Tup int string)))) (#1 : int)) (#b : string)))) (λ (λ %0)))) (λ (λ %1)))

---
info: (#1 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval getStrs #[tupTy]  Factory.default (fst (snd (prod (strConst "a") (prod (intConst 1) (strConst "b")))))


-- Test 3: Polymorphic Lists

/-
type List a = | Nil | Cons a (List a)

match Nil with | Nil => 1 | Cons _ _ => 0 end ==> 1
match [2] with | Nil => 0 | Cons x _ => x end ==> 2

-/

def nilConstr : LConstr String := {name := "Nil", args := []}
def consConstr : LConstr String := {name := "Cons", args := [("h", .ftvar "a"), ("t", .tcons "List" [.ftvar "a"])]}
def listTy : LDatatype String := {name := "List", typeArgs := ["a"], constrs := [nilConstr, consConstr]}

/-- info: Annotated expression:
((((~ListElim : (arrow (List $__ty5) (arrow int (arrow (arrow $__ty5 (arrow (List $__ty5) int)) int)))) (~Nil : (List $__ty5))) (#1 : int)) (λ (λ (#0 : int))))

---
info: (#1 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval getStrs #[listTy]  Factory.default ((LExpr.op "ListElim" .none).appMulti [.op "Nil" .none, (intConst 1), .abs .none (.abs .none (intConst 0))])

-- Test: elim(cons 1 nil, 0, fun x y => x) -> (fun x y => x) 1 nil

def consApp (e1 e2: LExpr LMonoTy String) : LExpr LMonoTy String := .app (.app (.op "Cons" .none) e1) e2

/-- info: Annotated expression:
((((~ListElim : (arrow (List int) (arrow int (arrow (arrow int (arrow (List int) int)) int)))) (((~Cons : (arrow int (arrow (List int) (List int)))) (#2 : int)) (~Nil : (List int)))) (#0 : int)) (λ (λ %1)))

---
info: (#2 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval getStrs #[listTy]  Factory.default ((LExpr.op "ListElim" .none).appMulti [consApp (.const "2" (.some .int)) (.op "Nil" .none), intConst 0, .abs .none (.abs .none (bvar 1))])

-- Test 4: Multiple types and Factories

/-
match [(3, "a"), (4, "b")] with
| (x1, y1) :: (x2, y2) :: _ => x1 + x2
| (x, y) :: nil => 1
| nil => 0
end ==> 7
-/

def addOp (e1 e2: LExpr LMonoTy String) : LExpr LMonoTy String := .app (.app (.op intAddFunc.name .none) e1) e2

/-- info: Annotated expression:
((((~ListElim : (arrow (List (Tup int string)) (arrow int (arrow (arrow (Tup int string) (arrow (List (Tup int string)) int)) int)))) (((~Cons : (arrow (Tup int string) (arrow (List (Tup int string)) (List (Tup int string))))) (((~Prod : (arrow int (arrow string (Tup int string)))) (#3 : int)) (#a : string))) (((~Cons : (arrow (Tup int string) (arrow (List (Tup int string)) (List (Tup int string))))) (((~Prod : (arrow int (arrow string (Tup int string)))) (#4 : int)) (#b : string))) (~Nil : (List (Tup int string)))))) (#0 : int)) (λ (λ (((~Int.Add : (arrow int (arrow int int))) (((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string int)) int))) %1) (λ (λ %1)))) ((((~ListElim : (arrow (List (Tup int string)) (arrow int (arrow (arrow (Tup int string) (arrow (List (Tup int string)) int)) int)))) %0) (#1 : int)) (λ (λ (((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string int)) int))) %1) (λ (λ %1))))))))))

---
info: (#7 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval getStrs #[listTy, tupTy]  IntBoolFactory
    ((LExpr.op "ListElim" .none).appMulti
      [consApp (prod (intConst 3) (strConst "a"))
        (consApp (prod (intConst 4) (strConst "b")) (.op "Nil" .none)),
      intConst 0,
      .abs .none (.abs .none
        (addOp (fst (.bvar 1))
          ((LExpr.op "ListElim" .none).appMulti
            [.bvar 0, intConst 1, .abs .none (.abs .none (fst (.bvar 1)))])))])

end Lambda
