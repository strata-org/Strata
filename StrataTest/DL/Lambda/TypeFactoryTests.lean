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

-- Utilities
def strConst (s: String) : LExpr LMonoTy Unit := .const s (.some .string)
def intConst (n: Nat) : LExpr LMonoTy Unit := .const (toString n) (.some .int)

private def absMulti' (n: Nat) (body: LExpr LMonoTy IDMeta) : LExpr LMonoTy IDMeta :=
  List.foldr (fun _ e => .abs .none e) body (List.range n)

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

def weekTy : LDatatype Unit := {name := "Day", typeArgs := [], constrs := List.map (fun x => {name := x, args := []}) ["Su", "M", "T", "W", "Th", "F", "Sa"]}

/--
info: Annotated expression:
(((((((((~DayElim : (arrow Day (arrow int (arrow int (arrow int (arrow int (arrow int (arrow int (arrow int int))))))))) (~W : Day)) (#0 : int)) (#1 : int)) (#2 : int)) (#3 : int)) (#4 : int)) (#5 : int)) (#6 : int))

---
info: (#3 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[weekTy]  Factory.default ((LExpr.op "DayElim" .none).mkApp (.op "W" (.some (.tcons "Day" [])) :: (List.range 7).map intConst))


-- Test 2: Polymorphic tuples

/-
type Tup a b = Prod a b

fst e = match e with | (x, y) => x
snd e = match e with | (x, y) => y

fst (3, "a") ==> 3
snd (3, "a") ==> "a"
fst (snd ("a", (1, "b"))) ==> 1

-/

def tupTy : LDatatype Unit := {name := "Tup", typeArgs := ["a", "b"], constrs := [{name := "Prod", args := [("x", .ftvar "a"), ("y", .ftvar "b")]}]}

def fst (e: LExpr LMonoTy Unit) := (LExpr.op "TupElim" .none).mkApp [e, .abs .none (.abs .none (.bvar 1))]

def snd (e: LExpr LMonoTy Unit) := (LExpr.op "TupElim" .none).mkApp [e, .abs .none (.abs .none (.bvar 0))]

def prod (e1 e2: LExpr LMonoTy Unit) : LExpr LMonoTy Unit := (LExpr.op "Prod" .none).mkApp [e1, e2]

/--
info: Annotated expression:
(((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string int)) int))) (((~Prod : (arrow int (arrow string (Tup int string)))) (#3 : int)) (#a : string))) (λ (λ %1)))

---
info: (#3 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[tupTy]  Factory.default (fst (prod (intConst 3) (strConst "a")))

/--
info: Annotated expression:
(((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string string)) string))) (((~Prod : (arrow int (arrow string (Tup int string)))) (#3 : int)) (#a : string))) (λ (λ %0)))

---
info: (#a : string)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[tupTy]  Factory.default (snd (prod (intConst 3) (strConst "a")))


/--
info: Annotated expression:
(((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string int)) int))) (((~TupElim : (arrow (Tup string (Tup int string)) (arrow (arrow string (arrow (Tup int string) (Tup int string))) (Tup int string)))) (((~Prod : (arrow string (arrow (Tup int string) (Tup string (Tup int string))))) (#a : string)) (((~Prod : (arrow int (arrow string (Tup int string)))) (#1 : int)) (#b : string)))) (λ (λ %0)))) (λ (λ %1)))

---
info: (#1 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[tupTy]  Factory.default (fst (snd (prod (strConst "a") (prod (intConst 1) (strConst "b")))))


-- Test 3: Polymorphic Lists

/-
type List a = | Nil | Cons a (List a)

match Nil with | Nil => 1 | Cons _ _ => 0 end ==> 1
match [2] with | Nil => 0 | Cons x _ => x end ==> 2

-/

def nilConstr : LConstr Unit := {name := "Nil", args := []}
def consConstr : LConstr Unit := {name := "Cons", args := [("h", .ftvar "a"), ("t", .tcons "List" [.ftvar "a"])]}
def listTy : LDatatype Unit := {name := "List", typeArgs := ["a"], constrs := [nilConstr, consConstr]}

-- Syntactic sugar
def cons (e1 e2: LExpr LMonoTy Unit) : LExpr LMonoTy Unit := .app (.app (.op "Cons" .none) e1) e2
def nil : LExpr LMonoTy Unit := .op "Nil" .none

def listExpr (l: List (LExpr LMonoTy Unit)) : LExpr LMonoTy Unit :=
  List.foldr cons nil l

/-- info: Annotated expression:
((((~ListElim : (arrow (List $__ty5) (arrow int (arrow (arrow $__ty5 (arrow (List $__ty5) (arrow int int))) int)))) (~Nil : (List $__ty5))) (#1 : int)) (λ (λ (λ (#1 : int)))))

---
info: (#1 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[listTy]  Factory.default ((LExpr.op "ListElim" .none).mkApp [nil, (intConst 1), .abs .none (.abs .none (.abs none (intConst 1)))])

-- Test: elim(cons 1 nil, 0, fun x y => x) -> (fun x y => x) 1 nil



/-- info: Annotated expression:
((((~ListElim : (arrow (List int) (arrow int (arrow (arrow int (arrow (List int) (arrow int int))) int)))) (((~Cons : (arrow int (arrow (List int) (List int)))) (#2 : int)) (~Nil : (List int)))) (#0 : int)) (λ (λ (λ %2))))

---
info: (#2 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[listTy]  Factory.default ((LExpr.op "ListElim" .none).mkApp [listExpr [.const "2" (.some .int)], intConst 0, .abs .none (.abs .none (.abs none (bvar 2)))])

-- Test 4: Multiple types and Factories

/-
match [(3, "a"), (4, "b")] with
| (x1, y1) :: (x2, y2) :: _ => x1 + x2
| (x, y) :: nil => 1
| nil => 0
end ==> 7
-/

def addOp (e1 e2: LExpr LMonoTy Unit) : LExpr LMonoTy Unit := .app (.app (.op intAddFunc.name .none) e1) e2

/-- info: Annotated expression:
((((~ListElim : (arrow (List (Tup int string)) (arrow int (arrow (arrow (Tup int string) (arrow (List (Tup int string)) (arrow int int))) int)))) (((~Cons : (arrow (Tup int string) (arrow (List (Tup int string)) (List (Tup int string))))) (((~Prod : (arrow int (arrow string (Tup int string)))) (#3 : int)) (#a : string))) (((~Cons : (arrow (Tup int string) (arrow (List (Tup int string)) (List (Tup int string))))) (((~Prod : (arrow int (arrow string (Tup int string)))) (#4 : int)) (#b : string))) (~Nil : (List (Tup int string)))))) (#0 : int)) (λ (λ (λ (((~Int.Add : (arrow int (arrow int int))) (((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string int)) int))) %2) (λ (λ %1)))) ((((~ListElim : (arrow (List (Tup int string)) (arrow int (arrow (arrow (Tup int string) (arrow (List (Tup int string)) (arrow int int))) int)))) %1) (#1 : int)) (λ (λ (λ (((~TupElim : (arrow (Tup int string) (arrow (arrow int (arrow string int)) int))) %2) (λ (λ %1))))))))))))

---
info: (#7 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[listTy, tupTy]  IntBoolFactory
    ((LExpr.op "ListElim" .none).mkApp
      [listExpr [(prod (intConst 3) (strConst "a")), (prod (intConst 4) (strConst "b"))],
      intConst 0,
      .abs .none (.abs .none (.abs none
        (addOp (fst (.bvar 2))
          ((LExpr.op "ListElim" .none).mkApp
            [.bvar 1, intConst 1, .abs .none (.abs .none (.abs none (fst (.bvar 2))))]))))])

-- Recursive tests

-- 1. List length and append

def length (x: LExpr LMonoTy Unit) :=
  (LExpr.op "ListElim" .none).mkApp [x, intConst 0, absMulti' 3 (addOp (intConst 1) (.bvar 0))]

/-- info: Annotated expression:
((((~ListElim : (arrow (List string) (arrow int (arrow (arrow string (arrow (List string) (arrow int int))) int)))) (((~Cons : (arrow string (arrow (List string) (List string)))) (#a : string)) (((~Cons : (arrow string (arrow (List string) (List string)))) (#b : string)) (((~Cons : (arrow string (arrow (List string) (List string)))) (#c : string)) (~Nil : (List string)))))) (#0 : int)) (λ (λ (λ (((~Int.Add : (arrow int (arrow int int))) (#1 : int)) %0)))))

---
info: (#3 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[listTy]  IntBoolFactory (length (listExpr [.const "a" (.some .string), .const "b" (.some .string), .const "c" (.some .string)]))


/-- info: Annotated expression:
((((~ListElim : (arrow (List int) (arrow int (arrow (arrow int (arrow (List int) (arrow int int))) int)))) (((~Cons : (arrow int (arrow (List int) (List int)))) (#0 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#1 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#2 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#3 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#4 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#5 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#6 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#7 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#8 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#9 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#10 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#11 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#12 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#13 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#14 : int)) (~Nil : (List int)))))))))))))))))) (#0 : int)) (λ (λ (λ (((~Int.Add : (arrow int (arrow int int))) (#1 : int)) %0)))))

---
info: (#15 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[listTy]  IntBoolFactory (length (listExpr ((List.range 15).map (fun n => .const (toString n) (.some .int)))))

/-
Append is trickier since it takes in two arguments, so the eliminator returns
a function. We can write it as (using nicer syntax):
l₁ ++ l₂ := (@ListElim (List α → List α) l₁ (fun x => x) (fun x xs rec => fun l₂ => x :: rec l₂)) l₂
-/

def append (l1 l2: LExpr LMonoTy Unit) : LExpr LMonoTy Unit :=
  .app ((LExpr.op "ListElim" .none).mkApp [l1, .abs .none (.bvar 0), absMulti' 3 (.abs .none (cons (.bvar 3) (.app (.bvar 1) (.bvar 0))))]) l2

def list1 :LExpr LMonoTy Unit := listExpr [intConst 2, intConst 4, intConst 6]
def list2 :LExpr LMonoTy Unit := listExpr [intConst 1, intConst 3, intConst 5]

-- The output is difficult to read, but gives [2, 4, 6, 1, 3, 5], as expected

/-- info: Annotated expression:
(((((~ListElim : (arrow (List int) (arrow (arrow (List int) (List int)) (arrow (arrow int (arrow (List int) (arrow (arrow (List int) (List int)) (arrow (List int) (List int))))) (arrow (List int) (List int)))))) (((~Cons : (arrow int (arrow (List int) (List int)))) (#2 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#4 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#6 : int)) (~Nil : (List int)))))) (λ %0)) (λ (λ (λ (λ (((~Cons : (arrow int (arrow (List int) (List int)))) %3) (%1 %0))))))) (((~Cons : (arrow int (arrow (List int) (List int)))) (#1 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#3 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#5 : int)) (~Nil : (List int))))))

---
info: (((~Cons : (arrow int (arrow (List int) (List int)))) (#2 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#4 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#6 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#1 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#3 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#5 : int)) (~Nil : (List int))))))))
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[listTy]  IntBoolFactory (append list1 list2)

-- 2. Preorder traversal of binary tree

/-
type binTree a = | Leaf | Node a (binTree a) (binTree a)

def toList (t: binTree a) =
  match t with
  | Leaf => []
  | Node a l r => a :: (toList l) ++ (toList r)

-/

def leafConstr : LConstr Unit := {name := "Leaf", args := []}
def nodeConstr : LConstr Unit := {name := "Node", args := [("x", .ftvar "a"), ("l", .tcons "binTree" [.ftvar "a"]), ("r", .tcons "binTree" [.ftvar "a"])]}
def binTreeTy : LDatatype Unit := {name := "binTree", typeArgs := ["a"], constrs := [leafConstr, nodeConstr]}

-- syntactic sugar
def node (x l r: LExpr LMonoTy Unit) : LExpr LMonoTy Unit := (LExpr.op "Node" .none).mkApp [x, l, r]
def leaf : LExpr LMonoTy Unit := LExpr.op "Leaf" .none

def toList (t: LExpr LMonoTy Unit) : LExpr LMonoTy Unit :=
  (LExpr.op "binTreeElim" .none).mkApp [t, nil, absMulti' 5 (cons (.bvar 4) (append (.bvar 1) (.bvar 0)))]

/-
tree:
        1
      2   4
    3       5
          6   7

toList gives [1; 2; 3; 4; 5; 6; 7]
-/
def tree1 : LExpr LMonoTy Unit :=
  node (intConst 1)
    (node (intConst 2)
      (node (intConst 3) leaf leaf)
      leaf)
    (node (intConst 4)
      leaf
      (node (intConst 5)
        (node (intConst 6) leaf leaf)
        (node (intConst 7) leaf leaf)))

/-- info: Annotated expression:
((((~binTreeElim : (arrow (binTree int) (arrow (List int) (arrow (arrow int (arrow (binTree int) (arrow (binTree int) (arrow (List int) (arrow (List int) (List int)))))) (List int))))) ((((~Node : (arrow int (arrow (binTree int) (arrow (binTree int) (binTree int))))) (#1 : int)) ((((~Node : (arrow int (arrow (binTree int) (arrow (binTree int) (binTree int))))) (#2 : int)) ((((~Node : (arrow int (arrow (binTree int) (arrow (binTree int) (binTree int))))) (#3 : int)) (~Leaf : (binTree int))) (~Leaf : (binTree int)))) (~Leaf : (binTree int)))) ((((~Node : (arrow int (arrow (binTree int) (arrow (binTree int) (binTree int))))) (#4 : int)) (~Leaf : (binTree int))) ((((~Node : (arrow int (arrow (binTree int) (arrow (binTree int) (binTree int))))) (#5 : int)) ((((~Node : (arrow int (arrow (binTree int) (arrow (binTree int) (binTree int))))) (#6 : int)) (~Leaf : (binTree int))) (~Leaf : (binTree int)))) ((((~Node : (arrow int (arrow (binTree int) (arrow (binTree int) (binTree int))))) (#7 : int)) (~Leaf : (binTree int))) (~Leaf : (binTree int))))))) (~Nil : (List int))) (λ (λ (λ (λ (λ (((~Cons : (arrow int (arrow (List int) (List int)))) %4) (((((~ListElim : (arrow (List int) (arrow (arrow (List int) (List int)) (arrow (arrow int (arrow (List int) (arrow (arrow (List int) (List int)) (arrow (List int) (List int))))) (arrow (List int) (List int)))))) %1) (λ %0)) (λ (λ (λ (λ (((~Cons : (arrow int (arrow (List int) (List int)))) %3) (%1 %0))))))) %0))))))))

---
info: (((~Cons : (arrow int (arrow (List int) (List int)))) (#1 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#2 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#3 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#4 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#5 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#6 : int)) (((~Cons : (arrow int (arrow (List int) (List int)))) (#7 : int)) (~Nil : (List int)))))))))
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[listTy, binTreeTy]  IntBoolFactory (toList tree1)

-- 3. Infinite-ary trees
namespace Tree

/-
type tree a = | Leaf a | Node (Nat -> tree a)

-- Find the length of the n-indexed chain in the tree
def height (n: Nat) (t: tree a) : int =
match t with
| Leaf => 0
| Node f => 1 + height (f n)

Example tree: Node (fun x => Node (fun y => if x + y == 0 then Node (fun _ => Leaf 3) else Leaf 4)) has zero-height 3 (and all other heights 2)

-/

def leafConstr : LConstr Unit := {name := "Leaf", args := [("x", .ftvar "a")]}
def nodeConstr : LConstr Unit := {name := "Node", args := [("f", .arrow .int (.tcons "tree" [.ftvar "a"]))]}
def treeTy : LDatatype Unit := {name := "tree", typeArgs := ["a"], constrs := [leafConstr, nodeConstr]}

-- syntactic sugar
def node (f: LExpr LMonoTy Unit) : LExpr LMonoTy Unit := (LExpr.op "Node" .none).mkApp [f]
def leaf (x: LExpr LMonoTy Unit) : LExpr LMonoTy Unit := (LExpr.op "Leaf" .none).mkApp [x]

def tree1 : LExpr LMonoTy Unit := node (.abs .none (node (.abs .none
  (.ite (.eq (addOp (.bvar 1) (.bvar 0)) (intConst 0))
    (node (.abs .none (leaf (intConst 3))))
    (leaf (intConst 4))
  ))))

def height (n: Nat) (t: LExpr LMonoTy Unit) : LExpr LMonoTy Unit :=
  (LExpr.op "treeElim" .none).mkApp [t, .abs .none (intConst 0), absMulti' 2 (addOp (intConst 1) (.app (.bvar 0) (intConst n)))]

/--info: Annotated expression:
((((~treeElim : (arrow (tree int) (arrow (arrow int int) (arrow (arrow (arrow int (tree int)) (arrow (arrow int int) int)) int)))) ((~Node : (arrow (arrow int (tree int)) (tree int))) (λ ((~Node : (arrow (arrow int (tree int)) (tree int))) (λ (if ((((~Int.Add : (arrow int (arrow int int))) %1) %0) == (#0 : int)) then ((~Node : (arrow (arrow int (tree int)) (tree int))) (λ ((~Leaf : (arrow int (tree int))) (#3 : int)))) else ((~Leaf : (arrow int (tree int))) (#4 : int)))))))) (λ (#0 : int))) (λ (λ (((~Int.Add : (arrow int (arrow int int))) (#1 : int)) (%0 (#0 : int))))))

---
info: (#3 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[treeTy]  IntBoolFactory (height 0 tree1)

/--info: Annotated expression:
((((~treeElim : (arrow (tree int) (arrow (arrow int int) (arrow (arrow (arrow int (tree int)) (arrow (arrow int int) int)) int)))) ((~Node : (arrow (arrow int (tree int)) (tree int))) (λ ((~Node : (arrow (arrow int (tree int)) (tree int))) (λ (if ((((~Int.Add : (arrow int (arrow int int))) %1) %0) == (#0 : int)) then ((~Node : (arrow (arrow int (tree int)) (tree int))) (λ ((~Leaf : (arrow int (tree int))) (#3 : int)))) else ((~Leaf : (arrow int (tree int))) (#4 : int)))))))) (λ (#0 : int))) (λ (λ (((~Int.Add : (arrow int (arrow int int))) (#1 : int)) (%0 (#1 : int))))))

---
info: (#2 : int)
-/
#guard_msgs in
#eval format $
  typeCheckAndPartialEval #[treeTy]  IntBoolFactory (height 1 tree1)

end Tree

-- Typechecking tests

/-
1. Non-positive type
type Bad := | C (Bad -> Bad)
-/

def badConstr1: LConstr Unit := {name := "C", args := [⟨"x", .arrow (.tcons "Bad" []) (.tcons "Bad" [])⟩]}
def badTy1 : LDatatype Unit := {name := "Bad", typeArgs := [], constrs := [badConstr1]}

/-- info: Error in constructor C: Non-strictly positive occurrence of Bad in type (arrow Bad Bad)
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval #[badTy1] IntBoolFactory (.const "0" .none)

/-
2.Non-strictly positive type
type Bad a := | C ((Bad a -> int) -> int)
-/

def badConstr2: LConstr Unit := {name := "C", args := [⟨"x", .arrow (.arrow (.tcons "Bad" [.ftvar "a"]) .int) .int⟩]}
def badTy2 : LDatatype Unit := {name := "Bad", typeArgs := ["a"], constrs := [badConstr2]}

/-- info: Error in constructor C: Non-strictly positive occurrence of Bad in type (arrow (arrow (Bad a) int) int)-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval #[badTy2] IntBoolFactory (.const "0" .none)

/-
3. Non-strictly positive type 2
type Bad a := | C (int -> (Bad a -> int))
-/

def badConstr3: LConstr Unit := {name := "C", args := [⟨"x", .arrow .int (.arrow (.tcons "Bad" [.ftvar "a"]) .int)⟩]}
def badTy3 : LDatatype Unit := {name := "Bad", typeArgs := ["a"], constrs := [badConstr3]}

/--info: Error in constructor C: Non-strictly positive occurrence of Bad in type (arrow (Bad a) int)-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval #[badTy3] IntBoolFactory (.const "0" .none)

/-
4. Strictly positive type
type Good := | C (int -> (int -> Good))
-/

def goodConstr1: LConstr Unit := {name := "C", args := [⟨"x", .arrow .int (.arrow .int (.tcons "Good" [.ftvar "a"]))⟩]}
def goodTy1 : LDatatype Unit := {name := "Good", typeArgs := ["a"], constrs := [goodConstr1]}

/-- info: Annotated expression:
(#0 : int)

---
info: (#0 : int)
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval #[goodTy1] IntBoolFactory (.const "0" .none)

/-
5. Non-uniform type
type Nonunif a := | C (int -> Nonunif (List a))
-/
def nonUnifConstr1: LConstr Unit := {name := "C", args := [⟨"x", .arrow .int (.arrow .int (.tcons "Nonunif" [.tcons "List" [.ftvar "a"]]))⟩]}
def nonUnifTy1 : LDatatype Unit := {name := "Nonunif", typeArgs := ["a"], constrs := [nonUnifConstr1]}

/-- info: Error in constructor C: Non-uniform occurrence of Nonunif, which is applied to [(List a)] when it should be applied to [a]-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval #[listTy, nonUnifTy1] IntBoolFactory (.const "0" .none)

/-
6. Nested types are allowed, though they won't produce a useful elimination principle
type Nest a := | C (List (Nest a))
-/
def nestConstr1: LConstr Unit := {name := "C", args := [⟨"x", .tcons "List" [.tcons "Nest" [.ftvar "a"]]⟩]}
def nestTy1 : LDatatype Unit := {name := "Nest", typeArgs := ["a"], constrs := [nestConstr1]}

/-- info: Annotated expression:
(#0 : int)

---
info: (#0 : int)
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval #[listTy, nestTy1] IntBoolFactory (.const "0" .none)

/-
7. 2 constructors with the same name:
type Bad = | C (int) | C (Bad)
-/

def badConstr4: LConstr Unit := {name := "C", args := [⟨"x", .int⟩]}
def badConstr5: LConstr Unit := {name := "C", args := [⟨"x", .tcons "Bad" [.ftvar "a"]⟩]}
def badTy4 : LDatatype Unit := {name := "Bad", typeArgs := ["a"], constrs := [badConstr4, badConstr5]}

/--
info: A function of name C already exists! Redefinitions are not allowed.
Existing Function: func C : ∀[a]. ((x : int)) → (Bad a);
New Function:func C : ∀[a]. ((x : (Bad a))) → (Bad a);
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval #[badTy4] IntBoolFactory (.const "0" .none)

/-
8. Constructor with same name as function not allowed
type Bad = | Int.add (int)
-/
def badConstr6: LConstr Unit := {name := "Int.Add", args := [⟨"x", .int⟩]}
def badTy5 : LDatatype Unit := {name := "Bad", typeArgs := [], constrs := [badConstr6]}

/-- info: A function of name Int.Add already exists! Redefinitions are not allowed.
Existing Function: func Int.Add :  ((x : int)) → Bad;
New Function:func Int.Add :  ((x : int) (y : int)) → int;-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval #[badTy5] IntBoolFactory (.const "0" .none)

end Lambda
