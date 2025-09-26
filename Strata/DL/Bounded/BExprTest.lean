import Strata.DL.Bounded.BExpr
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.LTy

-- Tests

namespace Test
open Std (ToFormat Format format)
open Lambda
open Bounded

-- NOTE: with a semantics for LExpr/LExprT, we could prove the equivalences mentioned above

def natTy : LMonoTy := LMonoTy.bounded (.ble (.bconst 0) .bvar)
def leOp (e1 e2: LExprT String) : LExprT String := .app (.app (LFunc.opExprT intLeFunc) e1 (.arrow .int .bool)) e2 .bool

def geOp (e1 e2: LExprT String) : LExprT String := .app (.app (LFunc.opExprT intGeFunc) e1 (.arrow .int .bool)) e2 .bool

def addOp (e1 e2: LExprT String) : LExprT String := .app (.app (LFunc.opExprT intAddFunc) e1 (.arrow .int .int)) e2 .int

def mulOp (e1 e2: LExprT String) : LExprT String := .app (.app (LFunc.opExprT intMulFunc) e1 (.arrow .int .int)) e2 .int

def notOp (e: LExprT String) : LExprT String := .app (LFunc.opExprT boolNotFunc) e .bool

-- easier to read
def eraseTy (x: LExprT String) :=
  LExpr.eraseTypes (LExprT.toLExpr x)

def eraseTys l := List.map eraseTy l

namespace TranslateTest

-- 1. ∀ (x: Nat), 0 <= x (quantified assumption)
-- Expected: ∀ (x: int), 0 <= x -> 0 <= x

def test1 := (@LExprT.quant String .all natTy (.bvar 0 natTy) (leOp (.const "0" .int) (.bvar 0 .int)))

/-- info: Lambda.LExpr.quant
  (Lambda.QuantifierKind.all)
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.bvar 0)
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op "Bool.Implies" none)
      (Lambda.LExpr.app
        (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
        (Lambda.LExpr.bvar 0)))
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.bvar 0)))
      -/
#guard_msgs in
#eval (eraseTy (translateBounded' test1) )

-- 2. λ(x: Nat), if 0 <= x then 1 else 2 (assumption inside ite)
-- Expected: λ (x: int), if 0 <= x -> 0 <= x then 1 else 2

def test2 : LExprT String := .abs (.ite (leOp (.const "0" .int) (.bvar 0 .int)) (.const "1" .int) (.const "2" .int) .int) (.arrow natTy .int)

/-- info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.ite
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op "Bool.Implies" none)
        (Lambda.LExpr.app
          (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
          (Lambda.LExpr.bvar 0)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
        (Lambda.LExpr.bvar 0)))
    (Lambda.LExpr.const "1" none)
    (Lambda.LExpr.const "2" none))-/
#guard_msgs in
#eval (eraseTy (translateBounded' test2))

-- 3. λ(x: int), if foo x >= 0 then 1 else 0 (for foo: int -> Nat) (propagate op/application information)
-- Expected: λ (x: int), if 0 <= foo x -> foo x >= 0 then 1 else 0

def test3 : LExprT String := .abs (.ite (geOp (.app (.op "foo" (.arrow .int natTy)) (.bvar 0 .int) natTy) (.const "0" .int)) (.const "1" .int) (.const "0" .int) .int) (.arrow .int .int)

/-- info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.ite
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op "Bool.Implies" none)
        (Lambda.LExpr.app
          (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
          (Lambda.LExpr.app (Lambda.LExpr.op "foo" none) (Lambda.LExpr.bvar 0))))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op "Int.Ge" none)
          (Lambda.LExpr.app (Lambda.LExpr.op "foo" none) (Lambda.LExpr.bvar 0)))
        (Lambda.LExpr.const "0" none)))
    (Lambda.LExpr.const "1" none)
    (Lambda.LExpr.const "0" none))-/
#guard_msgs in
#eval (eraseTy (translateBounded' test3))

-- 4. (x: Nat) + (y: Nat) >= 0 (free variable bounds)
-- Expected: 0 <= (x: int) -> 0 <= (y : int) -> x + y >= 0

def test4 : LExprT String := geOp (addOp (.fvar "x" natTy) (.fvar "y" natTy)) (.const "0" .int)

/-- info: Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.fvar "x" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op "Bool.Implies" none)
      (Lambda.LExpr.app
        (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
        (Lambda.LExpr.fvar "y" none)))
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op "Int.Ge" none)
        (Lambda.LExpr.app
          (Lambda.LExpr.app (Lambda.LExpr.op "Int.Add" none) (Lambda.LExpr.fvar "x" none))
          (Lambda.LExpr.fvar "y" none)))
      (Lambda.LExpr.const "0" none)))-/
#guard_msgs in
#eval eraseTy (translateBounded' test4)

-- 5. λ (x: Nat). λ (y: Nat). x + y >= 0 (multiple bound vars)
-- Expected: λ (x: int). λ (y: int). 0 <= y -> 0 <= x -> x + y >= 0

def test5 : LExprT String := .abs (.abs (geOp (addOp (.bvar 1 .int) (.bvar 0 .int)) (.const "0" .int)) (.arrow natTy .bool)) (.arrow natTy (.arrow natTy .bool))

/-- info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.abs
    (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op "Bool.Implies" none)
        (Lambda.LExpr.app
          (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
          (Lambda.LExpr.bvar 0)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op "Bool.Implies" none)
          (Lambda.LExpr.app
            (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
            (Lambda.LExpr.bvar 1)))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op "Int.Ge" none)
            (Lambda.LExpr.app
              (Lambda.LExpr.app (Lambda.LExpr.op "Int.Add" none) (Lambda.LExpr.bvar 1))
              (Lambda.LExpr.bvar 0)))
          (Lambda.LExpr.const "0" none)))))-/
#guard_msgs in
#eval eraseTy (translateBounded' test5)

-- 6. λ (x: Nat), if foo then λ (y: Nat). not (x = -1) else λ (y: Nat). x + y >= 0 (propagate inside branches of if-then-else)
--Expected: λ (x: int), if 0 <= x -> foo then λ (y: int), 0 <= y -> 0 <= x -> not (x = -1) else λ (y: int). 0 <= y -> 0 <= x -> x + y >= 0

def test6 : LExprT String := .abs (.ite (.op "foo" .bool) (.abs (notOp (.eq (.bvar 1 .int) (.const "-1" .int) .bool)) (.arrow natTy .bool)) (.abs (geOp (addOp (.bvar 1 .int) (.bvar 0 .int)) (.const "0" .int)) (.arrow natTy .bool)) (.arrow natTy .bool)) (.arrow natTy (.arrow natTy .bool))

/-- info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.ite
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op "Bool.Implies" none)
        (Lambda.LExpr.app
          (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
          (Lambda.LExpr.bvar 0)))
      (Lambda.LExpr.op "foo" none))
    (Lambda.LExpr.abs
      (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op "Bool.Implies" none)
          (Lambda.LExpr.app
            (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
            (Lambda.LExpr.bvar 0)))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op "Bool.Implies" none)
            (Lambda.LExpr.app
              (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
              (Lambda.LExpr.bvar 1)))
          (Lambda.LExpr.app
            (Lambda.LExpr.op "Bool.Not" none)
            (Lambda.LExpr.eq (Lambda.LExpr.bvar 1) (Lambda.LExpr.const "-1" none))))))
    (Lambda.LExpr.abs
      (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op "Bool.Implies" none)
          (Lambda.LExpr.app
            (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
            (Lambda.LExpr.bvar 0)))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op "Bool.Implies" none)
            (Lambda.LExpr.app
              (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
              (Lambda.LExpr.bvar 1)))
          (Lambda.LExpr.app
            (Lambda.LExpr.app
              (Lambda.LExpr.op "Int.Ge" none)
              (Lambda.LExpr.app
                (Lambda.LExpr.app (Lambda.LExpr.op "Int.Add" none) (Lambda.LExpr.bvar 1))
                (Lambda.LExpr.bvar 0)))
            (Lambda.LExpr.const "0" none))))))-/
#guard_msgs in
#eval eraseTy (translateBounded' test6)

end TranslateTest

-- Tests for wf conditions

-- For these tests, we initialize with an empty TEnv
def runWFTest (e: LExprT String) := do
  let (l, _) ← boundedWfConditions TEnv.default e;
  .ok (eraseTys l)

namespace WFTest

-- 1. constant: (1: Nat)
-- Expected: 0 <= 1

def test1 : LExprT String := .const "1" natTy

/--info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
  (Lambda.LExpr.const "1" none)]
   -/
#guard_msgs in
#eval runWFTest test1

-- 2. application: (λ x: Nat. x) 1
-- Expected: 0 <= 1

def test2 : LExprT String := .app (.abs (.bvar 0 .int) (.arrow natTy .int)) (.const "1" .int) .int

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
  (Lambda.LExpr.const "1" none)]-/
#guard_msgs in
#eval runWFTest test2

-- 3. application with assumption (bottom up): (λ x: Nat. x) (foo : Nat)
-- Expected: 0 <= foo -> 0 <= foo

def test3 : LExprT String := .app (.abs (.bvar 0 .int) (.arrow natTy .int)) (.op "foo" natTy) .int

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.op "foo" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
    (Lambda.LExpr.op "foo" none))]-/
#guard_msgs in
#eval runWFTest test3

-- 4. application with assumption (top down): (λ x: Nat. (λ y: Nat. y) x)
-- Expected: 0 <= x -> 0 <= x (no quantifiers)

def test4 : LExprT String := .abs (.app (.abs (.bvar 0 .int) (.arrow natTy .int)) (.bvar 0 .int) .int) (.arrow natTy .int)

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.fvar "$__var0" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
    (Lambda.LExpr.fvar "$__var0" none))]-/
#guard_msgs in
#eval runWFTest test4

-- 5. abstraction with assumption: (λ x: Nat. foo (x + 1)) (foo: Nat -> int)
-- Expected: 0 <= x -> 0 <= x + 1

def test5 : LExprT String := .abs (.app (.op "foo" (.arrow natTy .int)) (addOp (.bvar 0 .int) (.const "1" .int)) .int) (.arrow natTy .int)

/--info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.fvar "$__var0" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Add" none) (Lambda.LExpr.fvar "$__var0" none))
      (Lambda.LExpr.const "1" none)))]-/
#guard_msgs in
#eval runWFTest test5

-- 6. quantified assumption: (∃ x: Nat. foo x) where (foo: Nat -> int)
-- Expected: 0 <= x -> 0 <= x

def test6 : LExprT String := .quant .exist natTy (.bvar 0 .int) (.app (.op "foo" (.arrow natTy .int)) (.bvar 0 .int) .int)

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.fvar "$__var0" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
    (Lambda.LExpr.fvar "$__var0" none))]-/
#guard_msgs in
#eval runWFTest test6

-- 7. Lambda with bounded body (λ x: Nat. (x + 1: Nat))
-- Expected: 0 <= x -> 0 <= x + 1

def test7 : LExprT String := .abs (addOp (.bvar 0 .int) (.const "1" .int)) (.arrow natTy natTy)

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.fvar "$__var0" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Add" none) (Lambda.LExpr.fvar "$__var0" none))
      (Lambda.LExpr.const "1" none)))]-/
#guard_msgs in
#eval runWFTest test7


-- 8. Application with bounded body: (foo x) : Nat where foo: int -> Nat
-- Expected: [] (foo assumed)

def test8 : LExprT String := .app (.op "foo" (.arrow .int natTy)) (.fvar "x" .int) natTy

/-- info: ok: []-/
#guard_msgs in
#eval runWFTest test8

-- 9. Application with bounded body, no assumption: (λ (x: int) . x * x) 1 : Nat
-- Expected: 0 <= (λ (x: int) . x * x) 1

def test9 : LExprT String := .app (.abs (mulOp (.bvar 0 .int) (.bvar 0 .int)) (.arrow .int .int)) (.const "1" .int) natTy

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
  (Lambda.LExpr.app
    (Lambda.LExpr.abs
      (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app (Lambda.LExpr.op "Int.Mul" none) (Lambda.LExpr.bvar 0))
        (Lambda.LExpr.bvar 0)))
    (Lambda.LExpr.const "1" none))]-/
#guard_msgs in
#eval runWFTest test9

-- 10. If-then-else with bounded body: if b then 1 else 0 : Nat
-- Expected: 0 <= if b then 1 else 0

def test10 : LExprT String := .ite (.const "b" .bool) (.const "1" .int) (.const "0" .int) natTy

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
  (Lambda.LExpr.ite (Lambda.LExpr.const "b" none) (Lambda.LExpr.const "1" none) (Lambda.LExpr.const "0" none))]-/
#guard_msgs in
#eval runWFTest test10

-- 11. If-then-else with bound functions: if b then λ (x: int). x * x : Nat else λ (y: int). 0 : Nat (whole type int -> Nat)
-- Expected: 0 <= x * x; 0 <= 0

def test11 : LExprT String := .ite (.const "b" .bool) (.abs (mulOp (.bvar 0 .int) (.bvar 0 .int)) (.arrow .int natTy)) (.abs (.const "0" .int) (.arrow .int natTy)) (.arrow .int natTy)

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Mul" none) (Lambda.LExpr.fvar "$__var1" none))
    (Lambda.LExpr.fvar "$__var1" none)), Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
  (Lambda.LExpr.const "0" none)]-/
#guard_msgs in
#eval runWFTest test11

end WFTest

--tests with more sophisticated bounded types (mostly AI generated)

namespace OtherTest

-- Test 1: Nested bounded function applications
-- Input: add : {x < 10} → {y < 5} → {z < 15}, applied to (3 : {x < 10}) and (2 : {x < 5})
-- Expected: translate = add 3 2, wfCond = [3 < 10, 2 < 5]

def testNestedBoundedApps : LExprT String :=
  .app (.app (.op "add" (.arrow (.bounded (.blt (.bvar) (.bconst 10)))
                               (.arrow (.bounded (.blt (.bvar) (.bconst 5)))
                                      (.bounded (.blt (.bvar) (.bconst 15))))))
            (.const "3" (.bounded (.blt (.bvar) (.bconst 10))))
            (.arrow (.bounded (.blt (.bvar) (.bconst 5))) (.bounded (.blt (.bvar) (.bconst 15)))))
       (.const "2" (.bounded (.blt (.bvar) (.bconst 5))))
       (.bounded (.blt (.bvar) (.bconst 15)))

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.const "2" none))
  (Lambda.LExpr.const "5" none), Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.const "3" none))
  (Lambda.LExpr.const "10" none)]-/
#guard_msgs in
#eval runWFTest testNestedBoundedApps

/-- info: Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "add" none) (Lambda.LExpr.const "3" none))
  (Lambda.LExpr.const "2" none)-/
#guard_msgs in
#eval eraseTy (translateBounded' testNestedBoundedApps)

-- Test 2: Bounded variable in quantifier with complex bound expression
-- Input: ∀ (x : {x < 100 ∧ 0 ≤ x}). x = 42
-- Expected: translate = ∀ x:int. (x < 100 ∧ 0 ≤ x) → (x = 42), wfCond = []

def testComplexBoundInQuantifier : LExprT String :=
  .quant .all (.bounded (.band (.blt (.bvar) (.bconst 100))
                              (.ble (.bconst 0) (.bvar))))
         (.bvar 0 (.bounded (.band (.blt (.bvar) (.bconst 100))
                                  (.ble (.bconst 0) (.bvar)))))
         (.eq (.bvar 0 (.bounded (.band (.blt (.bvar) (.bconst 100))
                                       (.ble (.bconst 0) (.bvar)))))
              (.const "42" .int) .bool)

/-- info: ok: []-/
#guard_msgs in
#eval runWFTest testComplexBoundInQuantifier

/-- info: Lambda.LExpr.quant
  (Lambda.QuantifierKind.all)
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.bvar 0)
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op "Bool.Implies" none)
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op "Bool.And" none)
          (Lambda.LExpr.app
            (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.bvar 0))
            (Lambda.LExpr.const "100" none)))
        (Lambda.LExpr.app
          (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
          (Lambda.LExpr.bvar 0))))
    (Lambda.LExpr.eq (Lambda.LExpr.bvar 0) (Lambda.LExpr.const "42" none)))
-/
#guard_msgs in
#eval eraseTy (translateBounded' testComplexBoundInQuantifier)

-- Test 3: If-then-else with bounded branches and boolean condition
-- Input: if (0 < (getValue 5 : {0 ≤ x})) then (1 : {x < 10}) else (0 : {x < 10}) : {x < 10}
-- Expected: translate = if (0 ≤ getValue 5) → (0 < getValue 5) then 1 else 0, wfCond = [1 < 10, 0 < 10, (if (getValue 5) then 1 else 0) < 10]
def testBoundedIte : LExprT String :=
  .ite (.app (.app (LFunc.opExprT intLtFunc)
                   (.const "0" .int)
                   (.arrow .int .bool))
             (.app (.op "getValue" (.arrow .int (.bounded (.ble (.bconst 0) (.bvar)))))
                   (.const "5" .int)
                   (.bounded (.ble (.bconst 0) (.bvar))))
             .bool)
       (.const "1" (.bounded (.blt (.bvar) (.bconst 10))))
       (.const "0" (.bounded (.blt (.bvar) (.bconst 10))))
       (.bounded (.blt (.bvar) (.bconst 10)))

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Int.Lt" none)
    (Lambda.LExpr.ite
      (Lambda.LExpr.app
        (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.const "0" none))
        (Lambda.LExpr.app (Lambda.LExpr.op "getValue" none) (Lambda.LExpr.const "5" none)))
      (Lambda.LExpr.const "1" none)
      (Lambda.LExpr.const "0" none)))
  (Lambda.LExpr.const "10" none), Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.const "1" none))
  (Lambda.LExpr.const "10" none), Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.const "0" none))
  (Lambda.LExpr.const "10" none)]-/
#guard_msgs in
#eval runWFTest testBoundedIte

/-- info: Lambda.LExpr.ite
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op "Bool.Implies" none)
      (Lambda.LExpr.app
        (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
        (Lambda.LExpr.app (Lambda.LExpr.op "getValue" none) (Lambda.LExpr.const "5" none))))
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.app (Lambda.LExpr.op "getValue" none) (Lambda.LExpr.const "5" none))))
  (Lambda.LExpr.const "1" none)
  (Lambda.LExpr.const "0" none)-/
#guard_msgs in
#eval eraseTy (translateBounded' testBoundedIte)

-- Test 4: Lambda with bounded parameter and bounded return type
-- Input: λ (x : {0 ≤ x}). increment x : {y < 100}
-- Expected: translate = λ x:int. increment x, wfCond = [0 ≤ x → increment x < 100; 0 <= x -> 0 <= x]
def testBoundedLambda : LExprT String :=
  .abs (.app (.op "increment" (.arrow (.bounded (.ble (.bconst 0) (.bvar)))
                                     (.bounded (.blt (.bvar) (.bconst 100)))))
             (.bvar 0 (.bounded (.ble (.bconst 0) (.bvar))))
             (.bounded (.blt (.bvar) (.bconst 100))))
       (.arrow (.bounded (.ble (.bconst 0) (.bvar)))
               (.bounded (.blt (.bvar) (.bconst 100))))

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.fvar "$__var1" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
    (Lambda.LExpr.fvar "$__var1" none)), Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.fvar "$__var0" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op "Int.Lt" none)
      (Lambda.LExpr.app (Lambda.LExpr.op "increment" none) (Lambda.LExpr.fvar "$__var0" none)))
    (Lambda.LExpr.const "100" none))]-/
#guard_msgs in
#eval runWFTest testBoundedLambda

/-- info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.app (Lambda.LExpr.op "increment" none) (Lambda.LExpr.bvar 0))-/
#guard_msgs in
#eval eraseTy (translateBounded' testBoundedLambda)

-- Test 5: Equality between bounded expressions
-- Input: (square (3 : {-10 ≤ x ≤ 10}) : {0 ≤ y}) = (9 : {0 ≤ z})
-- Expected: translate = 0 <= square 3 -> square 3 = 9, wfCond = [-10 ≤ 3 ≤ 10, 0 ≤ 9]
def testBoundedEquality : LExprT String :=
  .eq (.app (.op "square" (.arrow (.bounded (.band (.ble (.bconst (-10)) (.bvar))
                                                  (.ble (.bvar) (.bconst 10))))
                                 (.bounded (.ble (.bconst 0) (.bvar)))))
            (.const "3" (.bounded (.band (.ble (.bconst (-10)) (.bvar))
                                        (.ble (.bvar) (.bconst 10)))))
            (.bounded (.ble (.bconst 0) (.bvar))))
      (.const "9" (.bounded (.ble (.bconst 0) (.bvar))))
      .bool

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.And" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "-10" none))
      (Lambda.LExpr.const "3" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "3" none))
    (Lambda.LExpr.const "10" none)), Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
  (Lambda.LExpr.const "9" none)]-/
#guard_msgs in
#eval runWFTest testBoundedEquality

/-- info: Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.app (Lambda.LExpr.op "square" none) (Lambda.LExpr.const "3" none))))
  (Lambda.LExpr.eq
    (Lambda.LExpr.app (Lambda.LExpr.op "square" none) (Lambda.LExpr.const "3" none))
    (Lambda.LExpr.const "9" none))-/
#guard_msgs in
#eval eraseTy (translateBounded' testBoundedEquality)

-- Test 6: Free variable with bounded type in assumptions
-- Input: compare (x : {x < 50}) 25, with assumption [x < 50]
-- Expected: translate = (x < 50) → compare x 25, wfCond = []
def testFreeVarWithAssumptions : LExprT String :=
  .app (.app (.op "compare" (.arrow .int (.arrow .int .bool)))
             (.fvar "x" (.bounded (.blt (.bvar) (.bconst 50))))
             (.arrow .int .bool))
       (.const "25" .int)
       .bool

/-- info: ok: []-/
#guard_msgs in
#eval runWFTest testFreeVarWithAssumptions

/-- info: Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.fvar "x" none))
      (Lambda.LExpr.const "50" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "compare" none) (Lambda.LExpr.fvar "x" none))
    (Lambda.LExpr.const "25" none))-/
#guard_msgs in
#eval eraseTy (translateBounded' testFreeVarWithAssumptions)

-- Test 7: Metadata preservation with bounded types
-- Input: @metadata(42 : {0 ≤ x < 100})
-- Expected: translate = @metadata(42), wfCond = [0 ≤ 42 < 100]
def testMetadataWithBounds : LExprT String :=
  .mdata (Info.mk "test_info")
         (.const "42" (.bounded (.band (.ble (.bconst 0) (.bvar))
                                      (.blt (.bvar) (.bconst 100)))))

/-- info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.And" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
      (Lambda.LExpr.const "42" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app (Lambda.LExpr.op "Int.Lt" none) (Lambda.LExpr.const "42" none))
    (Lambda.LExpr.const "100" none))]-/
#guard_msgs in
#eval runWFTest testMetadataWithBounds

/-- info: Lambda.LExpr.mdata { value := "test_info" } (Lambda.LExpr.const "42" none)-/
#guard_msgs in
#eval eraseTy (translateBounded' testMetadataWithBounds)

-- Test 8: Chain of bounded function applications
-- Input: f3 (f2 (f1 5 : {x < 10}) : {x < 20}) : {x < 30}
-- Expected: translate = f3 (f2 (f1 5)), wfCond = [f2 (f1 5) < 20 -> f1 5 < 10 → f2 (f1 5) < 20, f1 5 < 10 -> f1 5 < 10]
def testBoundedChain : LExprT String :=
  .app (.op "f3" (.arrow (.bounded (.blt (.bvar) (.bconst 20)))
                        (.bounded (.blt (.bvar) (.bconst 30)))))
       (.app (.op "f2" (.arrow (.bounded (.blt (.bvar) (.bconst 10)))
                              (.bounded (.blt (.bvar) (.bconst 20)))))
             (.app (.op "f1" (.arrow .int (.bounded (.blt (.bvar) (.bconst 10)))))
                   (.const "5" .int)
                   (.bounded (.blt (.bvar) (.bconst 10))))
             (.bounded (.blt (.bvar) (.bconst 20))))
       (.bounded (.blt (.bvar) (.bconst 30)))

/--info: ok: [Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op "Int.Lt" none)
        (Lambda.LExpr.app
          (Lambda.LExpr.op "f2" none)
          (Lambda.LExpr.app (Lambda.LExpr.op "f1" none) (Lambda.LExpr.const "5" none))))
      (Lambda.LExpr.const "20" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op "Bool.Implies" none)
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op "Int.Lt" none)
          (Lambda.LExpr.app (Lambda.LExpr.op "f1" none) (Lambda.LExpr.const "5" none)))
        (Lambda.LExpr.const "10" none)))
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op "Int.Lt" none)
        (Lambda.LExpr.app
          (Lambda.LExpr.op "f2" none)
          (Lambda.LExpr.app (Lambda.LExpr.op "f1" none) (Lambda.LExpr.const "5" none))))
      (Lambda.LExpr.const "20" none))), Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op "Bool.Implies" none)
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op "Int.Lt" none)
        (Lambda.LExpr.app (Lambda.LExpr.op "f1" none) (Lambda.LExpr.const "5" none)))
      (Lambda.LExpr.const "10" none)))
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op "Int.Lt" none)
      (Lambda.LExpr.app (Lambda.LExpr.op "f1" none) (Lambda.LExpr.const "5" none)))
    (Lambda.LExpr.const "10" none))]-/
#guard_msgs in
#eval runWFTest testBoundedChain

/-- info: Lambda.LExpr.app
  (Lambda.LExpr.op "f3" none)
  (Lambda.LExpr.app
    (Lambda.LExpr.op "f2" none)
    (Lambda.LExpr.app (Lambda.LExpr.op "f1" none) (Lambda.LExpr.const "5" none)))-/
#guard_msgs in
#eval eraseTy (translateBounded' testBoundedChain)

-- Test 9: Bounded type in boolean context with negation
-- Input: ¬((getValue 10 : {0 ≤ x}) < 5)
-- Expected: translate = (0 ≤ getValue 10) → ¬(getValue 10 < 5), wfCond = []
def testBoundedInBoolContext : LExprT String :=
  .app (LFunc.opExprT boolNotFunc)
       (.app (.app (LFunc.opExprT intLtFunc)
                   (.app (.op "getValue" (.arrow .int (.bounded (.ble (.bconst 0) (.bvar)))))
                         (.const "10" .int)
                         (.bounded (.ble (.bconst 0) (.bvar))))
                   (.arrow .int .bool))
             (.const "5" .int)
             .bool)
       .bool

def foo : LExprT String := (.app (.app (LFunc.opExprT intLtFunc)
                   (.app (.op "getValue" (.arrow .int (.bounded (.ble (.bconst 0) (.bvar)))))
                         (.const "10" .int)
                         (.bounded (.ble (.bconst 0) (.bvar))))
                   (.arrow .int .bool))
             (.const "5" .int)
             .bool)

#eval (eraseTys (translateBounded foo []).assume)

-- NOTE: all bottom-up assumptions need to be kept, even in boolean-valued terms, since they have to go to the top level

--ex: not (foo x < 0) for foo: int -> nat
-- want (I think): 0 <= foo x -> not (foo x < 0) - TRUE
-- we do NOT want: not (0 <= foo x -> foo x < 0) - this is FALSE
-- think we need to collect bottom-up assumptions differently

/-- info: ok: []-/
#guard_msgs in
#eval runWFTest testBoundedInBoolContext
#eval (translateBounded testBoundedInBoolContext []).assume
#eval eraseTy (translateBounded' testBoundedInBoolContext)

end OtherTest

end Test
