/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.TypeFactory

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)
open LExpr LTy

def getStrs (n: Nat) : List String :=
  List.map (fun x => "e" ++ toString x) (List.range n)

-- Test 1: Enum

-- Test 2: Polymorphic tuples

-- Test 3: Polymorphic Lists

def nilConstr : LConstr String := {name := "Nil", args := []}
def consConstr : LConstr String := {name := "Cons", args := [("h", .ftvar "a"), ("t", .tcons "List" [.ftvar "a"])]}
def listTy : LDatatype String := {name := "List", typeArgs := ["a"], constrs := [nilConstr, consConstr]}

-- elim(nil, 1, fun _ _ => 0) -> 1

/-- info: Lambda.LExpr.const "1" none-/
#guard_msgs in
#eval (elimConcreteEval listTy (.const "ERROR" .none) [.op "Nil" .none, .const "1" .none, .abs .none (.abs .none (.const "0" .none))])

-- Test: elim(cons 1 nil, 0, fun x y => x) -> (fun x y => x) 1 nil

def consApp (e1 e2: LExpr LMonoTy String) : LExpr LMonoTy String := .app (.app (.op "Cons" .none) e1) e2

/-- info: Lambda.LExpr.app
  (Lambda.LExpr.app (Lambda.LExpr.abs none (Lambda.LExpr.abs none (Lambda.LExpr.bvar 1))) (Lambda.LExpr.const "1" none))
  (Lambda.LExpr.op "Nil" none) -/
#guard_msgs in
#eval (elimConcreteEval listTy (.const "ERROR" .none) [consApp (.const "1" .none) (.op "Nil" .none), .const "0" .none, .abs .none (.abs .none (.bvar 1))])

-- Test 4: Polymorphic binary tree maps

-- Test 5: Term

end Lambda
