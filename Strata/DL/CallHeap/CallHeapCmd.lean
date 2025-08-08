/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Call.CallCmd
import Strata.DL.Heap.Heap
import Strata.DL.Imperative.Stmt

namespace CallHeap

/-! ## Call + Heap Dialect

The CallHeap dialect combines Call and Heap operations into a unified dialect.
This serves as the target dialect for language translations (Python, TypeScript, etc.)
and provides a standard interface for analyses.
-/

variable {PureExpr : Type}

-- Combined Call + Heap commands
inductive CallHeapCmd (P : Imperative.PureExpr) where
  -- Call operations
  | directCall : (lhs : List String) → (funcName : String) → (args : List P.Expr) → CallHeapCmd P
  -- Heap operations (from Imperative.Cmd)
  | init : (name : P.Ident) → (ty : P.Ty) → (expr : P.Expr) → CallHeapCmd P
  | set : (name : P.Ident) → (expr : P.Expr) → CallHeapCmd P
  | havoc : (name : P.Ident) → CallHeapCmd P
  | assume : (name : P.Ident) → (expr : P.Expr) → CallHeapCmd P
  | assert : (name : P.Ident) → (expr : P.Expr) → CallHeapCmd P
  deriving Inhabited

-- CallHeap statement type
abbrev CallHeapStatement (P : Imperative.PureExpr) := Imperative.Stmt P (CallHeapCmd P)

-- Convenience constructors for statements
def CallHeapStatement.call {P : Imperative.PureExpr} (lhs : List String) (funcName : String) (args : List P.Expr) : CallHeapStatement P :=
  .cmd (.directCall lhs funcName args)

def CallHeapStatement.simpleCall {P : Imperative.PureExpr} (funcName : String) (args : List P.Expr) : CallHeapStatement P :=
  .cmd (.directCall [] funcName args)

def CallHeapStatement.singleCall {P : Imperative.PureExpr} (result : String) (funcName : String) (args : List P.Expr) : CallHeapStatement P :=
  .cmd (.directCall [result] funcName args)

def CallHeapStatement.init {P : Imperative.PureExpr} (name : P.Ident) (ty : P.Ty) (expr : P.Expr) : CallHeapStatement P :=
  .cmd (.init name ty expr)

def CallHeapStatement.set {P : Imperative.PureExpr} (name : P.Ident) (expr : P.Expr) : CallHeapStatement P :=
  .cmd (.set name expr)

def CallHeapStatement.havoc {P : Imperative.PureExpr} (name : P.Ident) : CallHeapStatement P :=
  .cmd (.havoc name)

end CallHeap
