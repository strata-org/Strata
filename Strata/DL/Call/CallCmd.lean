/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.Stmt

namespace Call

/-! ## Call Dialect

The Call dialect extends Imperative with function call operations.
It provides a basic direct call mechanism that can be extended by languages
for more sophisticated call semantics.
-/

variable {PureExpr : Type}

-- Call commands extend imperative commands with call operations
inductive CallCmd (P : Imperative.PureExpr) where
  -- Wrap existing imperative commands
  | imperativeCmd : Imperative.Cmd P → CallCmd P
  -- Direct function call: lhs := funcName(args)
  | directCall : (lhs : List String) → (funcName : String) → (args : List P.Expr) → CallCmd P
  deriving Inhabited

-- Convenience constructors
def CallCmd.init {P : Imperative.PureExpr} (name : P.Ident) (ty : P.Ty) (expr : P.Expr) : CallCmd P :=
  .imperativeCmd (.init name ty expr .empty)

def CallCmd.set {P : Imperative.PureExpr} (name : P.Ident) (expr : P.Expr) : CallCmd P :=
  .imperativeCmd (.set name expr .empty)

def CallCmd.havoc {P : Imperative.PureExpr} (name : P.Ident) : CallCmd P :=
  .imperativeCmd (.havoc name .empty)

-- Call statement type
--abbrev CallStatement (P : Imperative.PureExpr) := Imperative.Stmt P (CallCmd P)
--
---- Convenience constructors for statements
--partial def CallStatement.cmd {P : Imperative.PureExpr} (cmd : CallCmd P) : CallStatement P :=
--  .cmd cmd
--
--def CallStatement.call {P : Imperative.PureExpr} (lhs : List String) (funcName : String) (args : List P.Expr) : CallStatement P :=
--  .cmd (.directCall lhs funcName args)
--
---- Simple call with no return value
--def CallStatement.simpleCall {P : Imperative.PureExpr} (funcName : String) (args : List P.Expr) : CallStatement P :=
--  .cmd (.directCall [] funcName args)
--
---- Call with single return value
--def CallStatement.singleCall {P : Imperative.PureExpr} (result : String) (funcName : String) (args : List P.Expr) : CallStatement P :=
--  .cmd (.directCall [result] funcName args)

end Call
