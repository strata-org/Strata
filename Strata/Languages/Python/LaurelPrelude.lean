/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel

/-!
# Laurel Prelude for Python

This module defines the minimal Laurel types and procedures needed to support
Python programs translated to Laurel.

## Current Scope (Steel Thread)
- Basic types: int, bool
- Basic operations: arithmetic, comparison, logical
- No heap operations
- No collections
- No exceptions

## Future Extensions
- Heap types (Composite, Field)
- Collections (List, Dict, Set)
- Exception handling
- Python standard library functions
-/

namespace Strata.Python.LaurelPrelude

open Laurel

/-! ## Type Definitions

For the minimal steel thread, we only need primitive types.
Collections and user-defined types will be added later.
-/

/-! ## Built-in Procedures

Python built-in functions that need to be modeled as Laurel procedures.
For the steel thread, we start with an empty set and add as needed.
-/

/-- Minimal Laurel program with Python prelude definitions -/
def minimalPrelude : Laurel.Program :=
  { staticProcedures := []
    staticFields := []
    types := []
    constants := [] }

/-! ## Helper Functions for Building Laurel AST

These helpers make it easier to construct Laurel AST nodes from Python translation.
-/

/-- Create a Laurel integer literal -/
def mkIntLiteral (n : Int) : StmtExprMd :=
  { val := StmtExpr.LiteralInt n
    md := default }

/-- Create a Laurel boolean literal -/
def mkBoolLiteral (b : Bool) : StmtExprMd :=
  { val := StmtExpr.LiteralBool b
    md := default }

/-- Create a Laurel identifier reference -/
def mkIdentifier (name : String) : StmtExprMd :=
  { val := StmtExpr.Identifier name
    md := default }

/-- Create a Laurel binary operation -/
def mkBinOp (op : Laurel.Operation) (lhs rhs : StmtExprMd) : StmtExprMd :=
  { val := StmtExpr.PrimitiveOp op [lhs, rhs]
    md := default }

/-- Create a Laurel unary operation -/
def mkUnaryOp (op : Laurel.Operation) (arg : StmtExprMd) : StmtExprMd :=
  { val := StmtExpr.PrimitiveOp op [arg]
    md := default }

/-- Create a Laurel assignment -/
def mkAssign (target value : StmtExprMd) : StmtExprMd :=
  { val := StmtExpr.Assign target value
    md := default }

/-- Create a Laurel local variable declaration -/
def mkLocalVariable (name : String) (ty : HighTypeMd) (init : Option StmtExprMd) : StmtExprMd :=
  { val := StmtExpr.LocalVariable name ty init
    md := default }

/-- Create a Laurel if-then-else -/
def mkIfThenElse (cond thenBranch : StmtExprMd) (elseBranch : Option StmtExprMd) : StmtExprMd :=
  { val := StmtExpr.IfThenElse cond thenBranch elseBranch
    md := default }

/-- Create a Laurel while loop -/
def mkWhile (cond body : StmtExprMd) (invariants : List StmtExprMd := []) : StmtExprMd :=
  { val := StmtExpr.While cond invariants none body
    md := default }

/-- Create a Laurel return statement -/
def mkReturn (value : Option StmtExprMd) : StmtExprMd :=
  { val := StmtExpr.Return value
    md := default }

/-- Create a Laurel assertion -/
def mkAssert (condition : StmtExprMd) : StmtExprMd :=
  { val := StmtExpr.Assert condition
    md := default }

/-- Create a Laurel block -/
def mkBlock (stmts : List StmtExprMd) (label : Option String := none) : StmtExprMd :=
  { val := StmtExpr.Block stmts label
    md := default }

/-! ## Type Helpers -/

/-- Create a Laurel int type -/
def intType : HighTypeMd :=
  { val := HighType.TInt
    md := default }

/-- Create a Laurel bool type -/
def boolType : HighTypeMd :=
  { val := HighType.TBool
    md := default }

/-- Create a Laurel void type -/
def voidType : HighTypeMd :=
  { val := HighType.TVoid
    md := default }

/-! ## Operation Mapping

Map Python operators to Laurel operations.
-/

/-- Python arithmetic operators -/
inductive PyArithOp where
  | add | sub | mul | div | mod | neg
deriving Repr, BEq

/-- Python comparison operators -/
inductive PyCmpOp where
  | eq | neq | lt | leq | gt | geq
deriving Repr, BEq

/-- Python logical operators -/
inductive PyLogicalOp where
  | and | or | not
deriving Repr, BEq

/-- Map Python arithmetic operator to Laurel operation -/
def pyArithOpToLaurel : PyArithOp → Laurel.Operation
  | .add => Laurel.Operation.Add
  | .sub => Laurel.Operation.Sub
  | .mul => Laurel.Operation.Mul
  | .div => Laurel.Operation.Div
  | .mod => Laurel.Operation.Mod
  | .neg => Laurel.Operation.Neg

/-- Map Python comparison operator to Laurel operation -/
def pyCmpOpToLaurel : PyCmpOp → Laurel.Operation
  | .eq => Laurel.Operation.Eq
  | .neq => Laurel.Operation.Neq
  | .lt => Laurel.Operation.Lt
  | .leq => Laurel.Operation.Leq
  | .gt => Laurel.Operation.Gt
  | .geq => Laurel.Operation.Geq

/-- Map Python logical operator to Laurel operation -/
def pyLogicalOpToLaurel : PyLogicalOp → Laurel.Operation
  | .and => Laurel.Operation.And
  | .or => Laurel.Operation.Or
  | .not => Laurel.Operation.Not

end Strata.Python.LaurelPrelude
