/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Heap.HTy
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Identifiers
import Strata.DL.Lambda.MetaData
import Lean

---------------------------------------------------------------------

namespace Heap

open Lambda (LExpr LMonoTy Info QuantifierKind)

-- Address type - simple natural numbers for now
abbrev Address := Nat

/-! ## Heap Expressions

Extension of Lambda expressions to include heap operations.
We add allocation, field access, and field update operations.
-/

/--
Heap Expressions extending Lambda expressions with heap operations.
I think some of these should not be expressions, for example "assign" make more sense as a statement, but I know in a lot of languages "assign" returns a value.
But for now we'll just keep it together.
-/
inductive HExpr : Type where
  -- Include all Lambda expressions (using String as Identifier)
  | lambda (e : LExpr LMonoTy String)
  -- New heap-specific expressions
  | alloc  (objTy : HMonoTy) (fields : List (Nat × HExpr))   -- Allocate object with (index, value) pairs
  | deref  (addr : HExpr) (field : Nat)                      -- Field access: addr[field]
  | assign (addr : HExpr) (field : Nat) (value : HExpr)      -- Field update: addr[field] := value
  | address (addr : Address)                                  -- Direct address value
  | null                                                      -- Null address
  -- Deferred operations for cross-dialect composition (following Lambda's pattern)
  | deferredOp (op : String) (ty : Option HMonoTy)           -- Deferred operation, like Lambda's .op
  | app (fn arg : HExpr)                                      -- Application, like Lambda's .app
  | deferredIte (guard consequent alternate : HExpr)         -- Deferred conditional, like Lambda's .ite
  deriving Repr

---------------------------------------------------------------------

namespace HExpr

instance : Inhabited HExpr where
  default := .null

-- Boolean constants
@[match_pattern]
protected def true : HExpr := .lambda (LExpr.true : LExpr LMonoTy String)

@[match_pattern]
protected def false : HExpr := .lambda (LExpr.false : LExpr LMonoTy String)

-- Integer constants
def int (n : Int) : HExpr :=
  .lambda (LExpr.const (toString n) (some LMonoTy.int) : LExpr LMonoTy String)

-- String constants
def string (s : String) : HExpr :=
  .lambda (LExpr.const s (some LMonoTy.string) : LExpr LMonoTy String)

-- Convert Lambda expression to Heap expression
def ofLambda (e : LExpr LMonoTy String) : HExpr := .lambda e

-- Extract Lambda expression if possible
def toLambda? (e : HExpr) : Option (LExpr LMonoTy String) :=
  match e with
  | .lambda le => some le
  | _ => none

end HExpr

end Heap
