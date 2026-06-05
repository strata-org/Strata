/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.Func

namespace Imperative

open Strata.DL.Util (Func)

public section

/--
Expected interface for pure expressions that can be used to specialize the
Imperative dialect.
-/
structure PureExpr : Type 1 where
  /-- Kinds of identifiers allowed in expressions. We expect identifiers to have
   decidable equality; see `EqIdent`. -/
  Ident   : Type
  EqIdent : DecidableEq Ident
  /-- Expressions -/
  Expr    : Type
  /-- Types -/
  Ty      : Type
  /-- Expression metadata type (for use in function declarations, etc.) -/
  ExprMetadata : Type
  /-- Typing environment, expected to contain a map of variables to their types,
  type substitution, etc.
  -/
  TyEnv   : Type
  /-- Typing context, expected to contain information that does not change
    during type checking/inference (e.g., known types and known functions.)
  -/
  TyContext : Type
  /-- Evaluation environment -/
  EvalEnv : Type

@[expose] abbrev PureExpr.TypedIdent (P : PureExpr) := P.Ident × P.Ty
@[expose] abbrev PureExpr.TypedExpr (P : PureExpr)  := P.Expr × P.Ty

/-! ## Type Classes for Expressions -/

class HasIdent (P : PureExpr) where
  ident : String → P.Ident

class HasFvar (P : PureExpr) where
  mkFvar : P.Ident → P.Expr
  getFvar : P.Expr → Option P.Ident

/-- Multi-variable version of `HasFvar.getFvar`: returns ALL free variables in
    a (possibly compound) expression.  `HasFvar.getFvar` only returns Some when
    the expression is a single fvar atom; `HasFvars.getFvars` recurses into
    compounds. -/
class HasFvars (P : PureExpr) where
  getFvars : P.Expr → List P.Ident

/-- Returns ALL operator/function names referenced in an expression
    (e.g., `.op` constructs in Lambda). -/
class HasOps (P : PureExpr) where
  getOps : P.Expr → List P.Ident

class HasVal (P : PureExpr) where
  value : P.Expr → Prop

/-- Boolean expressions.  Extends `HasVal P` (folding in the former
    `HasBoolVal`).  `boolIsVal` ensures `tt`/`ff` are values. -/
class HasBool (P : PureExpr) extends HasVal P where
  tt : P.Expr
  ff : P.Expr
  tt_is_not_ff: tt ≠ ff
  boolTy : P.Ty
  boolIsVal : (@HasVal.value P) tt ∧ (@HasVal.value P) ff

/-- Boolean operations: not, and, imp. -/
class HasBoolOps (P : PureExpr) extends HasBool P where
  not : P.Expr → P.Expr
  and : P.Expr → P.Expr → P.Expr
  imp : P.Expr → P.Expr → P.Expr

/-- Integer constants and the integer type. -/
class HasInt (P : PureExpr) [HasVal P] [HasFvars P] where
  zero  : P.Expr
  intTy : P.Ty
  isNumeral : P.Expr → Bool
  numeralIsValue : ∀ n, isNumeral n = Bool.true → (@HasVal.value P) n
  zeroIsNumeral : isNumeral zero = Bool.true
  numeralHasNoFvars : ∀ (n : P.Expr), isNumeral n = Bool.true →
    HasFvars.getFvars (P := P) n = []

/-- Integer arithmetic / comparison primitives. -/
class HasIntOps (P : PureExpr) [HasBool P] [HasFvars P] [HasInt P] where
  eq    : P.Expr → P.Expr → P.Expr
  lt    : P.Expr → P.Expr → P.Expr
  decr  : P.Expr → P.Expr

/-- Substitution of free variables in expressions.
    Used for closure capture in function declarations. -/
class HasSubstFvar (P : PureExpr) where
  /-- Substitute a single free variable with an expression -/
  substFvar : P.Expr → P.Ident → P.Expr → P.Expr
  /-- Simultaneously substitute multiple free variables with expressions.
      Replaces all variables in a single pass, avoiding capture between
      substitutions. -/
  substFvars : P.Expr → List (P.Ident × P.Expr) → P.Expr

/--
A function declaration for use with `PureExpr` - instantiation of `Func` for
any expression system that implements the `PureExpr` interface.
-/
@[expose] abbrev PureFunc (P : PureExpr) := Func P.Ident P.Expr P.Ty P.ExprMetadata

end -- public section
end Imperative
