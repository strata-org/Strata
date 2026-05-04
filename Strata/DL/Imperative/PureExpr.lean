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
/-- Boolean expressions -/
class HasBool (P : PureExpr) where
  tt : P.Expr
  ff : P.Expr
  tt_is_not_ff: tt ≠ ff
  boolTy : P.Ty
  /-- Returns true if the expression is a true boolean value (ignoring metadata). -/
  isTrue : P.Expr → Bool
  /-- Returns true if the expression is a false boolean value (ignoring metadata). -/
  isFalse : P.Expr → Bool

class HasNot (P : PureExpr) extends HasBool P where
  not : P.Expr → P.Expr

class HasAnd (P : PureExpr) extends HasBool P where
  and : P.Expr → P.Expr → P.Expr

class HasImp (P : PureExpr) extends HasBool P where
  imp : P.Expr → P.Expr → P.Expr

/-- Integer ordering primitives.
    `zero` is the lower-bound constant for well-foundedness (measure ≥ 0).
    `intTy` is the type of integer expressions, for variable declarations.
    `ge` is derivable as `HasNot.not (lt b a)` and is therefore omitted. -/
class HasIntOrder (P : PureExpr) where
  eq    : P.Expr → P.Expr → P.Expr
  lt    : P.Expr → P.Expr → P.Expr
  zero  : P.Expr
  intTy : P.Ty

class HasIdent (P : PureExpr) where
  ident : String → P.Ident

class HasFvar (P : PureExpr) where
  mkFvar : P.Ident → P.Expr
  getFvar : P.Expr → Option P.Ident

class HasVal (P : PureExpr) where
  value : P.Expr → Prop

class HasBoolVal (P : PureExpr) [HasBool P] [HasVal P] where
  bool_is_val : (@HasVal.value P) HasBool.tt ∧ (@HasVal.value P) HasBool.ff

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
