/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.Func

namespace Imperative

open Strata.DL.Util (Func)

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

abbrev PureExpr.TypedIdent (P : PureExpr) := P.Ident × P.Ty
abbrev PureExpr.TypedExpr (P : PureExpr)  := P.Expr × P.Ty

/-! ## Type Classes for Expressions -/
/-- Boolean expressions -/
class HasBool (P : PureExpr) where
  tt : P.Expr
  ff : P.Expr

class HasNot (P : PureExpr) extends HasBool P where
  not : P.Expr → P.Expr

class HasAnd (P : PureExpr) extends HasBool P where
  and : P.Expr → P.Expr → P.Expr

class HasImp (P : PureExpr) extends HasBool P where
  imp : P.Expr → P.Expr → P.Expr

class HasEq (P : PureExpr) where
  eq : P.Expr → P.Expr → P.Expr

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

/-- Substitute multiple free variables with expressions -/
def HasSubstFvar.substFvars [HasSubstFvar P] (e : P.Expr) (substs : List (P.Ident × P.Expr)) : P.Expr :=
  substs.foldl (fun e (id, val) => HasSubstFvar.substFvar e id val) e

/--
A function declaration for use with `PureExpr` - instantiation of `Func` for
any expression system that implements the `PureExpr` interface.
-/
abbrev PureFunc (P : PureExpr) := Func P.Ident P.Expr P.Ty P.ExprMetadata

end Imperative
