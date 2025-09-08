/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



namespace Imperative

/--
Expected interface for pure expressions that can be used to specialize the
Imperative dialect.
-/
structure PureExpr : Type 1 where
  Ident   : Type
  Expr    : Type
  Ty      : Type
  /-- Typing environment -/
  TyEnv   : Type
  /-- Evaluation environment -/
  EvalEnv : Type
  EqIdent : DecidableEq Ident

abbrev PureExpr.TypedIdent (P : PureExpr) := P.Ident × P.Ty
abbrev PureExpr.TypedExpr (P : PureExpr)  := P.Expr × P.Ty

/-! ## Type Classes for Expressions -/
/-- Boolean expressions -/
class HasBool (P : PureExpr) where
  tt : P.Expr
  ff : P.Expr

class HasBoolNeg (P : PureExpr) [HasBool P] where
  neg : P.Expr → P.Expr

class HasFvar (P : PureExpr) where
  mkFvar : P.Ident → P.Expr
  getFvar : P.Expr → Option P.Ident

class HasVal (P : PureExpr) where
  value : P.Expr → Prop

class HasBoolVal (P : PureExpr) [HasBool P] [HasVal P] where
  bool_is_val : (@HasVal.value P) HasBool.tt ∧ (@HasVal.value P) HasBool.ff

end Imperative
