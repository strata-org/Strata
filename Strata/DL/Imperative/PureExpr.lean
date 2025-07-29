/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
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
