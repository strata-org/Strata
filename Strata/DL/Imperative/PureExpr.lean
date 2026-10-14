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
  /-- Decidable equality on identifiers. -/
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
  /-- Factory for function/operator resolution -/
  Factory : Type
  /-- The expression evaluator. Takes a factory, a variable store, and an
      expression, and returns an optional evaluated expression. -/
  eval : Factory → (Ident → Option Expr) → Expr → Option Expr

abbrev PureExpr.TypedIdent (P : PureExpr) := P.Ident × P.Ty
abbrev PureExpr.TypedExpr (P : PureExpr)  := P.Expr × P.Ty

/-! ## Type Classes for Expressions -/

class HasIdent (P : PureExpr) where
  ident : String → P.Ident

/-- Lawfulness of `HasIdent`: the canonical identifier-injection is injective. -/
class LawfulHasIdent (P : PureExpr) [HasIdent P] where
  ident_inj : Function.Injective (HasIdent.ident (P := P))

class HasFvar (P : PureExpr) where
  mkFvar : P.Ident → P.Expr
  /-- A free variable carrying its type. A pass that introduces a variable after
      type checking has run must annotate it itself, since nothing downstream
      will. -/
  mkTypedFvar : P.Ident → P.Ty → P.Expr
  getFvar : P.Expr → Option P.Ident

/-- Lawfulness of `HasFvar`: the round-trip `getFvar (mkFvar x) = some x`. -/
class LawfulHasFvar (P : PureExpr) [HasFvar P] where
  getFvar_mkFvar : ∀ x : P.Ident,
    HasFvar.getFvar (HasFvar.mkFvar (P := P) x) = some x
  /-- The annotation does not change which variable the expression is. -/
  getFvar_mkTypedFvar : ∀ (x : P.Ident) (ty : P.Ty),
    HasFvar.getFvar (HasFvar.mkTypedFvar (P := P) x ty) = some x

/-- Multi-variable version of `HasFvar.getFvar`: returns ALL free variables in
    a (possibly compound) expression.  `HasFvar.getFvar` only returns Some when
    the expression is a single fvar atom; `HasFvars.getFvars` recurses into
    compounds. -/
class HasFvars (P : PureExpr) where
  getFvars : P.Expr → List P.Ident

/-- Lawfulness of `HasFvars` against `HasFvar`: the free-variable list of an
    `mkFvar x` expression, as computed by the `HasFvars.getFvars` extractor, is a
    subset of `[x]`. -/
class LawfulHasFvars (P : PureExpr) [HasFvar P] [HasFvars P] where
  mkFvar_getFvars : ∀ x : P.Ident,
    HasFvars.getFvars (HasFvar.mkFvar (P := P) x) ⊆ [x]
  /-- The annotation contributes no free variables of its own. -/
  mkTypedFvar_getFvars : ∀ (x : P.Ident) (ty : P.Ty),
    HasFvars.getFvars (HasFvar.mkTypedFvar (P := P) x ty) ⊆ [x]

/-- Returns ALL operator/function names referenced in an expression
    (e.g., `.op` constructs in Lambda). -/
class HasOps (P : PureExpr) where
  getOps : P.Expr → List P.Ident

class HasVal (P : PureExpr) where
  value : P.Factory → P.Expr → Prop
  /-- `e` is a value of the monomorphic type `ty`. -/
  valueOfTy : P.Factory → P.Expr → P.Ty → Prop

/-- Laws for the abstract typed-value predicate. -/
class LawfulHasVal (P : PureExpr) [HasVal P] where
  /-- Every typed value is a value. -/
  valueOfTy_isVal : ∀ f e ty,
    HasVal.valueOfTy (P := P) f e ty → HasVal.value (P := P) f e
  /-- Typed-value membership is congruent across the shared type of a witness:
      if some value `a` has both types `ty₁` and `ty₂`, then any value of type
      `ty₂` is also a value of type `ty₁`. -/
  valueOfTy_congr : ∀ f (a b : P.Expr) (ty₁ ty₂ : P.Ty),
    HasVal.valueOfTy (P := P) f a ty₁ → HasVal.valueOfTy (P := P) f a ty₂ →
    HasVal.valueOfTy (P := P) f b ty₂ → HasVal.valueOfTy (P := P) f b ty₁

/-- Boolean expressions.  Extends `HasVal P` (folding in the former
    `HasBoolVal`).  `boolIsVal` ensures `tt`/`ff` are values. -/
class HasBool (P : PureExpr) extends HasVal P where
  tt : P.Expr
  ff : P.Expr
  tt_is_not_ff: tt ≠ ff
  boolTy : P.Ty
  /-- Boolean constants have the Boolean type. -/
  boolIsValOfTy : ∀ f,
    (@HasVal.valueOfTy P) f tt boolTy ∧
    (@HasVal.valueOfTy P) f ff boolTy

/-- Boolean constants are values, induced by their typed-value proofs. -/
@[expose] def HasBool.boolIsVal {P : PureExpr} [HasBool P] [LawfulHasVal P]
    (f : P.Factory) :
    HasVal.value f HasBool.tt ∧ HasVal.value f HasBool.ff :=
  ⟨LawfulHasVal.valueOfTy_isVal f HasBool.tt HasBool.boolTy
      (HasBool.boolIsValOfTy f).1,
    LawfulHasVal.valueOfTy_isVal f HasBool.ff HasBool.boolTy
      (HasBool.boolIsValOfTy f).2⟩

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
  numeralIsValue : ∀ f n, isNumeral n = Bool.true → (@HasVal.value P) f n
  zeroIsNumeral : isNumeral zero = Bool.true
  numeralHasNoFvars : ∀ (n : P.Expr), isNumeral n = Bool.true →
    HasFvars.getFvars (P := P) n = []

/-- Integer arithmetic / comparison primitives. -/
class HasIntOps (P : PureExpr) [HasBool P] [HasFvars P] [HasInt P] where
  eq    : P.Expr → P.Expr → P.Expr
  lt    : P.Expr → P.Expr → P.Expr

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
abbrev PureFunc (P : PureExpr) := Func P.Ident P.Expr P.Ty P.ExprMetadata

end -- public section
end Imperative
