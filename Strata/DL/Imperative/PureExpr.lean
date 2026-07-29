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

@[expose] abbrev PureExpr.TypedIdent (P : PureExpr) := P.Ident × P.Ty
@[expose] abbrev PureExpr.TypedExpr (P : PureExpr)  := P.Expr × P.Ty

/-! ## Type Classes for Expressions -/

class HasIdent (P : PureExpr) where
  ident : String → P.Ident

/-- Lawfulness of `HasIdent`: the canonical identifier-injection is injective. -/
class LawfulHasIdent (P : PureExpr) [HasIdent P] where
  ident_inj : Function.Injective (HasIdent.ident (P := P))

/-- The shared kind-first freshness core: every `Q`-kind label's identifier
satisfies the abstract absence test `absent`.  `NoGenSuffix` instantiates
`absent := (· ∉ xs)` (syntactic — a name list); `NoGenStore` instantiates
`absent := (ρ.store · = none)` (semantic — a store), so the two freshness
conditions share this one definition. -/
abbrev AbsentAtGen {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (absent : P.Ident → Prop) : Prop :=
  ∀ s : String, Q s → absent (HasIdent.ident (P := P) s)

/-- `NoGenSuffix Q xs` says no name `xs` carries is the image of a `Q`-kind
string — equivalently, every ident in `xs` was supplied by user source.  Stated
*kind-first*: for every string `s` satisfying the label-kind predicate `Q` (the
kind of label a pass generates), `HasIdent.ident s` is absent from `xs`.
Instantiating `Q := HasUnderscoreDigitSuffix` recovers the blanket "no statement
writes a gen-shaped variable" condition; a per-kind `Q` lets a composition
partner satisfy the obligation by generating under a disjoint prefix. -/
abbrev NoGenSuffix {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (xs : List P.Ident) : Prop :=
  AbsentAtGen (P := P) Q (· ∉ xs)

/-- Contrapositive elimination: from `NoGenSuffix Q xs`, every member of `xs`
that equals `HasIdent.ident s` is not a `Q`-kind name.  This is the member-first
orientation some consumers apply. -/
theorem NoGenSuffix.contrapos {P : PureExpr} [HasIdent P]
    {Q : String → Prop} {xs : List P.Ident}
    (h : NoGenSuffix (P := P) Q xs) :
    ∀ x ∈ xs, ∀ s : String, x = HasIdent.ident (P := P) s → ¬ Q s :=
  fun _ hx s heq hQ => h s hQ (heq ▸ hx)

/-- Contrapositive introduction: the member-first orientation implies
`NoGenSuffix`.  Inverse of `NoGenSuffix.contrapos`. -/
theorem NoGenSuffix.ofContrapos {P : PureExpr} [HasIdent P]
    {Q : String → Prop} {xs : List P.Ident}
    (h : ∀ x ∈ xs, ∀ s : String, x = HasIdent.ident (P := P) s → ¬ Q s) :
    NoGenSuffix (P := P) Q xs :=
  fun s hQ hmem => h _ hmem s rfl hQ

class HasFvar (P : PureExpr) where
  mkFvar : P.Ident → P.Expr
  getFvar : P.Expr → Option P.Ident

/-- Lawfulness of `HasFvar`: the round-trip `getFvar (mkFvar x) = some x`. -/
class LawfulHasFvar (P : PureExpr) [HasFvar P] where
  getFvar_mkFvar : ∀ x : P.Ident,
    HasFvar.getFvar (HasFvar.mkFvar (P := P) x) = some x

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

/-- Returns ALL operator/function names referenced in an expression
    (e.g., `.op` constructs in Lambda). -/
class HasOps (P : PureExpr) where
  getOps : P.Expr → List P.Ident

class HasVal (P : PureExpr) where
  value : P.Factory → P.Expr → Prop

/-- Boolean expressions.  Extends `HasVal P` (folding in the former
    `HasBoolVal`).  `boolIsVal` ensures `tt`/`ff` are values. -/
class HasBool (P : PureExpr) extends HasVal P where
  tt : P.Expr
  ff : P.Expr
  tt_is_not_ff: tt ≠ ff
  boolTy : P.Ty
  boolIsVal : ∀ f, (@HasVal.value P) f tt ∧ (@HasVal.value P) f ff

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
@[expose] abbrev PureFunc (P : PureExpr) := Func P.Ident P.Expr P.Ty P.ExprMetadata

end -- public section
end Imperative
