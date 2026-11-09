/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.Func

namespace Imperative

open Strata.DL.Util (Func)

public section

universe u

/--
Expected interface for pure expressions that can be used to specialize the
Imperative dialect.
-/
structure PureExpr : Type (u + 1) where
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
  /-- Factory for function/operator resolution. A factory may also carry a
      semantic model (as Core's runtime factory does), which is why it lives in
      an arbitrary universe. -/
  Factory : Type u
  /-- Runtime values held by variable stores and produced by `eval`. A value
      may record the model it was produced in; `HasVal.value` says which
      values belong to a given factory. -/
  Val : Type u
  /-- The expression evaluator. Takes a factory, a variable store, and an
      expression, and returns an optional value. -/
  eval : Factory → (Ident → Option Val) → Expr → Option Val

abbrev PureExpr.TypedIdent (P : PureExpr) := P.Ident × P.Ty
abbrev PureExpr.TypedExpr (P : PureExpr)  := P.Expr × P.Ty

/-- `[DecidableEq P.Ident]` resolves to the bundled `PureExpr.EqIdent` field,
keeping the term on a single instance across a proof. -/
instance (P : PureExpr) : DecidableEq P.Ident := P.EqIdent

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

/-- Returns ALL operator/function names referenced in an expression
    (e.g., `.op` constructs in Lambda). -/
class HasOps (P : PureExpr) where
  getOps : P.Expr → List P.Ident

/-- Lawfulness of `HasFvar`: variable constructors round-trip through `getFvar`
and a typed variable contains no operator references. -/
class LawfulHasFvar (P : PureExpr) [HasFvar P] [HasOps P] where
  getFvar_mkFvar : ∀ x : P.Ident,
    HasFvar.getFvar (HasFvar.mkFvar (P := P) x) = some x
  /-- The annotation does not change which variable the expression is. -/
  getFvar_mkTypedFvar : ∀ (x : P.Ident) (ty : P.Ty),
    HasFvar.getFvar (HasFvar.mkTypedFvar (P := P) x ty) = some x
  /-- A typed variable has no operator or function references. -/
  getOps_mkTypedFvar : ∀ (x : P.Ident) (ty : P.Ty),
    HasOps.getOps (HasFvar.mkTypedFvar (P := P) x ty) = []

/-- Multi-variable version of `HasFvar.getFvar`: returns ALL free variables in
    a (possibly compound) expression.  `HasFvar.getFvar` only returns Some when
    the expression is a single fvar atom; `HasFvars.getFvars` recurses into
    compounds. -/
class HasFvars (P : PureExpr) where
  getFvars : P.Expr → List P.Ident
  /-- The free-variable occurrences of an expression that carry a type annotation, with
      their annotations.  There is no default: a language whose expressions carry no
      annotations says so with `fun _ => []`. -/
  getTypedFvars : P.Expr → List (P.Ident × P.Ty)

/-- Lawfulness of `HasFvars` against `HasFvar`: the free-variable list of an
    `mkFvar x` expression, as computed by the `HasFvars.getFvars` extractor, is a
    subset of `[x]`. -/
class LawfulHasFvars (P : PureExpr) [HasFvar P] [HasFvars P] where
  mkFvar_getFvars : ∀ x : P.Ident,
    HasFvars.getFvars (HasFvar.mkFvar (P := P) x) ⊆ [x]
  /-- The annotation contributes no free variables of its own. -/
  mkTypedFvar_getFvars : ∀ (x : P.Ident) (ty : P.Ty),
    HasFvars.getFvars (HasFvar.mkTypedFvar (P := P) x ty) ⊆ [x]
  /-- An annotated occurrence is a free variable. -/
  mem_getFvars_of_typed : ∀ (e : P.Expr) (x : P.Ident) (ty : P.Ty),
    (x, ty) ∈ HasFvars.getTypedFvars e → x ∈ HasFvars.getFvars e := by
    intros; simp_all
  /-- A bare variable carries no annotation. -/
  mkFvar_getTypedFvars : ∀ x : P.Ident,
    HasFvars.getTypedFvars (HasFvar.mkFvar (P := P) x) = [] := by
    intros; rfl
  /-- A typed variable carries only its own annotation. -/
  mkTypedFvar_getTypedFvars : ∀ (x : P.Ident) (ty : P.Ty),
    HasFvars.getTypedFvars (HasFvar.mkTypedFvar (P := P) x ty) ⊆ [(x, ty)] := by
    intros; simp

/-- Predicates on runtime values (`P.Val`): which values belong to a factory
    (and so may be held by its stores), and which values inhabit a type. -/
class HasVal (P : PureExpr) where
  /-- `v` is a runtime value of factory `f`. -/
  value : P.Factory → P.Val → Prop
  /-- `v` is a value of the monomorphic type `ty`. -/
  valueOfTy : P.Factory → P.Val → P.Ty → Prop

/-- Laws for the abstract typed-value predicate. -/
class LawfulHasVal (P : PureExpr) [HasVal P] where
  /-- Every typed value is a value. -/
  valueOfTy_isVal : ∀ f v ty,
    HasVal.valueOfTy (P := P) f v ty → HasVal.value (P := P) f v
  /-- Typed-value membership is congruent across the shared type of a witness:
      if some value `a` has both types `ty₁` and `ty₂`, then any value of type
      `ty₂` is also a value of type `ty₁`. -/
  valueOfTy_congr : ∀ f (a b : P.Val) (ty₁ ty₂ : P.Ty),
    HasVal.valueOfTy (P := P) f a ty₁ → HasVal.valueOfTy (P := P) f a ty₂ →
    HasVal.valueOfTy (P := P) f b ty₂ → HasVal.valueOfTy (P := P) f b ty₁

/-- Boolean expressions and values.  Extends `HasVal P`.  The expression
    constants `tt`/`ff` are syntax; `ttVal f`/`ffVal f` are the runtime values
    of factory `f` they evaluate to (see `WellFormedSemanticEvalVal`). -/
class HasBool (P : PureExpr) extends HasVal P where
  tt : P.Expr
  ff : P.Expr
  tt_is_not_ff: tt ≠ ff
  boolTy : P.Ty
  /-- The runtime value `true` of a factory. -/
  ttVal : P.Factory → P.Val
  /-- The runtime value `false` of a factory. -/
  ffVal : P.Factory → P.Val
  /-- The Boolean values are distinct. -/
  ttVal_ne_ffVal : ∀ f, ttVal f ≠ ffVal f
  /-- Boolean values have the Boolean type. -/
  boolIsValOfTy : ∀ f,
    (@HasVal.valueOfTy P) f (ttVal f) boolTy ∧
    (@HasVal.valueOfTy P) f (ffVal f) boolTy

set_option linter.defProp false in
/-- Boolean values are values, induced by their typed-value proofs. -/
@[expose] def HasBool.boolIsVal {P : PureExpr} [HasBool P] [LawfulHasVal P]
    (f : P.Factory) :
    HasVal.value f (HasBool.ttVal f) ∧ HasVal.value f (HasBool.ffVal f) :=
  ⟨LawfulHasVal.valueOfTy_isVal f (HasBool.ttVal f) HasBool.boolTy
      (HasBool.boolIsValOfTy f).1,
    LawfulHasVal.valueOfTy_isVal f (HasBool.ffVal f) HasBool.boolTy
      (HasBool.boolIsValOfTy f).2⟩

/-- A variable reference, annotated with `ty` when given. -/
@[expose] def HasFvar.mkVar {P : PureExpr} [HasFvar P] (x : P.Ident) (ty : Option P.Ty) : P.Expr :=
  match ty with
  | some t => HasFvar.mkTypedFvar x t
  | none => HasFvar.mkFvar x

/-- A Boolean variable reference. -/
@[expose] def HasFvar.mkBoolVar {P : PureExpr} [HasBool P] [HasFvar P] (x : P.Ident) : P.Expr :=
  HasFvar.mkVar x (some HasBool.boolTy)
/-- Laws for the Boolean expression constants: they read no variables. -/
class LawfulHasBool (P : PureExpr) [HasBool P] [HasFvars P] where
  tt_getFvars : HasFvars.getFvars (P := P) HasBool.tt = []
  ff_getFvars : HasFvars.getFvars (P := P) HasBool.ff = []

/-- Boolean operations: not, and, imp. -/
class HasBoolOps (P : PureExpr) extends HasBool P where
  not : P.Expr → P.Expr
  and : P.Expr → P.Expr → P.Expr
  imp : P.Expr → P.Expr → P.Expr

/-! ## Typing of expressions

The command semantics only steps when expressions evaluate, and an evaluator may
fail on ill-typed expressions (Core's denotational evaluator does).  These
definitions state the typing assumption under which evaluation cannot fail; their
consequences for commands are in `Strata.DL.Imperative.CmdSemanticsProps`. -/

/-- The types assigned to variables, as computed by a type checker. -/
abbrev VarTyping (P : PureExpr) := P.Ident → Option P.Ty

/-- The typing judgment for expressions. -/
class HasTyping (P : PureExpr) where
  /-- `e` has type `ty` under factory `f` when each free variable `x` has the
      type `Γ x`. -/
  HasType : P.Factory → VarTyping P → P.Expr → P.Ty → Prop

/-- The store `σ` (a `SemanticStore P`) conforms to the typing `Γ`: every variable
    that `Γ` types holds a value of that type. -/
@[expose] def StoreHasTyping {P : PureExpr} [HasVal P]
    (f : P.Factory) (σ : P.Ident → Option P.Val) (Γ : VarTyping P) : Prop :=
  ∀ x ty, Γ x = some ty → ∃ v, σ x = some v ∧ HasVal.valueOfTy f v ty

/-- Extend the typing `Γ` with the typed definitions `defs`; the first definition of a
    name wins. -/
@[expose] def VarTyping.extend {P : PureExpr} (Γ : VarTyping P)
    (defs : List (P.Ident × P.Ty)) : VarTyping P :=
  fun y => match defs.find? (fun d => d.1 == y) with
    | some d => some d.2
    | none => Γ y

/-- Type soundness of the evaluator against the typing judgment. -/
class LawfulHasTyping (P : PureExpr) [HasBool P] [HasTyping P] where
  /-- A well-typed expression evaluates, in a store conforming to its typing, to
      a value of its type. -/
  eval_of_hasType : ∀ (f : P.Factory) (Γ : VarTyping P) (σ : P.Ident → Option P.Val)
      (e : P.Expr) (ty : P.Ty),
    HasTyping.HasType f Γ e ty → StoreHasTyping f σ Γ →
    ∃ v, P.eval f σ e = some v ∧ HasVal.valueOfTy f v ty
  /-- The values of the Boolean type are the two Boolean values. -/
  valueOfTy_bool : ∀ (f : P.Factory) (v : P.Val),
    HasVal.valueOfTy f v HasBool.boolTy → v = HasBool.ttVal f ∨ v = HasBool.ffVal f

/-- Integer constants and the integer type. -/
class HasInt (P : PureExpr) [HasVal P] [HasFvars P] where
  zero  : P.Expr
  intTy : P.Ty
  isNumeral : P.Expr → Bool
  /-- The runtime values that are integer numerals. -/
  isNumeralVal : P.Val → Bool
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
  /-- Simultaneously rename free variables by NAME, in a single pass with
      first-match semantics (`a ↦ b` for the first `(a, b)` in the list, else
      unchanged). Unlike `substFvars`, this rewrites a free variable's name in
      place and preserves everything else about the occurrence — in particular
      any type annotation it carries — so renaming never drops type information
      the way substituting a freshly-built bare free variable would. -/
  renameFvars : P.Expr → List (P.Ident × P.Ident) → P.Expr

/--
A function declaration for use with `PureExpr` - instantiation of `Func` for
any expression system that implements the `PureExpr` interface.
-/
abbrev PureFunc (P : PureExpr) := Func P.Ident P.Expr P.Ty P.ExprMetadata

end -- public section
end Imperative
