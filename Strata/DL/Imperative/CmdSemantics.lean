/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
import all Strata.DL.Util.ListUtils

---------------------------------------------------------------------

namespace Imperative

public section

section

variable (P : PureExpr)

/-
These are intended to be as generic as possible, not using any specific
data structure. They'll probably usually be instantiated with map
lookups. The evaluation functions take two states: an old state and a
current state. This allows for two-state expressions and predicates.
-/
@[expose] abbrev SemanticStore := P.Ident → Option P.Expr
@[expose] abbrev SemanticEval := SemanticStore P → P.Expr → Option P.Expr
@[expose] abbrev SemanticEvalBool := SemanticStore P → P.Expr → Option Bool

/--
Evaluation relation of an Imperative command `Cmd`.
Commands do not modify the evaluator - only `funcDecl` statements do.

The Bool flag reports whether the command observed
a failure (e.g., an assertion whose guard is false).  The `Bool` is `true`
when the command signals a failure.
-/
@[expose] abbrev EvalCmdParam (P : PureExpr) (Cmd : Type) :=
  SemanticEval P → SemanticStore P → Cmd → SemanticStore P → Bool → Prop

/-- ### Well-Formedness of `SemanticStore`s -/

@[expose] def isDefined {P : PureExpr} (σ : SemanticStore P) (vs : List P.Ident) : Prop :=
  ∀ v, v ∈ vs → (σ v).isSome = true

def isNotDefined {P : PureExpr} (σ : SemanticStore P) (vs : List P.Ident) : Prop :=
  ∀ v, v ∈ vs → σ v = none

-- Can make this more generic by supplying a predicate function
-- (SemanticStore P) → P.Ident → Bool
-- determining whether each variable in the store is valid
-- This could express things like,
-- all variables in the store are values, all values are positive, etc.
def isDefinedOver {P : PureExpr}
  (getVars : α → List P.Ident) (σ : SemanticStore P) (s : α) : Prop :=
  isDefined σ (getVars s)

/-! ### Store Substitution -/

/-- Substitution relation between stores.  -/
def substStores {P : PureExpr} (σ₁ σ₂ : SemanticStore P) (substs : List (P.Ident × P.Ident))
  : Prop :=
  ∀ k1 k2, (k1, k2) ∈ substs → σ₁ k1 = σ₂ k2

def substDefined {P : PureExpr} (σ₁ σ₂ : SemanticStore P) (substs : List (P.Ident × P.Ident))
  : Prop :=
  ∀ k1 k2, (k1, k2) ∈ substs → (σ₁ k1).isSome = true ∧ (σ₂ k2).isSome = true

def substNodup {P : PureExpr} (substs : List (P.Ident × P.Ident))
  : Prop := (substs.unzip.1 ++ substs.unzip.2).Nodup

/-- a specialization of substitution, where the keys are the same -/
def invStores {P : PureExpr} (σ₁ σ₂ : SemanticStore P) (vs : List P.Ident)
  : Prop :=
  substStores σ₁ σ₂ $ vs.zip vs

def invStoresExcept {P : PureExpr} (σ₁ σ₂ : SemanticStore P) (vs : List P.Ident)
  : Prop := ∀ (vs' : List P.Ident), vs'.Disjoint vs → invStores σ₁ σ₂ vs'

def substSwap {P : PureExpr} (substs : List (P.Ident × P.Ident))
  : List (P.Ident × P.Ident) := substs.map Prod.swap

/-! ### Well-Formedness of `SemanticEval`s -/

@[expose] def WellFormedSemanticEvalBool {P : PureExpr} [HasBool P] [HasBoolOps P]
    (δ : SemanticEval P) : Prop :=
    ∀ σ e,
      (δ σ e = some Imperative.HasBool.tt ↔ δ σ (Imperative.HasBoolOps.not e) = (some HasBool.ff)) ∧
      (δ σ e = some Imperative.HasBool.ff ↔ δ σ (Imperative.HasBoolOps.not e) = (some HasBool.tt))

def WellFormedSemanticEvalVal {P : PureExpr} [HasVal P]
    (δ : SemanticEval P) : Prop :=
  -- evaluator only evaluates to values
    (∀ v v' σ, δ σ v = some v' → HasVal.value v') ∧
  -- evaluator is identity on values
    (∀ v' σ, HasVal.value v' → δ σ v' = some v')

@[expose] def WellFormedSemanticEvalVar {P : PureExpr} [HasFvar P] (δ : SemanticEval P)
    : Prop := (∀ e v σ, HasFvar.getFvar e = some v → δ σ e = σ v)

@[expose] def WellFormedSemanticEvalExprCongr {P : PureExpr} [HasFvars P] (δ : SemanticEval P)
    : Prop := ∀ e σ σ', (∀ x ∈ HasFvars.getFvars e, σ x = σ' x) → δ σ e = δ σ' e

/-- Well-formedness for the integer fragment of an evaluator. -/
structure WellFormedSemanticEvalInt {P : PureExpr}
    [HasBool P] [HasFvars P] [HasInt P] [HasIntOps P]
    (δ : SemanticEval P) : Prop where
  ltReduces : ∀ σ x y nx ny,
    δ σ x = some nx → HasInt.isNumeral nx = Bool.true →
    δ σ y = some ny → HasInt.isNumeral ny = Bool.true →
    δ σ (HasIntOps.lt x y) = some HasBool.tt ∨
    δ σ (HasIntOps.lt x y) = some HasBool.ff

/--
Abstract variable update.

This does not specify how `σ` is represented, only what it maps each variable to.
-/
inductive UpdateState : SemanticStore P → P.Ident → P.Expr → SemanticStore P → Prop where
  /-- The state `σ'` is be equivalent to `σ` except at `x`, where it maps to
  `v`. Requires that `x` mapped to something beforehand. -/
  | update :
    σ x = .some v' →
    σ' x = .some v →
    (∀ y, x ≠ y → σ' y = σ y) →
    ----
    UpdateState σ x v σ'

/--
Abtract variable initialization.

This does not specify how `σ` is represented, only what it maps each variable to.
-/
inductive InitState : SemanticStore P → P.Ident → P.Expr → SemanticStore P → Prop where
  /-- The state `σ'` is be equivalent to `σ` except at `x`, where it maps to
  `v`. Requires that `x` mapped to nothing beforehand. -/
  | init :
    σ x = none →
    σ' x = .some v →
    (∀ y, x ≠ y → σ' y = σ y) →
    ----
    InitState σ x v σ'

/--
An inductively-defined operational semantics for `Cmd` that depends on variable
lookup (`σ`) and expression evaluation (`δ`) functions.
Commands do not modify the evaluator - only `funcDecl` statements do.

The `Bool` output parameter is a *failure flag*: `true` when the command
signals an assertion failure, `false` otherwise.  Only `eval_assert_fail`
sets it to `true`; all other constructors report `false`.

The failure flag is accumulated in `Env.hasFailure` by the statement
semantics (`EvalStmt`).
-/
inductive EvalCmd [HasFvar P] [HasBool P] [HasBoolOps P] :
  SemanticEval P → SemanticStore P → Cmd P → SemanticStore P → Bool → Prop where
  /-- If `e` evaluates to a value `v`, initialize `x` according to `InitState`. -/
  | eval_init :
    δ σ e = .some v →
    InitState P σ x v σ' →
    WellFormedSemanticEvalVar δ →
    ---
    EvalCmd δ σ (.init x _ (.det e) _) σ' false

  /-- Initialize `x` with an unconstrained value (havoc semantics). -/
  | eval_init_unconstrained :
    InitState P σ x v σ' →
    WellFormedSemanticEvalVar δ →
    ---
    EvalCmd δ σ (.init x _ .nondet _) σ' false


  /-- If `e` evaluates to a value `v`, assign `x` according to `UpdateState`. -/
  | eval_set :
    δ σ e = .some v →
    UpdateState P σ x v σ' →
    WellFormedSemanticEvalVar δ →
    ----
    EvalCmd δ σ (.set x (.det e) _) σ' false

  /-- Assign `x` an arbitrary value `v` according to `UpdateState`. -/
  | eval_set_nondet :
    UpdateState P σ x v σ' →
    WellFormedSemanticEvalVar δ →
    ----
    EvalCmd δ σ (.set x .nondet _) σ' false

  /-- Assert passes: `e` evaluates to true, no failure. The store is unchanged. -/
  | eval_assert_pass :
    δ σ e = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    EvalCmd δ σ (.assert _ e _) σ false

  /-- Assert fails: `e` does not evaluate to true, failure flag is set.
      The store is unchanged — the command is an unconditional skip on the
      store, but the failure flag records the violation. -/
  | eval_assert_fail :
    δ σ e = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    EvalCmd δ σ (.assert _ e _) σ true

  /-- If `e` evaluates to true in `σ`, evaluate to the same `σ`. -/
  | eval_assume :
    δ σ e = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    EvalCmd δ σ (.assume _ e _) σ false

  /-- A cover, when encountered, is essentially a skip. -/
  | eval_cover :
    WellFormedSemanticEvalBool δ →
    ----
    EvalCmd δ σ (.cover _ e _) σ false

end section

end -- public section
