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

/-- The store `σ_cfg` contains everything `σ_struct` contains, with matching
values. `σ_cfg` may have additional entries that `σ_struct` does not.

Equivalently: for every variable defined in `σ_struct` (in the sense of
`isDefined`), `σ_cfg` assigns the same value at that variable. -/
@[expose] def StoreAgreement {P : PureExpr}
    (σ_struct σ_cfg : SemanticStore P) : Prop :=
  ∀ x, isDefined σ_struct [x] → σ_struct x = σ_cfg x

theorem StoreAgreement.refl {P : PureExpr} (σ : SemanticStore P) :
    StoreAgreement σ σ :=
  fun _ _ => rfl

theorem StoreAgreement.trans {P : PureExpr} {σ₁ σ₂ σ₃ : SemanticStore P}
    (h₁ : StoreAgreement σ₁ σ₂) (h₂ : StoreAgreement σ₂ σ₃) :
    StoreAgreement σ₁ σ₃ := by
  intro x h_def₁
  -- σ₁ x = σ₂ x from h₁; need σ₂ x = σ₃ x from h₂, which needs isDefined σ₂ [x].
  have h12 : σ₁ x = σ₂ x := h₁ x h_def₁
  have h_def₂ : isDefined σ₂ [x] := by
    intro v hv
    rw [List.mem_singleton] at hv
    -- hv : v = x; rewrite goal to be about x
    rw [hv]
    have h := h_def₁ x (List.mem_singleton.mpr rfl)
    -- h : (σ₁ x).isSome = true; rewrite via h12
    rw [← h12]; exact h
  have h23 : σ₂ x = σ₃ x := h₂ x h_def₂
  exact h12.trans h23

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

/-- The boolean evaluator and the general evaluator are in agreement
-- only defined conservatively,
-- since there could be coercions like [1 >>= True] and [0 >>= False]
-- or that when δ evaluates to none, δP evaluates to False
  -/
def WellFormedSemanticEvalBool {P : PureExpr} [HasBool P] [HasNot P]
    (δ : SemanticEval P) : Prop :=
    ∀ σ e,
      (δ σ e = some Imperative.HasBool.tt ↔ δ σ (Imperative.HasNot.not e) = (some HasBool.ff)) ∧
      (δ σ e = some Imperative.HasBool.ff ↔ δ σ (Imperative.HasNot.not e) = (some HasBool.tt))

def WellFormedSemanticEvalVal {P : PureExpr} [HasVal P]
    (δ : SemanticEval P) : Prop :=
  -- evaluator only evaluates to values
    (∀ v v' σ, δ σ v = some v' → HasVal.value v') ∧
  -- evaluator is identity on values
    (∀ v' σ, HasVal.value v' → δ σ v' = some v')

@[expose] def WellFormedSemanticEvalVar {P : PureExpr} [HasFvar P] (δ : SemanticEval P)
    : Prop := (∀ e v σ, HasFvar.getFvar e = some v → δ σ e = σ v)

@[expose] def WellFormedSemanticEvalExprCongr {P : PureExpr} [HasVarsPure P P.Expr] (δ : SemanticEval P)
    : Prop := ∀ e σ σ', (∀ x ∈ HasVarsPure.getVars e, σ x = σ' x) → δ σ e = δ σ' e

/-- A successful evaluation implies all the read-vars are defined. -/
@[expose] def WellFormedSemanticEvalDef {P : PureExpr} [HasVarsPure P P.Expr]
    (δ : SemanticEval P) : Prop :=
  ∀ e v σ, δ σ e = some v → isDefined σ (HasVarsPure.getVars e)

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
inductive EvalCmd [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] :
  SemanticEval P → SemanticStore P → Cmd P → SemanticStore P → Bool → Prop where
  /-- If `e` evaluates to a value `v`, initialize `x` according to `InitState`. -/
  | eval_init :
    δ σ e = .some v →
    InitState P σ x v σ' →
    WellFormedSemanticEvalVar δ →
    WellFormedSemanticEvalExprCongr δ →
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
    WellFormedSemanticEvalExprCongr δ →
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
    WellFormedSemanticEvalExprCongr δ →
    ----
    EvalCmd δ σ (.assert _ e _) σ false

  /-- Assert fails: `e` does not evaluate to true, failure flag is set.
      The store is unchanged — the command is an unconditional skip on the
      store, but the failure flag records the violation. -/
  | eval_assert_fail :
    δ σ e = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    WellFormedSemanticEvalExprCongr δ →
    ----
    EvalCmd δ σ (.assert _ e _) σ true

  /-- If `e` evaluates to true in `σ`, evaluate to the same `σ`. -/
  | eval_assume :
    δ σ e = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    WellFormedSemanticEvalExprCongr δ →
    ----
    EvalCmd δ σ (.assume _ e _) σ false

  /-- A cover, when encountered, is essentially a skip. -/
  | eval_cover :
    WellFormedSemanticEvalBool δ →
    ----
    EvalCmd δ σ (.cover _ e _) σ false

end section

end -- public section
