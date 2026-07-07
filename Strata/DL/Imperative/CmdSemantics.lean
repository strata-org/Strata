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
lookups.
-/
@[expose] abbrev SemanticStore := P.Ident → Option P.Expr
@[expose] abbrev SemanticEval := P.Factory → SemanticStore P → P.Expr → Option P.Expr
@[expose] abbrev SemanticEvalBool := P.Factory → SemanticStore P → P.Expr → Option Bool

/--
Evaluation relation of an Imperative command `Cmd`.
Commands do not modify the evaluator - only `funcDecl` statements do.

The Bool flag reports whether the command observed
a failure (e.g., an assertion whose guard is false).  The `Bool` is `true`
when the command signals a failure.
-/
@[expose] abbrev EvalCmdParam (P : PureExpr) (Cmd : Type) :=
  P.Factory → SemanticStore P → Cmd → SemanticStore P → Bool → Prop

/-! ### Well-Formedness of `SemanticStore` -/

/-- A store is well-formed when every binding it holds is a value.  The
    predicates below only constrain such stores, so the value rule and the var
    rule stay jointly satisfiable (an arbitrary store could bind a variable to a
    non-value). -/
@[expose] def WellFormedStore {P : PureExpr} [HasVal P] (σ : SemanticStore P) (f : P.Factory) : Prop :=
    ∀ x v, σ x = some v → HasVal.value f v


/-! ### Well-Formedness of `SemanticEval` -/

/-- The evaluator respects Boolean negation: for any store `σ` and expression
    `e`, `P.eval f σ e = some tt` iff `P.eval f σ (not e) = some ff`, and
    dually. -/
@[expose] def WellFormedSemanticEvalBool {P : PureExpr} [HasBool P] [HasBoolOps P]
    (f : P.Factory) : Prop :=
    ∀ σ e,
      (P.eval f σ e = some Imperative.HasBool.tt ↔ P.eval f σ (Imperative.HasBoolOps.not e) = (some HasBool.ff)) ∧
      (P.eval f σ e = some Imperative.HasBool.ff ↔ P.eval f σ (Imperative.HasBoolOps.not e) = (some HasBool.tt))

/-- Well-formedness of a `SemanticEval`'s value behavior, split into named
    clauses. -/
structure WellFormedSemanticEvalVal {P : PureExpr} [HasVal P]
    (f : P.Factory) : Prop where
  /-- The evaluator produces only values (on well-formed stores). -/
  outputsAreValues : ∀ v v' σ, WellFormedStore σ f → P.eval f σ v = some v' → HasVal.value f v'
  /-- The evaluator is the identity on values. -/
  identityOnValues : ∀ v' σ, HasVal.value f v' → P.eval f σ v' = some v'

/-- The evaluator resolves free variables via the store: on a well-formed
    store, evaluating a free-variable expression yields its store binding. -/
@[expose] def WellFormedSemanticEvalVar {P : PureExpr} [HasVal P] [HasFvar P]
    (f : P.Factory) : Prop :=
    (∀ e v σ, WellFormedStore σ f → HasFvar.getFvar e = some v → P.eval f σ e = σ v)

/-- The evaluator agrees on well-formed stores that agree on the free variables
    of the expression under evaluation. -/
@[expose] def WellFormedSemanticEvalExprCongr {P : PureExpr} [HasVal P] [HasFvars P]
    (f : P.Factory) : Prop :=
    ∀ e σ σ', WellFormedStore σ f → WellFormedStore σ' f →
      (∀ x ∈ HasFvars.getFvars e, σ x = σ' x) → P.eval f σ e = P.eval f σ' e

/-- Well-formedness for the integer fragment of a factory-based evaluator. -/
structure WellFormedSemanticEvalInt {P : PureExpr}
    [HasBool P] [HasFvars P] [HasInt P] [HasIntOps P]
    (f : P.Factory) : Prop where
  ltReduces : ∀ σ x y nx ny,
    P.eval f σ x = some nx → HasInt.isNumeral nx = Bool.true →
    P.eval f σ y = some ny → HasInt.isNumeral ny = Bool.true →
    P.eval f σ (HasIntOps.lt x y) = some HasBool.tt ∨
    P.eval f σ (HasIntOps.lt x y) = some HasBool.ff

/-- The evaluator is monotone under store extension: if `σ'` retains every
    binding of `σ`, a successful evaluation at `σ` succeeds identically at `σ'`.
    A successful result depends only on the bindings the evaluation reads, so
    growing the store preserves it. -/
@[expose] def WellFormedSemanticEvalMono {P : PureExpr}
    (f : P.Factory) : Prop :=
    ∀ e v σ σ', (∀ x w, σ x = some w → σ' x = some w) →
      P.eval f σ e = some v → P.eval f σ' e = some v

/-- Bundle of well-formedness conditions on `P.eval` against a factory `f`. -/
structure WellFormedSemanticEval {P : PureExpr} [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P]
    (f : P.Factory) : Prop where
  /-- The evaluator respects boolean negation:
      `eval e = some tt` iff `eval (not e) = some ff`, and dually. -/
  bool : WellFormedSemanticEvalBool f
  /-- The evaluator only outputs values and is the identity on values. -/
  val : WellFormedSemanticEvalVal f
  /-- The evaluator resolves free variables via the store. -/
  var : WellFormedSemanticEvalVar f
  /-- The evaluator agrees on stores that agree on free variables. -/
  exprCongr : WellFormedSemanticEvalExprCongr f
  /-- The evaluator reduces integer comparisons to booleans. -/
  int : WellFormedSemanticEvalInt f
  /-- The evaluator is monotone under store extension. -/
  mono : WellFormedSemanticEvalMono f


/-- ### Predicates on `SemanticStore`s -/

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


/-! ### Formal Semantics of Command. -/

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
lookup (`σ`) and expression evaluation (`P.eval`) functions.
Commands do not modify the evaluator - only `funcDecl` statements do.

The `Bool` output parameter is a *failure flag*: `true` when the command
signals an assertion failure, `false` otherwise.  Only `eval_assert_fail`
sets it to `true`; all other constructors report `false`.

The failure flag is accumulated in `Env.hasFailure` by the statement
semantics (`EvalStmt`).
-/
inductive EvalCmd [HasFvar P] [HasBool P] [HasBoolOps P] :
  P.Factory → SemanticStore P → Cmd P → SemanticStore P → Bool → Prop where
  /-- If `e` evaluates to a value `v`, initialize `x` according to `InitState`. -/
  | eval_init :
    P.eval f σ e = .some v →
    InitState P σ x v σ' →
    WellFormedSemanticEvalVar (P := P) f →
    ---
    EvalCmd f σ (.init x _ (.det e) _) σ' false

  /-- Initialize `x` with an unconstrained value (havoc semantics).  The
  havoc'd value `v` is still required to be a value, so a nondet write
  preserves store well-formedness. -/
  | eval_init_unconstrained :
    InitState P σ x v σ' →
    HasVal.value f v →
    WellFormedSemanticEvalVar (P := P) f →
    ---
    EvalCmd f σ (.init x _ .nondet _) σ' false

  /-- If `e` evaluates to a value `v`, assign `x` according to `UpdateState`. -/
  | eval_set :
    P.eval f σ e = .some v →
    UpdateState P σ x v σ' →
    WellFormedSemanticEvalVar (P := P) f →
    ----
    EvalCmd f σ (.set x (.det e) _) σ' false

  /-- Assign `x` an arbitrary value `v` according to `UpdateState`.  The
  havoc'd value `v` is still required to be a value, so a nondet write
  preserves store well-formedness. -/
  | eval_set_nondet :
    UpdateState P σ x v σ' →
    HasVal.value f v →
    WellFormedSemanticEvalVar (P := P) f →
    ----
    EvalCmd f σ (.set x .nondet _) σ' false

  /-- Assert passes: `e` evaluates to true, no failure. The store is unchanged. -/
  | eval_assert_pass :
    P.eval f σ e = .some HasBool.tt →
    WellFormedSemanticEvalBool (P := P) f →
    ----
    EvalCmd f σ (.assert _ e _) σ false

  /-- Assert fails: `e` does not evaluate to true, failure flag is set.
      The store is unchanged — the command is an unconditional skip on the
      store, but the failure flag records the violation. -/
  | eval_assert_fail :
    P.eval f σ e = .some HasBool.ff →
    WellFormedSemanticEvalBool (P := P) f →
    ----
    EvalCmd f σ (.assert _ e _) σ true

  /-- If `e` evaluates to true in `σ`, evaluate to the same `σ`. -/
  | eval_assume :
    P.eval f σ e = .some HasBool.tt →
    WellFormedSemanticEvalBool (P := P) f →
    ----
    EvalCmd f σ (.assume _ e _) σ false

  /-- A cover, when encountered, is essentially a skip. -/
  | eval_cover :
    WellFormedSemanticEvalBool (P := P) f →
    ----
    EvalCmd f σ (.cover _ e _) σ false

end section

end -- public section
