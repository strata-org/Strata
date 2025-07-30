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



import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.HasVars
import Strata.DL.Util.Map

---------------------------------------------------------------------

namespace Imperative

section

variable (P : PureExpr)

/-
These are intended to be as generic as possible, not using any specific
data structure. They'll probably usually be instantiated with map
lookups. The evaluation functions take two states: an old state and a
current state. This allows for two-state expressions and predicates.
-/
abbrev SemanticStore := P.Ident → Option P.Expr
abbrev SemanticEval := SemanticStore P → SemanticStore P → P.Expr → Option P.Expr
abbrev SemanticEvalBool := SemanticStore P → SemanticStore P → P.Expr → Option Bool
/--
Evaluation relation of an Imperative command `Cmd`.
-/
-- (FIXME) Change to a type class?
abbrev EvalCmdParam (P : PureExpr) (Cmd : Type) :=
  SemanticEval P → SemanticEvalBool P → SemanticStore P → SemanticStore P → Cmd →
  SemanticStore P → Prop

/-- ### Well-Formedness of `SemanticStore`s -/

def isDefined {P : PureExpr} (σ : SemanticStore P) (vs : List P.Ident) : Prop :=
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

theorem isDefinedCons :
  isDefined σ [v] →
  isDefined σ vs2 →
  isDefined σ (v :: vs2) := by
  intros Hd1 Hd2
  simp [isDefined] at *
  simp [Option.isSome] at *
  split <;> simp_all

theorem isDefinedApp :
  isDefined σ vs1 →
  isDefined σ vs2 →
  isDefined σ (vs1 ++ vs2) := by
  intros Hd1 Hd2
  simp [isDefined] at *
  intros id Hin
  simp [Option.isSome] at *
  cases Hin with
  | inl Hin =>
    split <;> simp
    specialize Hd1 id Hin; simp_all
  | inr Hin =>
    split <;> simp
    specialize Hd2 id Hin; simp_all

theorem isDefinedCons' :
  isDefined σ (h :: t) →
  isDefined σ [h] ∧ isDefined σ t := by simp [isDefined] at *

theorem isDefinedApp' :
  isDefined σ (t1 ++ t2) →
  isDefined σ t1 ∧ isDefined σ t2 := by
  intros Hd
  simp [isDefined] at *
  apply And.intro
  . intros x Hin
    apply Hd; left; assumption
  . intros x Hin
    apply Hd; right; assumption

/-! ### Well-Formedness of `SemanticEval`s -/

/-- The boolean evaluator and the general evaluator are in agreement
-- only defined conservatively,
-- since there could be coercions like [1 >>= True] and [0 >>= False]
-- or that when δ evaluates to none, δP evaluates to False
  -/
def WellFormedSemanticEvalBool {P : PureExpr} [HasBool P] [HasBoolNeg P]
    (δ : SemanticEval P) (δP : SemanticEvalBool P) : Prop :=
    ∀ σ₀ σ e b,
      (δ σ₀ σ e = some Imperative.HasBool.tt ↔ δP σ₀ σ e = (some true)) ∧
      (δ σ₀ σ e = some Imperative.HasBool.ff ↔ δP σ₀ σ e = (some false)) ∧
      (δP σ₀ σ e = (some b) ↔ δP σ₀ σ (Imperative.HasBoolNeg.neg e) = (some (not b)))

def WellFormedSemanticEvalVal {P : PureExpr} [HasVal P]
    (δ : SemanticEval P) (σ₀ σ : SemanticStore P) : Prop :=
  -- stores only contain values
    (∀ v v', σ₀ v = some v' → HasVal.value v') ∧
    (∀ v v', σ v = some v' → HasVal.value v') ∧
  -- evaluator only evaluates to values
    (∀ v v' σ₀ σ, δ σ₀ σ v = some v' → HasVal.value v') ∧
  -- evaluator is identity on values
    (∀ v' σ₀ σ, HasVal.value v' → δ σ₀ σ v' = some v')

def WellFormedSemanticEvalVar {P : PureExpr} [HasFvar P] (δ : SemanticEval P)
    : Prop := (∀ e v σ₀ σ, HasFvar.getFvar e = some v → δ σ₀ σ e = σ v)

/--
An inductive rule for state update.
-/
inductive UpdateState : SemanticStore P → P.Ident → P.Expr → SemanticStore P → Prop where
  | update :
    σ x = .some v' →
    σ' x = .some v →
    (∀ y, x ≠ y → σ' y = σ y) →
    ----
    UpdateState σ x v σ'

/--
An inductive rule for state initialization.
-/
inductive InitState : SemanticStore P → P.Ident → P.Expr → SemanticStore P → Prop where
  | init :
    σ x = none →
    σ' x = .some v →
    (∀ y, x ≠ y → σ' y = σ y) →
    ----
    InitState σ x v σ'

/--
An inductively-defined operational semantics that depends on
environment lookup and evaluation functions for expressions.
-/
inductive EvalCmd [HasFvar P] [HasBool P] [HasBoolNeg P] :
  SemanticEval P → SemanticEvalBool P →
  SemanticStore P → SemanticStore P →
  Cmd P → SemanticStore P → Prop where
  | eval_init :
    δ σ₀ σ e = .some v →
    InitState P σ x v σ' →
    WellFormedSemanticEvalVar δ →
    ---
    EvalCmd δ δP σ₀ σ (.init x _ e _) σ'

  | eval_set :
    δ σ₀ σ e = .some v →
    UpdateState P σ x v σ' →
    WellFormedSemanticEvalVar δ →
    ----
    EvalCmd δ δP σ₀ σ (.set x e _) σ'

  | eval_havoc :
    UpdateState P σ x v σ' →
    WellFormedSemanticEvalVar δ →
    ----
    EvalCmd δ δP σ₀ σ (.havoc x _) σ'

  | eval_assert :
    δP σ₀ σ e = .some true →
    WellFormedSemanticEvalBool δ δP →
    ----
    EvalCmd δ δP σ₀ σ (.assert _ e _) σ

  | eval_assume :
    δP σ₀ σ e = .some true →
    WellFormedSemanticEvalBool δ δP →
    ----
    EvalCmd δ δP σ₀ σ (.assume _ e _) σ

end section

theorem InitStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  InitState P σ v e σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [Hsome]
    exact Hdef Hv'

theorem UpdateStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  UpdateState P σ v e σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [Hsome]
    exact Hdef Hv'
