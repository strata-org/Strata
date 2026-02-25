/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprWF
import Strata.DL.Imperative.StmtSemantics
import Strata.Languages.Core.OldExpressions

---------------------------------------------------------------------

namespace Core

/-- expressions that can't be reduced when evaluating -/
inductive Value : Core.Expression.Expr → Prop where
  | const :  Value (.const () _)
  | bvar  :  Value (.bvar () _)
  | op    :  Value (.op () _ _)
  | abs   :  Value (.abs () _ _)

open Imperative

instance : HasVal Core.Expression where value := Value

instance : HasFvar Core.Expression where
  mkFvar := (.fvar () · none)
  getFvar
  | .fvar _ v _ => some v
  | _ => none

instance : HasSubstFvar Core.Expression where
  substFvar := Lambda.LExpr.substFvar

@[match_pattern]
def Core.true : Core.Expression.Expr := .boolConst () Bool.true
@[match_pattern]
def Core.false : Core.Expression.Expr := .boolConst () Bool.false

instance : HasBool Core.Expression where
  tt := Core.true
  ff := Core.false

instance : HasNot Core.Expression where
  not
  | Core.true => Core.false
  | Core.false => Core.true
  | e => Lambda.LExpr.app () (Lambda.boolNotFunc (T:=CoreLParams)).opExpr e

abbrev CoreEval := SemanticEval Expression
abbrev CoreStore := SemanticStore Expression

/-- If a compound expression is defined, its subexpressions are defined. -/
structure WellFormedCoreEvalDefinedness (δ : CoreEval) : Prop where
  absdef:   (∀ σ m ty e, (δ σ (.abs m ty e)).isSome → (δ σ e).isSome)
  appdef:   (∀ σ m e₁ e₂, (δ σ (.app m e₁ e₂)).isSome → (δ σ e₁).isSome ∧ (δ σ e₂).isSome)
  eqdef:    (∀ σ m e₁ e₂, (δ σ (.eq m e₁ e₂)).isSome → (δ σ e₁).isSome ∧ (δ σ e₂).isSome)
  quantdef: (∀ σ m k ty tr e, (δ σ (.quant m k ty tr e)).isSome → (δ σ tr).isSome ∧ (δ σ e).isSome)
  itedef:   (∀ σ m c t e, (δ σ (.ite m c t e)).isSome → (δ σ c).isSome ∧ (δ σ t).isSome ∧ (δ σ e).isSome)

structure WellFormedCoreEvalCong (δ : CoreEval): Prop where
    abscongr: (∀ σ σ' e₁ e₁' ,
      δ σ e₁ = δ σ' e₁' →
      (∀ m ty, δ σ (.abs m ty e₁) = δ σ' (.abs m ty e₁')))
    appcongr: (∀ σ σ' m e₁ e₁' e₂ e₂',
      δ σ e₁ = δ σ' e₁' →
      δ σ e₂ = δ σ' e₂' →
      (δ σ (.app m e₁ e₂) = δ σ' (.app m e₁' e₂')))
    eqcongr: (∀ σ σ' m e₁ e₁' e₂ e₂',
      δ σ e₁ = δ σ' e₁' →
      δ σ e₂ = δ σ' e₂' →
      (δ σ (.eq m e₁ e₂) = δ σ' (.eq m e₁' e₂')))
    quantcongr: (∀ σ σ' m k ty e₁ e₁' e₂ e₂',
      δ σ e₁ = δ σ' e₁' →
      δ σ e₂ = δ σ' e₂' →
      (δ σ (.quant m k ty e₁ e₂) = δ σ' (.quant m k ty e₁' e₂')))
    itecongr: (∀ σ σ' m e₁ e₁' e₂ e₂' e₃ e₃',
      δ σ e₁ = δ σ' e₁' →
      δ σ e₂ = δ σ' e₂' →
      δ σ e₃ = δ σ' e₃' →
      (δ σ (.ite m e₃ e₁ e₂) = δ σ' (.ite m e₃' e₁' e₂')))
    /-- Definedness-propagation properties for compound expressions. -/
    definedness : WellFormedCoreEvalDefinedness δ

inductive EvalExpressions {P} [HasVarsPure P P.Expr] : SemanticEval P → SemanticStore P → List P.Expr → List P.Expr → Prop where
  | eval_none :
    EvalExpressions δ σ [] []
  | eval_some :
    isDefined σ (HasVarsPure.getVars e) →
    δ σ e = .some v →
    EvalExpressions δ σ es vs →
    EvalExpressions δ σ (e :: es) (v :: vs)

inductive ReadValues : SemanticStore P → List P.Ident → List P.Expr → Prop where
  | read_none :
    ReadValues _ [] []
  | read_some :
    σ x = .some v →
    ReadValues σ xs vs →
    ReadValues σ (x :: xs) (v :: vs)

inductive UpdateStates : SemanticStore P → List P.Ident → List P.Expr → SemanticStore P → Prop where
  | update_none :
    UpdateStates σ [] [] σ
  | update_some :
    UpdateState P σ x v σ' →
    UpdateStates σ' xs vs σ'' →
    UpdateStates σ (x :: xs) (v :: vs) σ''

inductive InitStates : SemanticStore P → List P.Ident → List P.Expr → SemanticStore P → Prop where
  | init_none :
    InitStates σ [] [] σ
  | init_some :
    InitState P σ x v σ' →
    InitStates σ' xs vs σ'' →
    InitStates σ (x :: xs) (v :: vs) σ''

inductive InitVars : SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | init_none :
    InitVars σ [] σ
  | init_some :
    InitState P σ x v σ' →
    InitVars σ' xs σ'' →
    InitVars σ (x :: xs) σ''

inductive HavocVars : SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | update_none :
    HavocVars σ [] σ
  | update_some :
    UpdateState P σ x v σ' →
    HavocVars σ' xs σ'' →
    HavocVars σ (x :: xs) σ''

inductive TouchVars : SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | none :
    TouchVars σ [] σ
  | init_some :
    InitState P σ x v σ' →
    TouchVars σ' xs σ'' →
    TouchVars σ (x :: xs) σ''
  | update_some :
    UpdateState P σ x v σ' →
    TouchVars σ' xs σ'' →
    TouchVars σ (x :: xs) σ''

inductive Inits : SemanticStore P → SemanticStore P → Prop where
  | init : InitVars σ xs σ' → Inits σ σ'

def updatedState
  (σ : SemanticStore P)
  (ident : P.Ident)
  (val : P.Expr)
  : SemanticStore P :=
  λ k ↦ if (@Decidable.decide (k = ident) (P.EqIdent k ident))
    then some val
    else (σ k)

def updatedStates'
  (σ : SemanticStore P)
  (idvals : List (P.Ident × P.Expr))
  : SemanticStore P :=
  match idvals with
  | [] => σ
  | (ident, val) :: rest  => updatedStates' (updatedState σ ident val) rest

def updatedStates
  (σ : SemanticStore P)
  (idents : List P.Ident)
  (vals : List P.Expr)
  : SemanticStore P :=
  updatedStates' σ $ idents.zip vals

/-- The evaluator handles old expressions correctly
-- It should specify the exact expression form that would map to the old store
-- This can be used to implement more general two-state functions, as in Dafny
-- https://dafny.org/latest/DafnyRef/DafnyRef#sec-two-state
-- where this condition will be asserted at procedures utilizing those two-state functions
-/
def WellFormedCoreEvalTwoState (δ : CoreEval) (σ₀ σ : CoreStore) : Prop :=
    open Core.OldExpressions in
      (∃ vs vs' σ₁, HavocVars σ₀ vs σ₁ ∧ InitVars σ₁ vs' σ) ∧
      (∀ vs vs' σ₀ σ₁ σ,
        (HavocVars σ₀ vs σ₁ ∧ InitVars σ₁ vs' σ) →
        ∀ v,
          (v ∈ vs →
            ∀ oty mApp mOp mVar ty,
              δ σ (@oldVar (tyold := oty) mApp mOp mVar v ty) = σ₀ v) ∧
        -- if the variable is not modified, then old variable is identity
          (¬ v ∈ vs →
            ∀ oty mApp mOp mVar ty,
              δ σ (@oldVar (tyold := oty) mApp mOp mVar v ty) = σ v)) ∧
      -- evaluating on an old complex expression is the same as evlauating on its normal form
      -- TODO: can possibly break this into more sub-components, proving it using congruence and normalization property
      -- Might not be needed if we assume all expressions are normalized
      (∀ e σ, δ σ e = δ σ (normalizeOldExpr e))

/-! ### Closure Capture for Function Declarations -/

/--
Build a list of substitutions from the store for the given identifiers.
Returns pairs of (identifier, value) for each identifier that has a value in the store.
-/
def buildSubstitutions (σ : CoreStore) (ids : List Expression.Ident) : List (Expression.Ident × Expression.Expr) :=
  ids.filterMap (fun id =>
    match σ id with
    | some v => some (id, v)
    | none => none)

/--
Apply closure capture to a function declaration by substituting current variable
values into the function body and axioms. Variables that are function parameters
are not substituted (they are bound, not free in the closure sense).
-/
def closureCapture
    (σ : CoreStore) (decl : PureFunc Expression) : PureFunc Expression :=
  let paramNames := decl.inputs.map (·.1)
  -- Get free variables from body (if it exists), excluding parameters
  let bodyFreeVars := match decl.body with
    | some body => (HasVarsPure.getVars body).filter (· ∉ paramNames)
    | none => []
  -- Get free variables from axioms, excluding parameters
  let axiomFreeVars := decl.axioms.flatMap (fun ax =>
    (HasVarsPure.getVars ax).filter (· ∉ paramNames))
  -- Combine and deduplicate
  let allFreeVars := (bodyFreeVars ++ axiomFreeVars).eraseDups
  -- Build substitutions from the store
  let substs := buildSubstitutions σ allFreeVars
  -- Apply substitutions to body and axioms
  { decl with
    body := decl.body.map (fun b => HasSubstFvar.substFvars b substs)
    axioms := decl.axioms.map (fun ax => HasSubstFvar.substFvars ax substs) }

/--
Extend the evaluator with a new function definition by capturing the closure.
The closure capture substitutes current variable values from the store into
the function body and axioms. The returned evaluator handles applications of
the newly declared function by substituting arguments into the captured body.

Takes a parameter `φ` that specifies how to extend the evaluator with a captured
closure (without the store, since closure capture is handled here).
-/
def EvalPureFunc (φ : CoreEval → PureFunc Expression → CoreEval) : Imperative.ExtendEval Expression :=
  fun δ σ decl =>
    let capturedDecl := closureCapture σ decl
    φ δ capturedDecl

inductive EvalCommand (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) : CoreEval →
  CoreStore → Command → CoreStore → Prop where
  | cmd_sem {δ σ c σ'} :
    Imperative.EvalCmd Expression δ σ c σ' →
    ----
    EvalCommand π φ δ σ (CmdExt.cmd c) σ'

  /-
  NOTE: If π is NOT the first implicit variable below, Lean complains as
  follows; wish this error message actually mentioned which local variable was
  the problematic one.

  invalid nested inductive datatype 'Imperative.EvalBlock', nested inductive
  datatypes parameters cannot contain local variables.

  Here's a Zulip thread that can shed some light on this error message:
  https://leanprover-community.github.io/archive/stream/270676-lean4/topic/nested.20inductive.20datatypes.20parameters.20cannot.20contain.20local.20v.html
  -/
  | call_sem {δ σ₀ σ args vals oVals σA σAO σR n p modvals lhs σ' δ'} :
    π n = .some p →
    EvalExpressions (P:=Expression) δ σ args vals →
    ReadValues σ lhs oVals →
    WellFormedSemanticEvalVal δ →
    WellFormedSemanticEvalVar δ →
    WellFormedSemanticEvalBool δ →
    WellFormedCoreEvalTwoState δ σ₀ σ →

    isDefinedOver (HasVarsTrans.allVarsTrans π) σ (Statement.call lhs n args) →

    -- Note: this puts caller and callee names in the same store. If the program is type correct, however,
    -- this can't change semantics. Caller names that aren't visible to the callee won't be used. Caller
    -- names that overlap with callee names will be replaced.
    InitStates σ (ListMap.keys (p.header.inputs)) vals σA →

    -- need to initialize to the values of lhs, due to output variables possibly occuring in preconditions
    InitStates σA (ListMap.keys (p.header.outputs)) oVals σAO →

    -- Preconditions, if any, must be satisfied for execution to continue.
    (∀ pre, (Procedure.Spec.getCheckExprs p.spec.preconditions).contains pre →
      isDefinedOver (HasVarsPure.getVars) σAO pre ∧
      δ σAO pre = .some HasBool.tt) →
    @Imperative.EvalBlock Expression Command (EvalCommand π φ) (EvalPureFunc φ) _ _ _ _ _ _ _ δ σAO p.body σR δ' →
    -- Postconditions, if any, must be satisfied for execution to continue.
    (∀ post, (Procedure.Spec.getCheckExprs p.spec.postconditions).contains post →
      isDefinedOver (HasVarsPure.getVars) σAO post ∧
      δ σR post = .some HasBool.tt) →

    ReadValues σR (ListMap.keys (p.header.outputs) ++ p.spec.modifies) modvals →
    UpdateStates σ (lhs ++ p.spec.modifies) modvals σ' →
    ----
    EvalCommand π φ δ σ (CmdExt.call lhs n args) σ'

abbrev EvalStatement (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) : CoreEval →
    CoreStore → Statement → CoreStore → CoreEval → Prop :=
  Imperative.EvalStmt Expression Command (EvalCommand π φ) (EvalPureFunc φ)

abbrev EvalStatements (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) : CoreEval →
    CoreStore → List Statement → CoreStore → CoreEval → Prop :=
  Imperative.EvalBlock Expression Command (EvalCommand π φ) (EvalPureFunc φ)

inductive EvalCommandContract : (String → Option Procedure)  → CoreEval →
  CoreStore → Command → CoreStore → Prop where
  | cmd_sem {π δ σ c σ'} :
    Imperative.EvalCmd Expression δ σ c σ' →
    ----
    EvalCommandContract π δ σ (CmdExt.cmd c) σ'

  | call_sem {π δ σ args oVals vals σA σAO σO σR n p modvals lhs σ'} :
    π n = .some p →
    EvalExpressions (P:=Core.Expression) δ σ args vals →
    ReadValues σ lhs oVals →
    WellFormedSemanticEvalVal δ →
    WellFormedSemanticEvalVar δ →
    WellFormedSemanticEvalBool δ →
    WellFormedCoreEvalTwoState δ σ₀ σ →

    isDefinedOver (HasVarsTrans.allVarsTrans π) σ (Statement.call lhs n args) →

    -- Note: this puts caller and callee names in the same store. If the program is type correct, however,
    -- this can't change semantics. Caller names that aren't visible to the callee won't be used. Caller
    -- names that overlap with callee names will be replaced.
    InitStates σ (ListMap.keys (p.header.inputs)) vals σA →

    -- need to initialize to the values of lhs, due to output variables possibly occuring in preconditions
    InitStates σA (ListMap.keys (p.header.outputs)) oVals σAO →

    -- Preconditions, if any, must be satisfied for execution to continue.
    (∀ pre, (Procedure.Spec.getCheckExprs p.spec.preconditions).contains pre →
      isDefinedOver (HasVarsPure.getVars) σAO pre ∧
      δ σAO pre = .some HasBool.tt) →
    HavocVars σAO (ListMap.keys p.header.outputs) σO →
    HavocVars σO p.spec.modifies σR →
    -- Postconditions, if any, must be satisfied for execution to continue.
    (∀ post, (Procedure.Spec.getCheckExprs p.spec.postconditions).contains post →
      isDefinedOver (HasVarsPure.getVars) σAO post ∧
      δ σR post = .some HasBool.tt) →
    ReadValues σR (ListMap.keys (p.header.outputs) ++ p.spec.modifies) modvals →
    UpdateStates σ (lhs ++ p.spec.modifies) modvals σ' →
    ----
    EvalCommandContract π δ σ (.call lhs n args) σ'

abbrev EvalStatementContract (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) : CoreEval →
    CoreStore → Statement → CoreStore → CoreEval → Prop :=
  Imperative.EvalStmt Expression Command (EvalCommandContract π) (EvalPureFunc φ)

abbrev EvalStatementsContract (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) : CoreEval →
    CoreStore → List Statement → CoreStore → CoreEval → Prop :=
  Imperative.EvalBlock Expression Command (EvalCommandContract π) (EvalPureFunc φ)
