/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Imperative.StmtSemantics
import Strata.Languages.Boogie.OldExpressions

---------------------------------------------------------------------

namespace Boogie

/-- expressions that can't be reduced when evaluating -/
inductive Value : Boogie.Expression.Expr → Prop where
  | const :  Value (.const _)
  | bvar  :  Value (.bvar _)
  | op    :  Value (.op _ _)
  | abs   :  Value (.abs _ _)

open Imperative

instance : HasVal Boogie.Expression where value := Value

instance : HasFvar Boogie.Expression where
  mkFvar := (.fvar · none)
  getFvar
  | .fvar v _ => some v
  | _ => none

@[match_pattern]
def Boogie.true : Boogie.Expression.Expr := .boolConst Bool.true
@[match_pattern]
def Boogie.false : Boogie.Expression.Expr := .boolConst Bool.false

instance : HasBool Boogie.Expression where
  tt := Boogie.true
  ff := Boogie.false

instance : HasNot Boogie.Expression where
  not
  | Boogie.true => Boogie.false
  | Boogie.false => Boogie.true
  | e => Lambda.LExpr.app Lambda.boolNotFunc.opExpr e

abbrev BoogieEval := SemanticEval Expression
abbrev BoogieStore := SemanticStore Expression

def WellFormedBoogieEvalCong (δ : BoogieEval) : Prop :=
    (∀ e₁ e₁' σ₀ σ σ₀' σ',
      δ σ₀ σ e₁ = δ σ₀' σ' e₁' →
      (∀ ty, δ σ₀ σ (.abs ty e₁) = δ σ₀' σ' (.abs ty e₁')) ∧
      (∀ info, δ σ₀ σ (.mdata info e₁) = δ σ₀' σ' (.mdata info e₁')) ∧
    -- binary congruence
    (∀ e₂ e₂',
      δ σ₀ σ e₂ = δ σ₀' σ' e₂' →
      δ σ₀ σ (.app e₁ e₂) = δ σ₀' σ' (.app e₁' e₂') ∧
      δ σ₀ σ (.eq e₁ e₂) = δ σ₀' σ' (.eq e₁' e₂') ∧
      (∀ k ty, δ σ₀ σ (.quant k ty e₁ e₂) = δ σ₀' σ' (.quant k ty e₁' e₂')) ∧
    -- ternary congruence
    (∀ e₃ e₃',
      δ σ₀ σ e₃ = δ σ₀' σ' e₃' →
      δ σ₀ σ (.ite e₃ e₁ e₂) = δ σ₀' σ' (.ite e₃' e₁' e₂')
    ))
    )

inductive EvalExpressions {P} [HasVarsPure P P.Expr] : SemanticEval P → SemanticStore P → SemanticStore P → List P.Expr → List P.Expr → Prop where
  | eval_none :
    EvalExpressions δ σ₀ σ [] []
  | eval_some :
    isDefined σ (HasVarsPure.getVars e) →
    δ σ₀ σ e = .some v →
    EvalExpressions δ σ₀ σ es vs →
    EvalExpressions δ σ₀ σ (e :: es) (v :: vs)

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
def WellFormedBoogieEvalTwoState (δ : BoogieEval) (σ₀ σ : BoogieStore) : Prop :=
    open Boogie.OldExpressions in
      (∃ vs vs' σ₁, HavocVars σ₀ vs σ₁ ∧ InitVars σ₁ vs' σ) ∧
      (∀ vs vs' σ₀ σ₁ σ,
        (HavocVars σ₀ vs σ₁ ∧ InitVars σ₁ vs' σ) →
        -- if the variable is modified, then old variable should lookup in the old store
        ∀ v,
          (v ∈ vs → ∀ oty ty, δ σ₀ σ (@oldVar oty v ty) = σ₀ v) ∧
        -- if the variable is not modified, then old variable is identity
          (¬ v ∈ vs → ∀ oty ty, δ σ₀ σ (@oldVar oty v ty) = σ v)) ∧
      -- evaluating on an old complex expression is the same as evlauating on its normal form
      -- TODO: can possibly break this into more sub-components, proving it using congruence and normalization property
      -- Might not be needed if we assume all expressions are normalized
      (∀ e σ₀ σ, δ σ₀ σ e = δ σ₀ σ (normalizeOldExpr e))

inductive EvalCommand : (String → Option Procedure)  → BoogieEval →
  BoogieStore → BoogieStore → Command → BoogieStore → Prop where
  | cmd_sem {π δ σ₀ σ c σ'} :
    Imperative.EvalCmd (P:=Expression) δ σ₀ σ c σ' →
    ----
    EvalCommand π δ σ₀ σ (CmdExt.cmd c) σ'

  /-
  NOTE: If π is NOT the first implicit variable below, Lean complains as
  follows; wish this error message actually mentioned which local variable was
  the problematic one.

  invalid nested inductive datatype 'Imperative.EvalStmts', nested inductive
  datatypes parameters cannot contain local variables.

  Here's a Zulip thread that can shed some light on this error message:
  https://leanprover-community.github.io/archive/stream/270676-lean4/topic/nested.20inductive.20datatypes.20parameters.20cannot.20contain.20local.20v.html
  -/
  | call_sem {π δ σ₀ σ args vals oVals σA σAO σR n p modvals lhs σ'} :
    π n = .some p →
    EvalExpressions (P:=Expression) δ σ₀ σ args vals →
    ReadValues σ lhs oVals →
    WellFormedSemanticEvalVal δ →
    WellFormedSemanticEvalVar δ →
    WellFormedSemanticEvalBool δ →
    WellFormedBoogieEvalTwoState δ σ₀ σ →

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
      δ σAO σAO pre = .some HasBool.tt) →
    @Imperative.EvalStmts Expression Command (EvalCommand π) _ _ _ _ _ _ δ σAO σAO p.body σR →
    -- Postconditions, if any, must be satisfied for execution to continue.
    (∀ post, (Procedure.Spec.getCheckExprs p.spec.postconditions).contains post →
      isDefinedOver (HasVarsPure.getVars) σAO post ∧
      δ σAO σR post = .some HasBool.tt) →

    ReadValues σR (ListMap.keys (p.header.outputs) ++ p.spec.modifies) modvals →
    UpdateStates σ (lhs ++ p.spec.modifies) modvals σ' →
    ----
    EvalCommand π δ σ₀ σ (CmdExt.call lhs n args) σ'

abbrev EvalStatement (π : String → Option Procedure) : BoogieEval →
    BoogieStore → BoogieStore → Statement → BoogieStore → Prop :=
  Imperative.EvalStmt Expression Command (EvalCommand π)

abbrev EvalStatements (π : String → Option Procedure) : BoogieEval →
    BoogieStore → BoogieStore → List Statement → BoogieStore → Prop :=
  Imperative.EvalStmts Expression Command (EvalCommand π)

inductive EvalCommandContract : (String → Option Procedure)  → BoogieEval →
  BoogieStore → BoogieStore → Command → BoogieStore → Prop where
  | cmd_sem {π δ σ₀ σ c σ'} :
    Imperative.EvalCmd (P:=Expression) δ σ₀ σ c σ' →
    ----
    EvalCommandContract π δ σ₀ σ (CmdExt.cmd c) σ'

  | call_sem {π δ σ₀ σ args oVals vals σA σAO σO σR n p modvals lhs σ'} :
    π n = .some p →
    EvalExpressions (P:=Boogie.Expression) δ σ₀ σ args vals →
    ReadValues σ lhs oVals →
    WellFormedSemanticEvalVal δ →
    WellFormedSemanticEvalVar δ →
    WellFormedSemanticEvalBool δ →
    WellFormedBoogieEvalTwoState δ σ₀ σ →

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
      δ σAO σAO pre = .some HasBool.tt) →
    HavocVars σAO (ListMap.keys p.header.outputs) σO →
    HavocVars σO p.spec.modifies σR →
    -- Postconditions, if any, must be satisfied for execution to continue.
    (∀ post, (Procedure.Spec.getCheckExprs p.spec.postconditions).contains post →
      isDefinedOver (HasVarsPure.getVars) σAO post ∧
      δ σO σR post = .some HasBool.tt) →
    ReadValues σR (ListMap.keys (p.header.outputs) ++ p.spec.modifies) modvals →
    UpdateStates σ (lhs ++ p.spec.modifies) modvals σ' →
    ----
    EvalCommandContract π δ σ₀ σ (.call lhs n args) σ'

abbrev EvalStatementContract (π : String → Option Procedure) : BoogieEval →
    BoogieStore → BoogieStore → Statement → BoogieStore → Prop :=
  Imperative.EvalStmt Expression Command (EvalCommandContract π)

abbrev EvalStatementsContract (π : String → Option Procedure) : BoogieEval →
    BoogieStore → BoogieStore → List Statement → BoogieStore → Prop :=
  Imperative.EvalStmts Expression Command (EvalCommandContract π)
