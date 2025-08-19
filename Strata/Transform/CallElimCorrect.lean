/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Strata.Languages.Boogie.Env
import Strata.Languages.Boogie.Identifiers
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.ProgramType
import Strata.Languages.Boogie.WF
import Strata.DL.Lambda.Lambda
import Strata.Transform.CallElim
import Strata.DL.Imperative.CmdSemantics
import Strata.Languages.Boogie.StatementSemantics
import Strata.Languages.Boogie.StatementSemanticsProps
import Strata.DL.Util.ListUtils

/-! # Call Elimination Correctness Proof

  This file contains the main proof that the call elimination transformation is
  semantics preserving (see `callElimStatementCorrect`).
  Additionally, `callElimStmtsNoExcept` shows that the call elimination
  transformation always succeeds on well-formed statements.
-/

namespace CallElimCorrect
open Boogie CallElim

theorem BoogieIdent.isGlob_isGlobOrLocl :
  PredImplies (BoogieIdent.isGlob ·) (BoogieIdent.isGlobOrLocl ·) := by
  intros x H
  simp [BoogieIdent.isGlobOrLocl]
  exact Or.symm (Or.inr H)

theorem BoogieIdent.isLocl_isGlobOrLocl :
  PredImplies (BoogieIdent.isLocl ·) (BoogieIdent.isGlobOrLocl ·) := by
  intros x H
  simp [BoogieIdent.isGlobOrLocl]
  exact Or.symm (Or.inl H)

theorem BoogieIdent.Disjoint_isTemp_isGlobOrLocl :
  PredDisjoint (BoogieIdent.isTemp ·) (BoogieIdent.isGlobOrLocl ·) := by
  intros x H1 H2
  simp [BoogieIdent.isTemp] at H1
  simp [BoogieIdent.isGlobOrLocl] at H2
  split at H1 <;> simp_all
  cases H2 <;> simp [BoogieIdent.isGlob, BoogieIdent.isLocl] at *

theorem BoogieIdent.Disjoint_isLocl_isGlob :
  PredDisjoint (BoogieIdent.isLocl ·) (BoogieIdent.isGlob ·) := by
  intros x H1 H2
  simp [BoogieIdent.isLocl] at H1
  simp [BoogieIdent.isGlob] at H2
  split at H1 <;> simp_all

-- inidividual lemmas

theorem createHavocsApp :
createHavocs (a ++ b) = createHavocs a ++ createHavocs b := by
simp [createHavocs]

theorem createFvarsApp :
createFvars (a ++ b) = createFvars a ++ createFvars b := by
simp [createFvars]

theorem createFvarsLength :
(createFvars ls).length = ls.length := by
induction ls <;> simp [createFvars]

theorem filterIsGlobal_isSome :
  ident ∈ List.filter (isGlobalVar p) l →
  (p.find? DeclKind.var ident).isSome = true := by
  intros Hin
  simp [isGlobalVar] at Hin
  exact Hin.2

theorem getOldExprIdentTy_some : ∀ {p : Program} {id : Expression.Ident},
  (p.find? .var id).isSome = (getIdentTy? p id).isSome := by
  intros p id
  simp [Program.find?, getIdentTy?, Program.getVarTy?]
  split <;> simp_all

theorem getIdentTy!_store_same :
  getIdentTy! p x s = (Except.ok a', s') →
  s = s' := by
  intros H
  simp [getIdentTy!] at H
  generalize Hgt: (getIdentTy? p x) = gt at H
  split at H
  . cases H
  . simp [pure] at H
    cases H
    rfl

theorem getIdentTys!_store_same :
  getIdentTys! p xs s = (Except.ok a', s') →
  s = s' := by
  intros H
  induction xs generalizing s a' s' <;> simp [getIdentTys!, pure, ExceptT.pure, ExceptT.mk, StateT.pure] at H
  case nil =>
    cases H
    rfl
  case cons h t ih =>
    simp [bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont] at H
    split at H
    next heq =>
    split at H
    . simp [StateT.bind, bind] at H
      split at H
      next heq' =>
      simp [ExceptT.bindCont] at H
      split at H
      . have H1 := getIdentTy!_store_same heq
        have H2 := ih heq'
        simp [StateT.pure, pure] at H
        cases H
        simp_all
      . cases H
    . cases H

theorem getIdentTy!_no_throw :
  (p.find? .var ident).isSome = true →
  ∃ r, (runCallElimWith ident (getIdentTy! p) cs) = (Except.ok r) := by
  intros H
  simp [runCallElimWith, StateT.run, getIdentTy!]
  have Hsome := @getOldExprIdentTy_some p ident
  simp [H] at Hsome
  simp [Option.isSome] at Hsome
  split at Hsome <;> simp_all
  next x val heq =>
  simp [pure, ExceptT.pure, ExceptT.mk, StateT.pure]

theorem getIdentTys!_no_throw :
  ∀ {p : Program}
    {idents : List Expression.Ident}
    {cs : BoogieGenState},
  (∀ ident ∈ idents, (p.find? .var ident).isSome = true) →
  ∃ r, (runCallElimWith idents (getIdentTys! p) cs) = (Except.ok r) := by
  intros p idents cs Hglob
  induction idents generalizing cs
  case nil =>
    simp [getIdentTys!,
          pure, ExceptT.pure, ExceptT.mk,
          StateT.run, StateT.pure]
  case cons h t ih =>
    simp [getIdentTys!, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.run,
      StateT.bind] at *
    have Hsome : (p.find? DeclKind.var h).isSome = true := by simp_all
    have Hhead := @getIdentTy!_no_throw _ _ cs Hsome
    cases Hhead with
    | intro T' Hok' =>
    simp [runCallElimWith, StateT.run] at Hok'
    split <;> simp_all
    next err cs' Hres =>
    specialize @ih cs'
    cases ih with
    | intro T Hok =>
    simp [bind, StateT.bind, pure, ExceptT.pure, ExceptT.mk, ExceptT.bindCont]
    split <;> simp_all
    simp [pure, StateT.pure]

-- Step 1. A theorem stating that given a well-formed program, call-elim will return no exception
theorem callElimStmtsNoExcept :
  ∀ (st : Boogie.Statement)
    (p : Boogie.Program),
    WF.WFStatementsProp p [st] →
  ∃ sts, Except.ok sts = ((CallElim.runCallElim [st] (CallElim.callElimStmts · p)))
  -- NOTE: the generated variables will not be local, but temp. So it will not be well-formed
  -- ∧ WF.WFStatementsProp p sts
  := by
  intros st p wf
  simp [CallElim.callElimStmts, CallElim.callElimStmt]
  cases st with
  | block l b md => exists [.block l b md]
  | ite cd tb eb md => exists [.ite cd tb eb md]
  | goto l b => exists [.goto l b]
  | loop g m i b md => exists [.loop g m i b md]
  | cmd c =>
    cases c with
    | cmd c' => exists [Imperative.Stmt.cmd (CmdExt.cmd c')]
    | call lhs procName args md =>
    split
    . -- call case
      next heq =>
      cases heq
      next st =>
      split <;>
        simp only [StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind, genArgExprIdentsTrip, ne_eq, liftM,
              monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, List.unzip_snd, ite_not, ExceptT.bindCont, ExceptT.map,
              genOldExprIdentsTrip]
      . split
        next res a s heq1 =>
        split
        . -- succeeded, prove it is well-formed
          simp [StateT.bind, pure, Functor.map, ExceptT.mk, genOutExprIdentsTrip, liftM, monadLift,
            MonadLift.monadLift, ExceptT.lift, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind]
          split at heq1 <;> try cases heq1
          . next res' a' s' heq2 =>
            split
            split <;> simp only [bind, StateT.bind, StateT.pure]
            . split
              split <;> simp [pure, StateT.pure, Except.ok.injEq]
              -- old expression returns error, contradiction by well-formedness
              next ss _ _ _ _ s x e heq1 =>
              split at heq1 <;> simp_all
              next a' s' hif heq' =>
              cases heq' <;> simp_all
              simp [bind, ExceptT.bindCont, StateT.bind] at heq1
              split at heq1 <;> simp_all
              split at heq1
              . simp [ExceptT.pure, pure, ExceptT.mk, StateT.pure] at heq1
                cases heq1
              . next s x e heq =>
                generalize Heq : (List.filter (isGlobalVar p)
                  (List.flatMap OldExpressions.extractOldExprVars
                    (OldExpressions.normalizeOldExprs
                      (List.map Procedure.Check.expr res'.spec.postconditions.values))).eraseDups)
                        = eq at *
                have Hgen := @getIdentTys!_no_throw p eq (List.mapM.loop genOldExprIdent eq [] ss).snd ?_
                simp [runCallElimWith, StateT.run] at Hgen
                . cases Hgen with
                  | intro tys Hgen =>
                  simp_all
                . simp [← Heq, isGlobalVar] at *
            . -- output length not equal, contradiction
              next x e heq1 =>
              split at heq1
              . next x e heq1' =>
                simp [StateT.bind, StateT.map, pure, ExceptT.pure, ExceptT.bindCont, ExceptT.mk] at heq1
                cases heq1
              . -- lhs length not equal to outputs length
                next Hne =>
                cases wf with
                | mk df al ol =>
                exfalso
                apply Hne
                simp [Option.isSome] at df
                split at df <;> simp_all
                apply Hne
                simp [← ol, Lambda.LMonoTySignature.toTrivialLTy]
        . -- failed to get type for arguments, contradiction
          split at heq1
          . next x e heq1' =>
            simp [StateT.bind, StateT.map, pure, ExceptT.pure, ExceptT.bindCont, ExceptT.mk] at heq1
            cases heq1
          . -- arg length not equal to inputs length
            next Hne =>
            cases wf with
            | mk df al ol =>
            exfalso
            apply Hne
            simp [Option.isSome] at df
            split at df <;> simp_all
            apply Hne
            simp [← al, Lambda.LMonoTySignature.toTrivialLTy]
      . exfalso
        next proc Hfalse =>
        simp [Program.Procedure.find?] at Hfalse
        split at Hfalse <;> simp_all
        next heq' =>
        cases wf with
        | intro wf =>
        cases wf with
        | mk wf =>
        simp [Program.Procedure.find?] at wf
        split at wf <;> simp_all
    . -- other case
      exfalso
      next st Hfalse =>
      specialize Hfalse lhs procName args md
      simp_all

theorem postconditions_subst_unwrap :
  substPost ∈
  OldExpressions.substsOldExprs (createOldVarsSubst oldTrips)
    (OldExpressions.normalizeOldExprs ps) →
  ∃ post, post ∈ ps ∧ substPost = (OldExpressions.substsOldExpr (createOldVarsSubst oldTrips)
    (OldExpressions.normalizeOldExpr post)) := by
  intros H
  induction ps
  case nil =>
    simp [OldExpressions.normalizeOldExprs, OldExpressions.substsOldExprs] at H
  case cons h t ih =>
    simp [OldExpressions.normalizeOldExprs, OldExpressions.substsOldExprs] at H
    cases H with
    | inl Hin =>
      simp_all
    | inr Hin =>
      simp
      cases Hin with
      | intro x Hin =>
      right
      refine ⟨x, Hin.1, ?_⟩
      symm
      exact Hin.2

theorem prepostconditions_unwrap {ps : List (BoogieLabel × Procedure.Check)} :
post ∈ List.map Procedure.Check.expr (ListMap.values ps) →
∃ label attr, (label, { expr := post, attr : Procedure.Check }) ∈ ps := by
  intros H
  induction ps
  case nil =>
    cases H
  case cons h t ih =>
    simp at H
    cases H with
    | intro c Hc
    simp [ListMap.values] at Hc
    cases Hc.1 with
    | inl Hin =>
      simp_all
      refine ⟨h.1, c.attr, ?_⟩
      left
      simp [← Hc, Hin]
    | inr Hin =>
      simp
      specialize ih ?_
      . simp [← Hc.2]
        refine ⟨c, ⟨Hin, rfl⟩⟩
      . cases ih with
        | intro label ih => cases ih with
        | intro attr ih =>
          refine ⟨label, attr, Or.inr ih⟩

theorem updatedStateIsDefinedMono :
  (σ k').isSome = true →
  (updatedState σ k v k').isSome = true := by
  intros Hsome
  simp [updatedState]
  by_cases Heq : (k' = k) <;> simp [Heq]
  case neg => assumption

theorem EvalExpressionUpdatedState {δ : BoogieEval}:
Imperative.WellFormedSemanticEvalVar δ →
Boogie.WellFormedBoogieEvalCong δ →
Imperative.WellFormedSemanticEvalVal δ →
¬ k ∈ (Imperative.HasVarsPure.getVars e) →
δ σ₀ σ e = some v' →
δ σ₀ (updatedState σ k v) e = some v' := by
  intros Hwfv Hwfc Hwfvl Hnin Hsome
  simp [Imperative.WellFormedSemanticEvalVar, Imperative.HasFvar.getFvar] at Hwfv
  simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
  simp [Imperative.WellFormedSemanticEvalVal] at Hwfvl
  have Hval := Hwfvl.2
  simp [← Hsome] at *
  induction e <;> simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
  case const c t | op o ty | bvar b =>
    rw [Hval]; rw [Hval]; constructor; constructor
  case fvar n ty =>
    simp [Hwfv]
    simp [updatedState]
    intros Heq
    simp [Heq]
    simp_all
  case mdata info e ih =>
    apply ((Hwfc e e σ₀ (updatedState σ k v) σ₀ σ) ?_).2.1
    apply ih ; simp_all
  case abs ty e ih =>
    apply ((Hwfc e e σ₀ (updatedState σ k v) σ₀ σ) ?_).1
    apply ih ; simp_all
  case quant kk ty e ih =>
    apply ((Hwfc e e σ₀ (updatedState σ k v) σ₀ σ) ?_).2.2.1
    apply ih
    simp_all
  case app fn e fnih eih =>
    apply (((Hwfc fn fn σ₀ (updatedState σ k v) σ₀ σ) ?_).2.2.2 e e ?_).1
    apply fnih ; simp_all
    apply eih ; simp_all
  case ite c t e cih tih eih =>
    apply (((Hwfc t t σ₀ (updatedState σ k v) σ₀ σ) ?_).2.2.2 e e ?_).2.2 c c ?_
    apply tih ; simp_all
    apply eih ; simp_all
    apply cih ; simp_all
  case eq e1 e2 e1ih e2ih =>
    apply (((Hwfc e1 e1 σ₀ (updatedState σ k v) σ₀ σ) ?_).2.2.2 e2 e2 ?_).2.1
    apply e1ih ; simp_all
    apply e2ih ; simp_all

theorem EvalExpressionsUpdatedState {δ : BoogieEval} :
  Imperative.WellFormedSemanticEvalVar δ →
  Boogie.WellFormedBoogieEvalCong δ →
  Imperative.WellFormedSemanticEvalVal δ →
  ¬ k ∈ es.flatMap Imperative.HasVarsPure.getVars →
  EvalExpressions (P:=Boogie.Expression) δ σ₀ σ es vs →
  EvalExpressions (P:=Boogie.Expression) δ σ₀ (updatedState σ k v) es vs := by
  intros Hwfv Hwfc Hwfvl Hnin Heval
  have Hlen := EvalExpressionsLength Heval
  induction es generalizing vs σ
  case nil =>
    have Hnil := List.eq_nil_of_length_eq_zero (Eq.symm Hlen)
    simp [Hnil]
    constructor
  case cons h t ih =>
    cases vs
    . cases Heval
    . case cons h' t' =>
      rcases Heval
      case eval_some Hdef Heval Hevals =>
      constructor
      . exact updatedStateDefMonotone Hdef
      . apply EvalExpressionUpdatedState <;> simp_all
      . apply ih <;> simp_all

theorem EvalExpressionUpdatedStates {δ : BoogieEval} :
  Imperative.WellFormedSemanticEvalVar δ →
  Boogie.WellFormedBoogieEvalCong δ →
  Imperative.WellFormedSemanticEvalVal δ →
  ks'.length = vs'.length →
  ks'.Nodup →
  ks'.Disjoint (Imperative.HasVarsPure.getVars e) →
  δ σ₀ σ e = some v →
  δ σ₀ (updatedStates σ ks' vs') e = some v := by
  intros Hwfv Hwfc Hwfvl Hlen Hnd Hnin Heval
  induction ks' generalizing vs' σ
  case nil =>
    have Hnil := List.eq_nil_of_length_eq_zero (Eq.symm Hlen)
    simp [Hnil]
    simp [updatedStates, updatedStates']
    assumption
  case cons h t ih =>
    cases vs'
    . simp_all
    . case cons h' t' =>
      simp [updatedStates, updatedStates']
      rw [← updatedStateComm']
      apply EvalExpressionUpdatedState <;> try assumption
      . intros Hin
        apply Hnin _ Hin
        simp_all
      . apply ih <;> simp_all
        apply List.Disjoint.mono_left _ Hnin
        simp_all
      . rw [List.unzip_zip] <;> grind

theorem EvalExpressionsUpdatedStates {δ : BoogieEval} :
  Imperative.WellFormedSemanticEvalVar δ →
  Boogie.WellFormedBoogieEvalCong δ →
  Imperative.WellFormedSemanticEvalVal δ →
  ks'.length = vs'.length →
  ks'.Nodup →
  ks'.Disjoint (es.flatMap Imperative.HasVarsPure.getVars) →
  EvalExpressions (P:=Boogie.Expression) δ σ₀ σ es vs →
  EvalExpressions (P:=Boogie.Expression) δ σ₀ (updatedStates σ ks' vs') es vs := by
  intros Hwfv Hwfc Hwfvl Hlen Hnd Hnin Heval
  have Hlen := EvalExpressionsLength Heval
  induction ks' generalizing vs' σ
  case nil =>
    have Hnil := List.eq_nil_of_length_eq_zero (Eq.symm Hlen)
    simp [Hnil]
    simp [updatedStates, updatedStates']
    assumption
  case cons h t ih =>
    cases vs'
    . simp_all
    . case cons h' t' =>
      simp [updatedStates, updatedStates']
      rw [← updatedStateComm']
      apply EvalExpressionsUpdatedState <;> try assumption
      . intros Hin
        apply Hnin _ Hin
        simp_all
      . apply ih <;> simp_all
        apply List.Disjoint.mono_left _ Hnin
        simp_all
      . rw [List.unzip_zip] <;> grind

theorem ReadValueUpdatedState :
  x ≠ k →
  σ x = some v' →
  updatedState σ k v x = some v' := by
  intros Hne Hsome
  simp [updatedState, Hne] <;> simp_all

theorem ReadValueUpdatedStates :
  ¬ x ∈ ks →
  σ x = some v' →
  ks.length = vs.length →
  updatedStates σ ks vs x = some v' := by
  intros Hne Hsome Hlen
  induction ks generalizing σ vs
  case nil =>
    cases vs <;> simp_all
    simp [updatedStates, updatedStates']
    assumption
  case cons h t ih =>
    cases vs
    case nil => simp_all
    case cons h' t' =>
    simp [updatedStates, updatedStates']
    apply ih <;> simp_all
    simp [updatedState]
    simp_all

theorem ReadValuesUpdatedState :
  ¬ k ∈ ks →
  ReadValues σ ks vs →
  ReadValues (updatedState σ k v) ks vs := by
  intros Hin Hrd
  induction Hrd
  case read_none =>
    apply ReadValues.read_none
  case read_some xs' vs' x v' Hsome Hrd Hrd2 =>
    constructor <;> try assumption
    apply ReadValueUpdatedState <;> simp_all
    apply Ne.symm Hin.1
    apply Hrd2 <;> simp_all

theorem ReadValuesUpdatedStates :
  ks'.length = vs'.length →
  ks'.Disjoint ks →
  ReadValues σ ks vs →
  ReadValues (updatedStates σ ks' vs') ks vs := by
  intros Hlen Hin Hrd
  induction ks generalizing vs
  case nil =>
    cases Hrd
    constructor
  case cons h t ih =>
    cases vs with
    | nil =>
      cases Hrd
    | cons h t =>
      cases Hrd with
      | read_some Hh Ht =>
      constructor
      . refine ReadValueUpdatedStates ?_ Hh Hlen
        . intros Hin'
          exact Hin Hin' List.mem_cons_self
      . apply ih ?_ Ht
        apply List.Disjoint.mono_right _ Hin
        simp_all

theorem ReadValueUpdatedState' :
  x ≠ k →
  updatedState σ k v x = some v' →
  σ x = some v' := by
  intros Hne Hsome
  simp [updatedState, Hne] at Hsome <;> simp_all

theorem ReadValueUpdatedStates' :
  ¬ x ∈ ks →
  updatedStates σ ks vs x = some v' →
  ks.length = vs.length →
  σ x = some v' := by
  intros Hne Hsome Hlen
  induction ks generalizing σ vs
  case nil =>
    cases vs <;> simp_all
    simp [updatedStates, updatedStates'] at Hsome
    assumption
  case cons h t ih =>
    cases vs
    case nil => simp_all
    case cons h' t' =>
    simp [updatedStates, updatedStates'] at *
    specialize ih Hne.2 Hsome Hlen
    exact ReadValueUpdatedState' Hne.1 ih

theorem ReadValuesUpdatedState' :
  ¬ k ∈ ks →
  ReadValues (updatedState σ k v) ks vs →
  ReadValues σ ks vs := by
  intros Hin Hrd
  induction Hrd
  case read_none =>
    apply ReadValues.read_none
  case read_some xs' vs' x v' Hsome Hrd Hrd2 =>
    constructor <;> try assumption
    apply ReadValueUpdatedState' (k:=k) (v:=v) _ Hsome
    . exact Ne.symm (List.ne_of_not_mem_cons Hin)
    . apply Hrd2
      exact List.not_mem_of_not_mem_cons Hin

theorem ReadValuesUpdatedStates' :
  ks'.length = vs'.length →
  ks'.Disjoint ks →
  ReadValues (updatedStates σ ks' vs') ks vs →
  ReadValues σ ks vs := by
  intros Hlen Hin Hrd
  induction ks generalizing vs
  case nil =>
    cases Hrd
    constructor
  case cons h t ih =>
    cases vs with
    | nil =>
      cases Hrd
    | cons h t =>
      cases Hrd with
      | read_some Hh Ht =>
      constructor
      . refine ReadValueUpdatedStates' ?_ Hh Hlen
        . intros Hin'
          exact Hin Hin' List.mem_cons_self
      . apply ih ?_ Ht
        apply List.Disjoint.mono_right _ Hin
        simp_all

theorem ReadValuesUpdatedStatesSame :
  ks.length = vs.length →
  ks.Nodup →
  ReadValues (updatedStates σ ks vs) ks vs := by
  intros Hlen Hnd
  induction ks generalizing σ vs
  case nil =>
    cases vs <;> simp_all
    constructor
  case cons h t ih =>
    cases vs
    . simp_all
    . simp [updatedStates, updatedStates']
      rw [← updatedStateComm']
      constructor <;> simp_all
      simp [updatedState]
      rw [updatedStateComm']
      apply ih <;> simp_all
      rw [List.unzip_zip] <;> simp_all
      rw [List.unzip_zip] <;> simp_all

theorem EvalStatementContractInitVar :
  Imperative.WellFormedSemanticEvalVar δ →
  σ v = some vv →
  σ v' = none →
  EvalStatementContract π δ δP σ₀ σ
    (createInitVar ((v', ty), v))
    (updatedState σ v' vv) := by
  intros Hwf Hsome Hnone
  simp [createInitVar]
  constructor
  constructor
  . apply Imperative.EvalCmd.eval_init <;> try assumption
    have Hwfv := Hwf (Lambda.LExpr.fvar v none) v σ₀ σ
    rw [Hwfv]; assumption
    simp [Imperative.HasFvar.getFvar]
    apply Imperative.InitState.init Hnone
    simp [updatedState]
    intros y Hne
    simp [updatedState]
    intros Heq
    simp_all
  . simp [Imperative.isDefinedOver,
          Imperative.isDefined,
          Imperative.HasVarsImp.modifiedVars,
          Command.modifiedVars,
          Imperative.Cmd.modifiedVars]

theorem EvalStatementsContractInitVars :
  Imperative.WellFormedSemanticEvalVar δ →
  -- the generated old variable names shouldn't overlap with original variables
  List.Nodup ((trips.unzip.fst.unzip.fst) ++ (trips.unzip.snd)) →
  ReadValues σ (trips.unzip.snd) vvs →
  Imperative.isNotDefined σ (trips.unzip.fst.unzip.fst) →
  EvalStatementsContract π δ δP σ₀ σ
    (createInitVars trips)
    (updatedStates σ
      (trips.unzip.fst.unzip.fst) vvs) := by
  intros Hwf Hndup Hdef Hndef
  induction trips generalizing σ vvs with
  | nil =>
    simp [createInitVars, updatedStates]
    constructor
  | cons h t ih =>
    cases Hdef
    next vs vv Hsome Hrest =>
    cases h with
    | mk pair v =>
    cases pair with
    | mk v' ty =>
    apply Imperative.EvalStmts.stmts_some_sem
    apply EvalStatementContractInitVar <;> try assumption
    apply Hndef <;> simp_all
    unfold updatedStates
    apply ih
    . simp_all
      have HH := Hndup.2
      apply List.Sublist.nodup (by simp) HH
    . refine ReadValuesUpdatedState ?_ Hrest
      simp [List.Nodup] at Hndup
      have Hin := Hndup.1
      apply List.forall_mem_ne.mp
      intros x' ty'
      simp_all
    . simp [Imperative.isNotDefined] at Hndef ⊢
      intros v x x1 Hin
      simp [updatedState]
      split <;> simp_all
      apply Hndef.2
      apply Hin

theorem EvalStatementContractInit :
  Imperative.WellFormedSemanticEvalVar δ →
  δ σ₀ σ e = some vv →
  σ v' = none →
  EvalStatementContract π δ δP σ₀ σ
    (createInit ((v', ty), e))
    (updatedState σ v' vv) := by
  intros Hwf Hsome Hnone
  simp [createInit]
  constructor
  constructor
  . apply Imperative.EvalCmd.eval_init <;> try assumption
    apply Imperative.InitState.init Hnone
    simp [updatedState]
    intros y Hne
    simp [updatedState]
    intros Heq
    simp_all
  . simp [Imperative.isDefinedOver,
          Imperative.isDefined,
          Command.modifiedVars,
          Imperative.Cmd.modifiedVars,
          Imperative.HasVarsImp.modifiedVars]

theorem EvalStatementsContractInits :
  Imperative.WellFormedSemanticEvalVar δ →
  Imperative.WellFormedSemanticEvalVal δ →
  WellFormedBoogieEvalCong δ →
  -- the generated old variable names shouldn't overlap with original variables
  trips.unzip.1.unzip.1.Disjoint (List.flatMap (Imperative.HasVarsPure.getVars (P:=Expression)) trips.unzip.2) →
  List.Nodup (trips.unzip.1.unzip.1) →
  EvalExpressions (P:=Boogie.Expression) δ σ₀ σ (trips.unzip.2) vvs →
  -- ReadValues σ (trips.unzip.2) vvs →
  Imperative.isNotDefined σ (trips.unzip.1.unzip.1) →
  EvalStatementsContract π δ δP σ₀ σ
    (createInits trips)
    (updatedStates σ
      (trips.unzip.1.unzip.1) vvs) := by
  intros Hwfvr Hwfvl Hwfc Hdisj Hndup Hdef Hndef
  induction trips generalizing σ vvs with
  | nil =>
    simp [createInits, updatedStates]
    constructor
  | cons h t ih =>
    cases Hdef
    next vs vv Hsome Hrest =>
    cases h with
    | mk pair v =>
    cases pair with
    | mk v' ty =>
    apply Imperative.EvalStmts.stmts_some_sem
    apply EvalStatementContractInit <;> try assumption
    apply Hndef <;> simp_all
    unfold updatedStates
    apply ih
    . apply List.Disjoint.mono ?_ ?_ Hdisj <;> simp_all
    . simp_all
    . refine EvalExpressionsUpdatedState Hwfvr Hwfc Hwfvl ?_ Hrest
      simp at Hdisj
      have Hdisj' :
        [v'].Disjoint (List.flatMap Imperative.HasVarsPure.getVars t.unzip.snd) := by
        apply List.Disjoint.mono ?_ ?_ Hdisj <;> simp_all
      intros Hin
      exact Hdisj' (List.mem_singleton.mpr rfl) Hin
    . simp [Imperative.isNotDefined] at Hndef ⊢
      intros v x x1 Hin
      simp [updatedState]
      split <;> simp_all
      apply Hndef.2
      apply Hin

theorem EvalStatementContractHavocUpdated :
  ∀ vv,
  Imperative.WellFormedSemanticEvalVar δ →
  σ v = some vv' →
  EvalStatementContract π δ δP σ₀ σ
    (createHavoc v)
    (updatedState σ v vv) := by
  intros vv Hwf Hsome
  simp [createHavoc]
  constructor
  constructor
  . constructor
    . exact updatedStateUpdate Hsome
    . assumption
  . simp [Imperative.isDefinedOver, Imperative.isDefined,
          Imperative.HasVarsImp.modifiedVars,
          Command.modifiedVars,
          Imperative.Cmd.modifiedVars, Option.isSome]
    split <;> simp_all

theorem ReadValuesSome :
  Imperative.isDefined σ ks →
  ∃ vs, ReadValues σ ks vs := by
  intros H
  induction ks
  case nil =>
    exists []
    constructor
  case cons h t ih =>
    have Hh := H h
    have Ht := ih ?_
    . cases Ht with
      | intro t' Hrd =>
      simp [Option.isSome] at Hh
      split at Hh <;> simp_all
      next x val heq =>
      exists val :: t'
      constructor <;> simp_all
    . simp [Imperative.isDefined] at *
      intros v a
      simp_all

theorem idents2havocsApp :
createHavocs (vs₁ ++ vs₂) =
createHavocs vs₁ ++ createHavocs vs₂ := by
cases vs₁ <;> simp [createHavocs]

theorem createFvarsSubstStores :
  ks1.length = ks2.length →
  Imperative.WellFormedSemanticEvalVar δ →
  Imperative.substDefined σ σA (ks1.zip ks2) →
  Imperative.substStores σ σA (ks1.zip ks2) →
  ReadValues σA ks2 argVals →
  EvalExpressions (P:=Boogie.Expression) δ σ₀ σ (createFvars ks1) argVals := by
    intros Hlen Hwfv Hdef Hsubst Hrd
    simp [createFvars]
    have Hlen2 := ReadValuesLength Hrd
    induction Hrd generalizing ks1
    case read_none => simp_all; constructor
    case read_some xs vs x v Hsome Hrds ih' =>
      induction ks1 generalizing ks2 vs v with
      | nil =>
        simp_all
      | cons h t ih =>
        simp
        constructor
        . simp [createFvar,
                Imperative.HasVarsPure.getVars,
                Lambda.LExpr.LExpr.getVars]
          simp [Imperative.substDefined] at Hdef
          intros hh Hin
          apply (Hdef hh x ?_).1
          left
          simp_all
        . simp [createFvar]
          simp [Imperative.WellFormedSemanticEvalVar] at Hwfv
          simp [Imperative.HasFvar.getFvar] at Hwfv
          simp [Hwfv]
          rw [Hsubst]
          exact Hsome
          simp_all
        . apply ih' <;> simp_all
          . intros k1 k2 Hin
            apply Hdef <;> simp_all
          . simp [Imperative.substStores] at *
            intros
            apply Hsubst <;> simp_all

theorem EvalStatementsContractHavocVars :
  Imperative.WellFormedSemanticEvalVar δ →
  Imperative.isDefined σ vs →
  HavocVars σ vs σ' →
  EvalStatementsContract π δ δP σ₀ σ
    (createHavocs vs) σ' := by
  intros Hwfv Hdef Hhav
  simp [createHavocs]
  induction vs generalizing σ
  case nil =>
    have Heq := HavocVarsEmpty Hhav
    simp_all
    exact Imperative.EvalStmts.stmts_none_sem
  case cons h t ih =>
    simp [createHavoc]
    cases Hhav with
    | update_some Hup Hhav =>
    apply Imperative.EvalStmts.stmts_some_sem
    apply EvalStmtRefinesContract
    apply Imperative.EvalStmt.cmd_sem
    apply EvalCommand.cmd_sem
    apply Imperative.EvalCmd.eval_havoc <;> try assumption
    . simp [Imperative.isDefinedOver, Command.modifiedVars,Imperative.Cmd.modifiedVars,
            Imperative.HasVarsImp.modifiedVars]
      simp [Imperative.isDefined] at Hdef ⊢
      apply Hdef.1
    . apply ih <;> try assumption
      . apply UpdateStateDefMonotone (σ:=σ) (vs:=t) <;> try assumption
        simp [Imperative.isDefined] at * <;> simp_all

theorem updatedStateInv :
¬k = h →
updatedState σ h h' k = σ k := by
intros Hne
unfold updatedState
simp [Hne] <;> simp_all

theorem updatedStatesInv :
¬k ∈ ks' →
updatedStates σ ks' vs' k = σ k := by
intros Hin
induction ks' generalizing vs' σ <;> simp_all
case nil =>
  simp [updatedStates, updatedStates']
case cons h t ih =>
  cases vs'
  case nil =>
    simp [updatedStates, updatedStates']
  case cons h' t' =>
    unfold updatedStates
    have Hsome' : (updatedState σ h h') k = σ k := by
      apply updatedStateInv <;> simp_all
    simp [← Hsome']
    exact ih

theorem UpdateStateUpdatedDists
{P : Imperative.PureExpr}
{σ σ' : Imperative.SemanticStore P}
{h : P.Ident} {v : P.Expr} {ks : List P.Ident} {vs : List P.Expr} :
¬ h ∈ ks →
Imperative.UpdateState P σ h v σ' →
Imperative.UpdateState P (updatedStates σ ks vs) h v (updatedStates σ' ks vs) := by
intros Hnin Hup
cases Hup with
| update Hsome HH =>
simp [updatedStates]
generalize Hls : ks.zip vs = ls
induction ls generalizing ks vs σ σ'
case nil =>
  simp [updatedStates']
  simp_all
  constructor <;> try simp_all
  rfl
case cons h t ih H' =>
  simp [updatedStates']
  have Hzip := List.zip_eq_cons_iff.mp Hls
  cases Hzip with | intro l1 Hzip => cases Hzip with | intro l2 Hzip =>
  apply ih ?_ (ks:=l1) (vs:=l2) <;> simp_all
  . simp [updatedState]
    split <;> simp_all
  . intros y Hne
    simp [updatedState]
    split <;> simp_all
  . cases h with
    | mk l r =>
    simp [updatedState] at *
    split <;> simp_all

theorem InitStateUpdatedDists
{P : Imperative.PureExpr}
{σ σ' : Imperative.SemanticStore P}
{h : P.Ident} {v : P.Expr} {ks : List P.Ident} {vs : List P.Expr} :
¬ h ∈ ks →
Imperative.InitState P σ h v σ' →
Imperative.InitState P (updatedStates σ ks vs) h v (updatedStates σ' ks vs) := by
intros Hnin Hup
cases Hup with
| init Hsome HH =>
simp [updatedStates]
generalize Hls : ks.zip vs = ls
induction ls generalizing ks vs σ σ'
case nil =>
  simp [updatedStates']
  simp_all
  constructor <;> try simp_all
case cons h t ih H' =>
  simp [updatedStates']
  have Hzip := List.zip_eq_cons_iff.mp Hls
  cases Hzip with | intro l1 Hzip => cases Hzip with | intro l2 Hzip =>
  apply ih ?_ (ks:=l1) (vs:=l2) <;> simp_all
  . simp [updatedState]
    split <;> simp_all
  . intros y Hne
    simp [updatedState]
    split <;> simp_all
  . cases h with
    | mk l r =>
    simp [updatedState] at *
    split <;> simp_all

theorem UpdateStatesUpdatedDists
{P : Imperative.PureExpr}
{σ σ' : Imperative.SemanticStore P}
{ks ks': List P.Ident} {vs vs' : List P.Expr} :
  ks.Disjoint ks' →
  UpdateStates σ ks vs σ' →
  UpdateStates (updatedStates σ ks' vs') ks vs (updatedStates σ' ks' vs') := by
intros Hnd Hup
induction Hup
case update_none =>
  exact UpdateStates.update_none
case update_some Hup Hups ih =>
  apply UpdateStates.update_some
  . apply UpdateStateUpdatedDists <;> try assumption
    simp [List.Disjoint] at Hnd
    simp_all
  . apply ih
    simp [List.Disjoint] at *
    simp_all

theorem InitStatesUpdatedDists
{P : Imperative.PureExpr}
{σ σ' : Imperative.SemanticStore P}
{ks ks': List P.Ident} {vs vs' : List P.Expr} :
  ks.Disjoint ks' →
  InitStates σ ks vs σ' →
  InitStates (updatedStates σ ks' vs') ks vs (updatedStates σ' ks' vs') := by
intros Hnd Hup
induction Hup
case init_none =>
  exact InitStates.init_none
case init_some Hup Hups ih =>
  apply InitStates.init_some
  . apply InitStateUpdatedDists <;> try assumption
    simp [List.Disjoint] at Hnd
    simp_all
  . apply ih
    simp [List.Disjoint] at *
    simp_all

theorem UpdateStatesUpdatedDist
{P : Imperative.PureExpr}
{σ σ' : Imperative.SemanticStore P}
{ks : List P.Ident} {vs : List P.Expr}
{k : P.Ident} {v : P.Expr} :
  ¬ k ∈ ks →
  UpdateStates σ ks vs σ' →
  UpdateStates (updatedState σ k v) ks vs (updatedState σ' k v) := by
intros Hnd Hup
have Hnd : ks.Disjoint [k] := by
  intros a Hin1 Hin2
  apply Hnd
  simp_all
have HH := UpdateStatesUpdatedDists (vs':=[v]) Hnd Hup
simp [updatedStates, updatedStates'] at HH
assumption

theorem HavocVarsUpdatedDists :
ks.Disjoint ks' →
HavocVars σ ks σ' →
HavocVars (updatedStates σ ks' vs') ks
          (updatedStates σ' ks' vs') := by
intros Hnd Hhav
induction ks generalizing σ
case nil =>
  have Heq := HavocVarsEmpty Hhav
  simp_all
  exact HavocVars.update_none
case cons h t ih =>
  cases Hhav
  next v σ'' Hup Hhav2 =>
  apply HavocVars.update_some (v:=v) (σ':=(updatedStates σ'' ks' vs'))
  . simp [List.Disjoint] at Hnd
    apply UpdateStateUpdatedDists Hnd.1 Hup
  . apply ih ?_ Hhav2
    apply List.Disjoint.mono_left ?_ Hnd
    simp_all

theorem InitVarsUpdatedDists :
ks.Disjoint ks' →
InitVars σ ks σ' →
InitVars (updatedStates σ ks' vs') ks
          (updatedStates σ' ks' vs') := by
intros Hnd Hhav
induction ks generalizing σ
case nil =>
  have Heq := InitVarsEmpty Hhav
  simp_all
  exact InitVars.init_none
case cons h t ih =>
  cases Hhav
  next v σ'' Hup Hhav2 =>
  apply InitVars.init_some (v:=v) (σ':=(updatedStates σ'' ks' vs'))
  . simp [List.Disjoint] at Hnd
    apply InitStateUpdatedDists Hnd.1 Hup
  . apply ih ?_ Hhav2
    apply List.Disjoint.mono_left ?_ Hnd
    simp_all

theorem HavocVarsUpdatedDist :
¬ k ∈ ks →
HavocVars σ ks σ' →
HavocVars (updatedState σ k v) ks
          (updatedState σ' k v) := by
intros Hnd Hhav
have Hnd : ks.Disjoint [k] := by
  intros a Hin1 Hin2
  apply Hnd
  simp_all
have HH := HavocVarsUpdatedDists (vs':=[v]) Hnd Hhav
simp [updatedStates, updatedStates'] at HH
assumption

theorem InitVarsUpdatedDist :
¬ k ∈ ks →
InitVars σ ks σ' →
InitVars (updatedState σ k v) ks
          (updatedState σ' k v) := by
intros Hnd Hhav
have Hnd : ks.Disjoint [k] := by
  intros a Hin1 Hin2
  apply Hnd
  simp_all
have HH := InitVarsUpdatedDists (vs':=[v]) Hnd Hhav
simp [updatedStates, updatedStates'] at HH
assumption

theorem UpdatedStatesDisjNotDefMonotone :
  ks.Disjoint ks' →
  ks.length = vs.length →
  Imperative.isNotDefined σ ks' →
  Imperative.isNotDefined (updatedStates σ ks vs) ks' := by
intros Hdis Hlen Hndef
simp [Imperative.isNotDefined, updatedStates] at *
intros v Hin
induction ks generalizing vs σ <;> simp_all
case nil =>
  simp [updatedStates']
  exact Hndef v Hin
case cons h t ih =>
  induction vs generalizing h t σ <;> simp_all
  case cons h' t' ih' =>
    simp [updatedStates']
    rw [ih] <;> try simp_all
    . apply List.Disjoint.mono_left _ Hdis
      simp_all
    . intros v Hin
      simp [updatedState]
      split <;> simp_all
      apply Hdis _ Hin
      simp_all

/-- We can't use arbitrary expressions for substitution,
    because then we can't say anything about the stores
    due to not knowing the exact form of the expressions -/
theorem Lambda.LExpr.substFvarCorrect :
  Boogie.WellFormedBoogieEvalCong δ →
  Imperative.WellFormedSemanticEvalVar (P:=Expression) δ →
  Imperative.WellFormedSemanticEvalVal (P:=Expression) δ →
  Imperative.substStores σ σ' [(fro, to)] →
  -- NOTE: `to` shouldn't be referred to in the original expression as well, but it is not needed in this lemma.
  Imperative.invStores σ σ'
    ((@Imperative.HasVarsPure.getVars Expression _ _ e).removeAll [fro]) →
  -- NOTE: the old store is irrelevant because we assume congruence on old expressions as well,
  -- More relation between the old store would be needed if we remove old expression congruence from WellFormedSemanticEvalVal
  δ σ₀ σ e = δ σ₀' σ' (e.substFvar fro (createFvar to)) := by
  intros Hwfc Hwfvr Hwfvl Hsubst2 Hinv
  induction e <;> simp [Lambda.LExpr.substFvar, createFvar] at *
  case const c ty | op o ty | bvar x =>
    rw [Hwfvl.2]
    rw [Hwfvl.2]
    constructor
    constructor
  case fvar name ty =>
    simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
    split <;> try simp_all
    . simp [Imperative.substStores] at Hsubst2
      rw [Hwfvr]
      rw [Hwfvr]
      exact Hsubst2
      simp [Imperative.HasFvar.getFvar]
      simp [Imperative.HasFvar.getFvar]
    . next Hne =>
      simp [Imperative.invStores, Imperative.substStores,
            Imperative.HasVarsPure.getVars,
            Lambda.LExpr.LExpr.getVars, List.removeAll, Hne] at Hinv
      rw [Hwfvr]
      rw [Hwfvr]
      exact Hinv
      simp [Imperative.HasFvar.getFvar]
      simp [Imperative.HasFvar.getFvar]
  case mdata info e ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    specialize ih Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    have Hinfo := Hwfc.2.1
    specialize Hinfo info
    simp [Hinfo]
  case abs ty e ih  =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    specialize ih Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    apply Hwfc.1
  case quant k ty e ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    specialize ih Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    have Hquant := Hwfc.2.2.1
    exact Hquant k ty
  case app c fn fih eih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.app_removeAll, List.zip_append] at *
    specialize fih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    specialize Hwfc _ _ _ _ _ _ fih
    have Hfun := Hwfc.2.2.2
    specialize Hfun _ _ eih
    have Hfun := Hfun.1
    exact Hfun
  case ite c t e cih tih eih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.app_removeAll, List.zip_append] at *
    specialize cih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize tih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; right; assumption
    specialize Hwfc _ _ _ _ _ _ tih
    have Hfun := Hwfc.2.2.2
    specialize Hfun _ _ eih
    have Hfun := Hfun.2.2
    specialize Hfun _ _ cih
    exact Hfun
  case eq e1 e2 e1ih e2ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.app_removeAll, List.zip_append] at *
    specialize e1ih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize e2ih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    specialize Hwfc _ _ _ _ _ _ e1ih
    have Hfun := Hwfc.2.2.2
    specialize Hfun _ _ e2ih
    have Hfun := Hfun.2.1
    exact Hfun

theorem Lambda.LExpr.substFvarsCorrectZero :
  Boogie.WellFormedBoogieEvalCong δ →
  Imperative.WellFormedSemanticEvalVar δ →
  Imperative.WellFormedSemanticEvalVal δ →
  Imperative.invStores σ σ' (Imperative.HasVarsPure.getVars e) →
  δ σ₀ σ e = δ σ₀' σ' e := by
  intros Hwfc Hwfvr Hwfvl Hinv
  induction e <;> simp at *
  case const c ty | op o ty | bvar x =>
    rw [Hwfvl.2]
    rw [Hwfvl.2]
    constructor
    constructor
  case fvar name ty =>
    simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
    specialize Hwfvr (Lambda.LExpr.fvar name ty) name
    rw [Hwfvr]
    rw [Hwfvr]
    rw [Hinv]
    simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars]
    simp [Imperative.HasFvar.getFvar]
    simp [Imperative.HasFvar.getFvar]
  case mdata info e ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    specialize ih Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    have Hinfo := Hwfc.2.1
    specialize Hinfo info
    simp [Hinfo]
  case abs ty e ih  =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    specialize ih Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    apply Hwfc.1
  case quant k ty e ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    specialize ih Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    have Hquant := Hwfc.2.2.1
    exact Hquant k ty
  case app c fn fih eih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.zip_append] at *
    specialize fih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    specialize Hwfc _ _ _ _ _ _ fih
    have Hfun := Hwfc.2.2.2
    specialize Hfun _ _ eih
    have Hfun := Hfun.1
    exact Hfun
  case ite c t e cih tih eih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.zip_append] at *
    specialize cih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize tih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; left; assumption
    specialize eih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; right; assumption
    specialize Hwfc _ _ _ _ _ _ tih
    have Hfun := Hwfc.2.2.2
    specialize Hfun _ _ eih
    have Hfun := Hfun.2.2
    specialize Hfun _ _ cih
    exact Hfun
  case eq e1 e2 e1ih e2ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    simp [Imperative.invStores, Imperative.substStores,
          Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    simp [List.zip_append] at *
    specialize e1ih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      left; assumption
    specialize e2ih ?_
    . intros k1 k2 Hin
      rw [Hinv]
      right; assumption
    specialize Hwfc _ _ _ _ _ _ e1ih
    have Hfun := Hwfc.2.2.2
    specialize Hfun _ _ e2ih
    have Hfun := Hfun.2.1
    exact Hfun

theorem updatedStoresInvStores :
  ¬ k ∈ ks →
  Imperative.invStores σ (updatedState σ k v) ks := by
  intros Hnin k1 k2 Hin
  have Heq : k1 = k2 := zip_self_eq Hin
  simp_all
  have Hin := (List.of_mem_zip Hin).1
  have Hne : k2 ≠ k := by
    exact ne_of_mem_of_not_mem Hin Hnin
  simp [updatedState]
  simp_all

theorem invStoresSubstHead :
  Imperative.substStores (P := Expression) σ (updatedState σ h' v₁) [(h, h')] →
  ¬ h' ∈ vs →
  Imperative.invStores σ (updatedState σ h' v₁) (List.removeAll vs [h]) := by
intros Hnin Hsubst k1 k2
apply updatedStoresInvStores
simp [List.removeAll]
simp_all

theorem invStoresEraseDups' :
  Imperative.invStores (P:=Expression) σ σ' vs.eraseDups →
  Imperative.invStores (P:=Expression) σ σ' vs := by
  intros Hinv k1 k2 Hin
  specialize Hinv k1 k2
  have Heq := zip_self_eq Hin
  simp_all
  apply Hinv
  apply zip_self_eq'
  refine eraseDupsBy.sound ?_
  have Hsub := eraseDupsBy.sound Hin
  have Hmem := List.of_mem_zip Hin
  exact Hmem.1

theorem invStoresSubstTail'  [BEq P.Ident] [LawfulBEq P.Ident] {σ : Imperative.SemanticStore P}:
  σ h = some v₁ →
  Imperative.invStores (P:=P) σ₀ σ (List.removeAll vs (h :: t)) →
  Imperative.invStores (updatedState σ₀ h v₁) σ (List.removeAll vs t) := by
  intros Hsome Hinv k1 k2 Hin
  have Heq := zip_self_eq Hin
  simp_all
  simp [Imperative.invStores, Imperative.substStores] at *
  simp [updatedState]
  split <;> simp_all
  . next neq =>
    apply Hinv
    apply zip_self_eq'
    have Hin := (List.of_mem_zip Hin).1
    apply removeAll_cons <;> simp_all

theorem invStoresSubstTail :
  Imperative.substStores (P := Expression) σ σ' ((h, h') :: t.zip t') →
  Imperative.substStores (P := Expression) (updatedState σ h' v₁) σ' (t.zip t') →
  σ h = some v₁ →
  h ≠ h' →
  Imperative.invStores σ σ' (List.removeAll vs ((h :: t) ++ (h' :: t'))) →
  Imperative.invStores (updatedState σ h' v₁) σ'
                            (List.removeAll (vs.replaceAll h h') (t ++ t')) := by
  intros Hsubst1 Hsubst2 Hsome Hne Hinv k1 k2 Hin
  have Heq := zip_self_eq Hin
  simp_all
  simp [Imperative.invStores, Imperative.substStores] at *
  simp [updatedState]
  split
  . rw [← Hsubst1 h] <;> simp_all
  . next neq =>
    apply Hinv
    apply zip_self_eq'
    have Hin := (List.of_mem_zip Hin).1
    have Hsub := removeAll_sublist (vs.replaceAll h h') (t ++ t')
    have Hin' : k2 ∈ (vs.replaceAll h h') := List.Sublist.mem Hin Hsub
    have Hor := in_replaceAll_removeAll Hin
    cases Hor <;> simp_all
    apply removeAll_cons
    . intros Heq
      simp_all
      have Hnmem : ¬ h ∈ vs.replaceAll h h' := replaceAll_not_mem Hne
      exact Hnmem Hin'
    . simp [List.removeAll] at *
      simp_all

theorem subst_create_replace :
(Imperative.HasVarsPure.getVars (Lambda.LExpr.substFvar e h (createFvar h'))) =
(Imperative.HasVarsPure.getVars e).replaceAll h h'
:= by
induction e <;> simp [
    Imperative.HasVarsPure.getVars,
    Lambda.LExpr.LExpr.getVars,
    Lambda.LExpr.substFvar,
    createFvar,
    List.replaceAll,
  ] at * <;> try assumption
case fvar name ty =>
  split <;> try simp_all
  simp [Lambda.LExpr.LExpr.getVars]
  split <;> simp_all
  simp [Lambda.LExpr.LExpr.getVars]
case app fn e fn_ih e_ih =>
  rw [fn_ih, e_ih]
  rw [List.replaceAll_app]
case ite c t e c_ih t_ih e_ih =>
  rw [c_ih, t_ih, e_ih]
  rw [List.replaceAll_app]
  rw [List.replaceAll_app]
case eq e1 e2 e1_ih e2_ih =>
  rw [e1_ih, e2_ih]
  rw [List.replaceAll_app]

theorem substDefined_tail :
Imperative.substDefined σ σ' (h :: t) →
Imperative.substDefined σ σ' t := by
intros Hsubst k1 k2 Hin
apply Hsubst
exact List.mem_cons_of_mem h Hin

theorem substDefined_updatedState :
Imperative.substDefined σ σ' ls →
Imperative.substDefined (updatedState σ k v) σ' ls := by
intros Hsubst k1 k2 Hin
apply And.intro
. apply updatedStateIsDefinedMono
  exact (Hsubst k1 k2 Hin).1
. exact (Hsubst k1 k2 Hin).2

theorem zip_notin_fst :
  t.length = t'.length →
  (∀ x, ¬(h, x) ∈ List.zip t t') →
  ¬ h ∈ t := by
intros Hlen H
induction t generalizing t' h <;> simp_all
case cons h t ih =>
induction t' <;> simp_all
case cons h' t' =>
have HH := H h'
simp_all
exact ih rfl H

theorem zip_notin_snd :
  t.length = t'.length →
  (∀ x, ¬(x, h) ∈ List.zip t t') →
  ¬ h ∈ t' := by
intros Hlen H
induction t' generalizing t h <;> simp_all
case cons h t ih =>
induction t <;> simp_all
case cons h' t' =>
have HH := H h'
simp_all
exact ih Hlen H

theorem substNodup_ht :
  t.length = t'.length →
  Imperative.substNodup ((h, h') :: List.zip t t') →
  ¬ h ∈ t ∧ ¬ h' ∈ t' := by
  intros Hlen Hsubst
  simp [Imperative.substNodup] at Hsubst
  apply And.intro
  . intros Hin
    exact zip_notin_fst Hlen Hsubst.1.1 Hin
  . have Hnd := nodup_middle Hsubst.2
    simp at Hnd
    have Hnd' := Hnd.1.2
    exact zip_notin_snd Hlen Hnd'

theorem getVarsSubstCreateFvar :
v ∈ (Imperative.HasVarsPure.getVars (P:=Expression) (Lambda.LExpr.substFvar e h (createFvar h'))) →
v ∈ (Imperative.HasVarsPure.getVars e) ∨ v = h' := by
intros Hin
induction e <;>
simp [Lambda.LExpr.substFvar,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      createFvar
      ] at * <;> try simp_all
case fvar name ty =>
  split at Hin <;> simp [Lambda.LExpr.LExpr.getVars] at * <;> simp_all
case app fn e fn_ih e_ih =>
  cases Hin <;> simp_all
  cases fn_ih <;> simp_all
  cases e_ih <;> simp_all
case ite c t e c_ih t_ih e_ih =>
  cases Hin with
  | inl Hin => cases (c_ih Hin) <;> simp_all
  | inr Hin =>
  cases Hin with
  | inl Hin => cases (t_ih Hin) <;> simp_all
  | inr Hin => cases (e_ih Hin) <;> simp_all
case eq fn e fn_ih e_ih =>
  cases Hin <;> simp_all
  cases fn_ih <;> simp_all
  cases e_ih <;> simp_all

theorem Lambda.LExpr.substFvarsCorrect :
  WellFormedBoogieEvalCong δ →
  Imperative.WellFormedSemanticEvalVar (P:=Expression) δ →
  Imperative.WellFormedSemanticEvalVal (P:=Expression) δ →
  fro.length = to.length →
  Imperative.substDefined σ σ' (fro.zip to) →
  Imperative.substNodup (fro.zip to) →
  Imperative.substStores σ σ' (fro.zip to) →
  to.Disjoint (@Imperative.HasVarsPure.getVars Expression _ _ e) →
  Imperative.invStores σ σ'
    ((@Imperative.HasVarsPure.getVars Expression _ _ e).removeAll (fro ++ to)) →
  δ σ₀ σ e = δ σ₀' σ' (e.substFvars (fro.zip $ createFvars to)) := by
  intros Hwfc Hwfvr Hwfvl Hlen Hdef Hnd Hsubst Hnin Hinv
  induction fro generalizing to σ₀ σ σ' e
  case nil =>
    simp_all
    have Hemp : to = [] := by
      apply List.eq_nil_of_length_eq_zero (Eq.symm Hlen)
    simp [Hemp] at *
    simp [Lambda.LExpr.substFvars]
    exact substFvarsCorrectZero Hwfc Hwfvr Hwfvl Hinv
  case cons h t ih =>
    cases to with
    | nil => simp_all
    | cons h' t' =>
    simp [Lambda.LExpr.substFvars] at *
    simp [createFvars] at *
    have Hsubst1 := substStoresCons' Hnd Hdef Hsubst
    cases Hsubst1 with
    | intro σ₁ Hsubst1 =>
    cases Hsubst1 with
    | intro v₁ Hsubst1 =>
    cases Hsubst1 with
    | intro Hsome Hsubst1 =>
    cases Hsubst1 with
    | intro Hstore Hsubst1 =>
    cases Hsubst1 with
    | intro Hsubst' Hsubst1 =>
    -- the old store can stay unchanged since it is irrelevant
    rw [substFvarCorrect (σ₀ := σ₀) (σ₀' := σ₀) (e := e) Hwfc Hwfvr Hwfvl Hsubst'] <;> simp_all
    rw [ih] <;> try simp_all
    . refine substDefined_updatedState ?_
      exact substDefined_tail Hdef
    . simp [Imperative.substNodup] at Hnd ⊢
      have Hnd2 := nodup_middle Hnd.2
      simp_all
    . -- Disjoint
      intros a' Hin Hin2
      have Hor := getVarsSubstCreateFvar Hin2
      cases Hor <;> simp_all
      next Hin3 =>
        apply @Hnin a' ?_ ?_
        exact List.mem_cons_of_mem h' Hin
        exact Hin3
      next Heq =>
        apply @Hnin h' ?_ ?_
        simp_all
        exfalso
        have Hht := substNodup_ht Hlen Hnd
        simp_all
    . -- invStores from σ₁ to σ'
      rw [subst_create_replace]
      apply invStoresSubstTail Hsubst Hsubst1 Hsome ?_ Hinv
      . simp [Imperative.substNodup] at Hnd
        simp_all
    . simp [List.Disjoint] at Hnin
      exact invStoresSubstHead Hsubst' Hnin.1

theorem createAssertsCorrect :
  Imperative.WellFormedSemanticEvalBool δ δP →
  Imperative.WellFormedSemanticEvalVar δ →
  Imperative.WellFormedSemanticEvalVal δ →
  -- TODO: remove congruence of old expressions, and require pre to contain no old expressions
  Boogie.WellFormedBoogieEvalCong δ →
  ks.length = ks'.length →
  Imperative.substNodup (ks.zip ks') →
  Imperative.substDefined σA σ' (ks.zip ks') →
  (∀ pre, pre ∈ pres →
    Imperative.invStores σA σ'
      ((Imperative.HasVarsPure.getVars (P:=Expression) pre).removeAll (ks ++ ks')) ∧
    ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) pre) ∧
    δP σA σA pre = some true) →
  EvalExpressions δ σ₀ σ (createFvars ks') vals →
  ReadValues σA ks vals →
  Imperative.substStores σ' σA (ks'.zip ks) →
  EvalStatementsContract π δ δP σ₀ σ' (createAsserts pres (ks.zip (createFvars ks'))) σ' := by
   intros Hwfb Hwfvr Hwfvl Hwfc Hlen Hnd Hdef Hpres Heval Hrd Hsubst2
   simp [createAsserts]
   -- Make index parameter `i` explicit so that we can induct generalizing `i`.
   suffices h : ∀ (i : Nat) (l : List Expression.Expr),
     (∀ pre, pre ∈ l →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) pre).removeAll (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) pre) ∧
       δP σA σA pre = some true) →
     EvalStatementsContract π δ δP σ₀ σ'
       (List.mapIdx (fun j pred => Statement.assert s!"assert_{i + j}"
         (Lambda.LExpr.substFvars pred (ks.zip (createFvars ks')))) l) σ'
   by
    have := @h 0 pres Hpres
    simp at this; exact this
   intros i l Hl
   induction l generalizing i
   case nil =>
     simp; constructor
   case cons st sts ih =>
     simp; constructor; constructor; constructor; constructor
     specialize Hl st (by simp)
     . have Heq : δ σA σA st = δ σ₀ σ' (Lambda.LExpr.substFvars st (ks.zip (createFvars ks'))) := by
         apply Lambda.LExpr.substFvarsCorrect Hwfc Hwfvr Hwfvl Hlen Hdef Hnd ?_ Hl.2.1 Hl.1
         . apply Imperative.substStoresFlip'
           simp [Imperative.substSwap, zip_swap]
           assumption
       simp [Imperative.WellFormedSemanticEvalBool] at Hwfb
       rw [(Hwfb _ _ _).1.1.mp]
       have Hl' := (Hwfb _ _ _).1.1.mpr Hl.2.2
       simp [← Hl']
       exact Eq.symm Heq
     . assumption
     . simp [Imperative.isDefinedOver, Command.modifiedVars,
             Imperative.Cmd.modifiedVars,
             Imperative.HasVarsImp.modifiedVars,
             Imperative.isDefined]
     . have ih' := ih (i + 1)
       ac_nf at ih'
       apply ih'
       intros pre Hin
       simp_all

theorem createAssumesCorrect :
  Imperative.WellFormedSemanticEvalBool δ δP →
  Imperative.WellFormedSemanticEvalVar δ →
  Imperative.WellFormedSemanticEvalVal δ →
  Boogie.WellFormedBoogieEvalCong δ →
  ks.length = ks'.length →
  Imperative.substNodup (ks.zip ks') →
  Imperative.substDefined σA σ' (ks.zip ks') →
  (∀ post, post ∈ posts →
    Imperative.invStores σA σ'
      ((Imperative.HasVarsPure.getVars (P:=Expression) post).removeAll (ks ++ ks')) ∧
    ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) post) ∧
    δP σ₀' σA post = some true) →
  Imperative.substStores σA σ' (ks.zip ks') →
  EvalStatementsContract π δ δP σ₀ σ' (createAssumes posts (ks.zip (createFvars ks'))) σ' := by
   intros Hwfb Hwfvr Hwfvl Hwfc Hlen Hnd Hdef Hposts Hsubst2
   simp [createAssumes]
   -- Make index parameter `i` explicit so that we can induct generalizing `i`.
   suffices h : ∀ (i : Nat) (l : List Expression.Expr),
     (∀ post, post ∈ l →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) post).removeAll (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) post) ∧
       δP σ₀' σA post = some true) →
     EvalStatementsContract π δ δP σ₀ σ'
       (List.mapIdx (fun j pred => Statement.assume s!"assume_{i + j}"
         (Lambda.LExpr.substFvars pred (ks.zip (createFvars ks')))) l) σ'
   by
    have := @h 0 posts Hposts
    simp at this; exact this
   intros i l Hl
   induction l generalizing i
   case nil =>
    simp; constructor
   case cons st sts ih =>
    simp ; constructor ; constructor ; constructor ; constructor
    specialize Hl st (by simp)
    . have Heq : δ σ₀' σA st = δ σ₀ σ' (Lambda.LExpr.substFvars st (ks.zip (createFvars ks'))) := by
        apply Lambda.LExpr.substFvarsCorrect Hwfc Hwfvr Hwfvl Hlen Hdef Hnd Hsubst2 Hl.2.1 Hl.1
      simp [Imperative.WellFormedSemanticEvalBool] at Hwfb
      rw [(Hwfb _ _ _).1.1.mp]
      have Hposts' := (Hwfb _ _ _).1.1.mpr Hl.2.2
      simp [← Hposts']
      exact Eq.symm Heq
    . assumption
    . simp [Imperative.isDefinedOver, Command.modifiedVars,
            Imperative.Cmd.modifiedVars,
            Imperative.HasVarsImp.modifiedVars,
            Imperative.isDefined]
    . have ih' := ih (i + 1)
      ac_nf at ih'
      apply ih'
      intros post Hin
      simp_all

theorem SubstPostsMem :
  substPost ∈ OldExpressions.substsOldExprs (createOldVarsSubst oldTrips)
  (OldExpressions.normalizeOldExprs vs) →
  ∃ post, post ∈ vs ∧
    substPost = OldExpressions.substsOldExpr (createOldVarsSubst oldTrips) (OldExpressions.normalizeOldExpr post)
  := by
  intros Hin
  generalize Heq : OldExpressions.substsOldExprs
                    (createOldVarsSubst oldTrips)
                    (OldExpressions.normalizeOldExprs vs) = l at *
  cases vs <;> simp [OldExpressions.normalizeOldExprs,
                     OldExpressions.substsOldExprs] at *
  case nil => simp_all
  case cons h t =>
    simp [← Heq] at *
    cases Hin with
    | inl Hin =>
      left; assumption
    | inr Hin =>
      right
      cases Hin with
      | intro id HH =>
      exact ⟨id, HH.1, Eq.symm HH.2⟩

/--
Generate the substitution pairs needed for the body of the procedure
-/
def createOldStoreSubst
  (trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident))
  : List (Expression.Ident × Expression.Ident) :=
    trips.map go where go
    | ((v', _), v) => (v, v')

theorem createOldStoreSubstEq :
  createOldStoreSubst oldTrips =
  oldTrips.unzip.2.zip oldTrips.unzip.1.unzip.1 := by
  induction oldTrips <;> simp [createOldStoreSubst, createOldStoreSubst.go] at *
  case cons h t ih => exact ih

theorem substOldCorrect :
  Imperative.WellFormedSemanticEvalVar δ →
  Imperative.WellFormedSemanticEvalVal δ →
  Boogie.WellFormedBoogieEvalCong δ →
  Boogie.WellFormedBoogieEvalTwoState δ σ₀ σ →
  OldExpressions.NormalizedOldExpr e →
  Imperative.invStores σ₀ σ₀'
    ((OldExpressions.extractOldExprVars e).removeAll [fro]) →
  Imperative.substDefined σ₀ σ [(fro, to)] →
  Imperative.substStores σ₀ σ [(fro, to)] →
  -- substitute the store and the expression simultaneously
  δ σ₀ σ e = δ σ₀' σ (OldExpressions.substOld fro (createFvar to) e) := by
  intros Hwfvr Hwfvl Hwfc Hwf2 Hnorm Hinv Hdef Hsubst
  induction e <;> simp [OldExpressions.substOld] at *
  case const c ty | op o ty | bvar x =>
    rw [Hwfvl.2]
    rw [Hwfvl.2]
    constructor
    constructor
  case fvar name ty =>
    simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
    rw [Hwfvr]
    rw [Hwfvr]
    exact name
    simp [Imperative.HasFvar.getFvar]
    simp [Imperative.HasFvar.getFvar]
  case mdata info e ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    cases Hnorm with
    | mdata Hnorm =>
    specialize ih Hnorm Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    have Hinfo := Hwfc.2.1
    specialize Hinfo info
    simp [Hinfo]
  case abs ty e ih  =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    cases Hnorm with
    | abs Hnorm =>
    specialize ih Hnorm Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    apply Hwfc.1
  case quant k ty e ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    cases Hnorm with
    | quant Hnorm =>
    specialize ih Hnorm Hinv
    specialize Hwfc _ _ _ _ _ _ ih
    have Hquant := Hwfc.2.2.1
    exact Hquant k ty
  case app c fn fih eih =>
    cases Hnorm with
    | app Hc Hfn Hwf =>
    specialize fih Hc ?_
    . intros k1 k2 Hin
      rw [Hinv]
      unfold OldExpressions.extractOldExprVars at ⊢
      split <;> simp_all
      . unfold OldExpressions.extractOldExprVars at Hin
        simp_all
      . unfold OldExpressions.extractOldExprVars at Hin
        simp_all
      . simp [List.app_removeAll, List.zip_append]
        simp_all
    specialize eih Hfn ?_
    . intros k1 k2 Hin
      rw [Hinv]
      unfold OldExpressions.extractOldExprVars at ⊢
      split <;> simp_all
      . unfold OldExpressions.extractOldExprVars at Hin
        simp_all
      . specialize Hwf _
        constructor
        cases Hwf
        simp_all
      . simp [List.app_removeAll, List.zip_append]
        simp_all
    split
    . -- is an old var
      split
      . -- is an old var that is substituted
        next x ty eq =>
        simp [eq] at *
        simp [WellFormedBoogieEvalTwoState] at Hwf2
        cases Hwf2.1 with
        | intro vs Hwf2' =>
        cases Hwf2' with
        | intro vs' Hwf2' =>
        cases Hwf2' with
        | intro σ₁ Hwf2' =>
        by_cases Hin : fro ∈ vs
        case pos e1 e2 ty' =>
        -- old var is modified
          have HH := ((Hwf2.2.1 vs vs' σ₀ σ₁ σ Hwf2'.1 Hwf2'.2) fro).1 Hin
          simp [OldExpressions.oldVar,
                OldExpressions.oldExpr,
                BoogieIdent.unres] at HH
          rw [HH]
          simp [createFvar]
          simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
          rw [Hwfvr (v:=to)]
          apply Hsubst
          exact List.mem_singleton.mpr rfl
          simp [Imperative.HasFvar.getFvar]
        case neg e1 e2 ty' =>
        -- old var is not modified
          have Hup := HavocVarsUpdateStates Hwf2'.1
          cases Hup with
          | intro as Hup =>
          have Hinit := InitVarsInitStates Hwf2'.2
          cases Hinit with
          | intro bs Hinit =>
          have Hsubst' := substStoresUpdatesInv' ?_ Hsubst Hup
          have Hsubst'' := substStoresInitsInv' ?_ Hsubst' Hinit
          . have HH := ((Hwf2.2.1 _ _ _ _ _ Hwf2'.1 Hwf2'.2) fro).2 Hin
            simp [OldExpressions.oldVar,
                  OldExpressions.oldExpr,
                  BoogieIdent.unres] at HH
            simp [createFvar]
            simp [HH]
            simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
            rw [Hwfvr (v:=to)]
            . simp [Imperative.substStores] at Hsubst''
              exact Hsubst''
            . simp [Imperative.HasFvar.getFvar]
          . simp [Imperative.substDefined] at *
            have Hdef' : Imperative.isDefined σ₀ [fro] := by
              simp [Imperative.isDefined]
              exact Hdef.1
            have Hdef'' := UpdateStatesDefMonotone Hdef' Hup
            simp [Imperative.isDefined] at Hdef''
            refine ⟨Hdef'', Hdef.2⟩
          . simp [List.Disjoint]
            intros a Hin Heq
            simp [Heq] at *
            contradiction
      . -- is an old var that is not substituted, use congruence
        specialize Hwfc _ _ _ _ _ _ fih
        have Hfun := Hwfc.2.2.2
        specialize Hfun _ _ eih
        have Hfun := Hfun.1
        exact Hfun
    . -- is not an old var, use congruence
      specialize Hwfc _ _ _ _ _ _ fih
      have Hfun := Hwfc.2.2.2
      specialize Hfun _ _ eih
      have Hfun := Hfun.1
      exact Hfun
  case ite c t e cih tih eih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    cases Hnorm with
    | ite Hc Ht He =>
    specialize cih Hc ?_
    . intros k1 k2 Hin
      rw [Hinv]
      simp [OldExpressions.extractOldExprVars,
            List.app_removeAll,
            List.zip_append]
      left; assumption
    specialize tih Ht ?_
    . intros k1 k2 Hin
      rw [Hinv]
      simp [OldExpressions.extractOldExprVars,
            List.app_removeAll,
            List.zip_append]
      right; left; assumption
    specialize eih He ?_
    . intros k1 k2 Hin
      rw [Hinv]
      simp [OldExpressions.extractOldExprVars,
            List.app_removeAll,
            List.zip_append]
      right; right; assumption
    specialize Hwfc _ _ _ _ _ _ tih
    have Hfun := Hwfc.2.2.2
    specialize Hfun _ _ eih
    have Hfun := Hfun.2.2
    specialize Hfun _ _ cih
    exact Hfun
  case eq e1 e2 e1ih e2ih =>
    simp [Boogie.WellFormedBoogieEvalCong] at Hwfc
    cases Hnorm with
    | eq He1 He2 =>
    specialize e1ih He1 ?_
    . intros k1 k2 Hin
      rw [Hinv]
      simp [OldExpressions.extractOldExprVars,
            List.app_removeAll,
            List.zip_append]
      left; assumption
    specialize e2ih He2 ?_
    . intros k1 k2 Hin
      rw [Hinv]
      simp [OldExpressions.extractOldExprVars,
            List.app_removeAll,
            List.zip_append]
      right; assumption
    specialize Hwfc _ _ _ _ _ _ e1ih
    have Hfun := Hwfc.2.2.2
    specialize Hfun _ _ e2ih
    have Hfun := Hfun.2.1
    exact Hfun

-- Needed from refinement theorem
-- UpdateState P✝ σ id v✝ σ'✝
-- Ht : TouchVars σ'✝ l₂ σ''
-- ⊢ TouchVars σ l₂ σ''

theorem UpdateStatesUpdatedId :
k ∈ vs →
UpdateStates σ₀ vs vs' σ₁ →
UpdateStates (updatedState σ₀ k v) vs vs' σ₁ := by
intros Hin Hup
have Hlen := UpdateStatesLength Hup
induction vs generalizing vs' σ₀ σ₁ k v <;> simp_all
case cons h t ih =>
  cases vs'
  case nil => simp_all
  case cons h' t' =>
    cases Hup with
    | update_some Hup Hups =>
    next σ'' =>
    cases Hin with
    | inl Heq =>
      -- the head is overwritten
      simp [Heq] at *
      apply UpdateStates.update_some (σ':=σ'') ?_ Hups
      constructor
      . simp [updatedState]
        rfl
      . cases Hup
        assumption
      . intros y Hne
        simp [updatedState]
        cases Hup
        split <;> simp_all
    | inr Heq =>
      -- a part of the tail is overwritten
      cases Hup with
      | update Hsome Hall Hsome' =>
      next v' =>
      by_cases Heq : h = k
      case pos =>
        -- both the tail and head are overwritten
        simp [Heq] at *
        apply UpdateStates.update_some (σ':=(updatedState σ'' k h'))
        . constructor
          . simp [updatedState]
            rfl
          . simp [updatedState]
          . intros y Hne
            simp [updatedState]
            split <;> simp_all
        . apply ih <;> simp_all
      case neg =>
        -- only the tail is overwritten
        apply UpdateStates.update_some (σ':=(updatedState σ'' k v))
        . constructor
          . simp [updatedState]
            simp_all
            rfl
          . simp [updatedState]
            simp_all
          . intros y Hne
            simp [updatedState]
            split <;> simp_all
        . apply ih <;> simp_all

theorem InitVarsRemoveAll {P: Imperative.PureExpr} [BEq P.Ident] [LawfulBEq P.Ident]
  {σ σ' : Imperative.SemanticStore P}
  {k : P.Ident} {v : P.Expr} {vs : List P.Ident} :
  σ' k = some v →
  InitVars σ vs σ' →
  InitVars (updatedState (P:=P) σ k v) (List.removeAll vs [k]) σ' := by
intros Hsome Hinit
have HinitSt := InitVarsInitStates Hinit
cases HinitSt with
| intro mv HinitSt =>
have Hnd := InitStatesNodup HinitSt
clear HinitSt
induction vs generalizing σ σ' k v
case nil =>
  simp_all
  simp [InitVarsEmpty Hinit] at *
  rw [updatedStateId] <;> simp_all
case cons h t ih =>
  cases Hinit with
  | init_some Hinit Hinits
  next vv σ₁ =>
  simp only [List.cons_removeAll]
  split
  -- the initialized variable h is not the same as the updated variable k
  . next Hne =>
    simp_all
    apply InitVars.init_some (σ':=(updatedState (updatedState σ k v) h vv))
    apply updatedStateInit
    . simp [updatedState]
      split <;> simp_all
      cases Hinit
      assumption
    . rw [updatedStateComm]
      apply ih Hsome
      have Heq := InitStateUpdated Hinit <;> simp_all
      exact fun a => Hne (Eq.symm a)
  -- the initialized variable h *is* the same as the updated variable k
  . next Heq =>
    -- assert that v = vv, since it has been initialized
    have Heq' : σ₁ k = some v := by
      have Hinitst := InitVarsInitStates Hinits
      cases Hinitst
      case intro t' Hinitst =>
        apply InitStatesSomeMonotone' ?_ Hsome
        apply Hinitst
        simp_all
    have Heq'' : σ₁ k = some vv := by
      have Hrd := InitStateReadValues Hinit
      cases Hrd <;> simp_all
    simp_all
    have Heq''' : (updatedState σ k v) = (updatedState σ₁ k v) := by
      funext x
      simp [updatedState]
      split <;> simp_all
      next Hne =>
      cases Hinit with
      | init Hnone Hsome Hall =>
      rw [Hall]
      exact fun a => Hne (Eq.symm a)
    simp_all

theorem updatedStateOldWellFormedBoogieEvalTwoState :
  σ k = some v →
  WellFormedBoogieEvalTwoState δ σ₀ σ →
  WellFormedBoogieEvalTwoState δ (updatedState σ₀ k v) σ := by
  intros Hsome Hwf2
  simp [WellFormedBoogieEvalTwoState] at *
  refine ⟨?_, Hwf2.2⟩
  cases Hwf2.1 with
  | intro vs Hwf2 =>
  cases Hwf2 with
  | intro vs' Hwf =>
  cases Hwf with
  | intro σ₁ Hwf =>
  by_cases Hin : k ∈ vs
  -- k is already in vs, use the mod/init lists as is
  case pos =>
    refine ⟨vs,vs',σ₁,?_,Hwf.2⟩
    have Hup := HavocVarsUpdateStates Hwf.1
    cases Hup with
    | intro vs' Hup =>
    apply UpdateStatesHavocVars (modvals:=vs')
    exact UpdateStatesUpdatedId Hin Hup
  -- k is not in vs, add k to vs
  case neg =>
    by_cases Hin' : k ∈ vs'
    -- k not in vs, but is in vs'.
    -- This is the case that k is a newly created variable
    -- Since we are updating/initializing k in σ₀, we remove k from vs'
    case pos =>
      refine ⟨vs,vs'.removeAll [k],(updatedState σ₁ k v),?_,?_⟩
      . refine HavocVarsUpdatedDist Hin ?_
        exact Hwf.1
      . apply InitVarsRemoveAll <;> simp_all
    -- k is not in vs'
    case neg =>
      have Hup := HavocVarsUpdateStates Hwf.1
      cases Hup with
      | intro es' Hup =>
      refine ⟨k :: vs,vs',σ₁,?_,Hwf.2⟩
      have Hdef1 : Imperative.isDefined σ₁ [k] := by
        apply InitVarsDefMonotone' (σ':=σ) (vs':=vs') <;> simp_all
        . simp_all [List.Disjoint]
        . simp [Imperative.isDefined, Option.isSome]
          split <;> simp_all
      have Hdef0 : Imperative.isDefined σ₀ [k] := by
        exact HavocVarsDefMonotone' (vs':=vs) Hdef1 Hwf.1
      simp [Imperative.isDefined, Option.isSome] at Hdef0
      split at Hdef0 <;> simp_all
      next x val heq =>
      apply UpdateStatesHavocVars (modvals:=val :: es')
      refine UpdateStatesUpdatedId ?_ ?_
      . exact List.mem_cons_self
      . apply UpdateStates.update_some (σ':=updatedState σ₀ k val)
        apply updatedStateUpdate <;> assumption
        rw [updatedStateId] <;> simp_all

open OldExpressions in
theorem substOld_create_replace :
NormalizedOldExpr e →
(extractOldExprVars (substOld h (createFvar h') e)) =
(extractOldExprVars e).removeAll [h] := by
  intros Hnorm
  induction Hnorm <;> simp [extractOldExprVars, createFvar, substOld] at * <;> try assumption
  case app fn e Hnfn Hne Hwf ih1 ih2 =>
    split
    . -- is old var
      next e1 e2 ty x ty =>
      split <;> simp [extractOldExprVars, List.removeAll] <;> simp_all
    . -- is a normal expression (non-old)
      next e1 e2 HH =>
      have Hnold : ¬ IsOldPred fn := by
        intros Hold
        specialize Hwf Hold
        cases Hold
        cases Hwf
        simp_all
        simp [BoogieIdent.unres] at HH
      have Hnold' : ¬ IsOldPred (substOld h (Lambda.LExpr.fvar h' none) fn) := by
        intros Hold
        apply Hnold
        apply substOldIsOldPred' ?_ Hold
        intros Hold
        cases Hold
      unfold extractOldExprVars
      simp
      split <;> simp_all
      . -- old var, contradiction
        exfalso; apply Hnold'; constructor
      . -- old expr, contradiction
        exfalso; apply Hnold'; constructor
      split <;> simp_all
      . -- old expr, contradiction
        exfalso; apply Hnold; constructor
      . simp [List.app_removeAll]
  case ite c t e cih tih eih =>
    rw [cih, tih, eih]
    simp [List.app_removeAll]
  case eq e1 e2 e1ih e2ih =>
    rw [e1ih, e2ih]
    simp [List.app_removeAll]

theorem substsOldCorrect :
  Imperative.WellFormedSemanticEvalVar δ →
  Imperative.WellFormedSemanticEvalVal δ →
  Boogie.WellFormedBoogieEvalCong δ →
  Boogie.WellFormedBoogieEvalTwoState δ σ₀ σ →
  OldExpressions.NormalizedOldExpr e →
  Imperative.substStores σ₀ σ (createOldStoreSubst oldTrips) →
  Imperative.substDefined σ₀ σ (createOldStoreSubst oldTrips) →
  Imperative.substNodup (createOldStoreSubst oldTrips) →
  oldTrips.unzip.1.unzip.1.Disjoint (OldExpressions.extractOldExprVars e) →
  δ σ₀ σ e = δ σ₀' σ (OldExpressions.substsOldExpr (createOldVarsSubst oldTrips) e) := by
  intros Hwfvr Hwfvl Hwfc Hwf2 Hnorm Hsubst Hdef Hnd Hdisj
  induction oldTrips generalizing e σ₀
  case nil =>
    simp [createOldVarsSubst, OldExpressions.substsOldExpr] at *
    cases Hwf2 with
    | intro vs Hwf2 =>
      apply Lambda.LExpr.substFvarsCorrectZero Hwfc Hwfvr Hwfvl
      intros k1 k2 Hin
      simp [zip_self_eq Hin]
  case cons h t ih =>
    simp [createOldVarsSubst, OldExpressions.substsOldExpr, OldExpressions.substsOldExpr] at *
    simp [createOldVarsSubst.go]
    simp [createOldStoreSubst, createOldStoreSubst.go] at Hsubst
    have Hsubst1 := substStoresCons' Hnd Hdef Hsubst
    cases Hsubst1 with
    | intro σ₁ Hsubst1 =>
    cases Hsubst1 with
    | intro v₁ Hsubst1 =>
    cases Hsubst1 with
    | intro Hsome Hsubst1 =>
    cases Hsubst1 with
    | intro Hstore Hsubst1 =>
    cases Hsubst1 with
    | intro Hsubst' Hsubst1 =>
    rw [← ih (σ₀ := σ₁)] <;> try simp_all
    rw [← substOldCorrect (e := e) Hwfvr Hwfvl Hwfc Hwf2 Hnorm] <;> try simp_all
    . apply invStoresSubstHead Hsubst'
      simp [List.Disjoint] at Hdisj
      simp_all
    . -- substDefined
      simp [createOldStoreSubst, createOldStoreSubst.go] at Hdef
      intros k1 k2 Hin
      apply Hdef <;> simp_all
    . -- substStores
      intros k1 k2 Hin
      apply Hsubst <;> simp_all
    . -- wfTwoState
      refine updatedStateOldWellFormedBoogieEvalTwoState ?_ Hwf2
      rw [← Hsubst]
      exact Hsome
      simp_all
    . -- normalized expr
      apply OldExpressions.substOldNormalizedMono
      . simp [createFvar]
        intros Hold
        cases Hold
      . simp_all
      . simp [createFvar]
        constructor
    . simp [Imperative.substNodup, createOldStoreSubst] at Hnd ⊢
      have Hnd2 := nodup_middle Hnd.2
      simp_all
    . -- substDefined
      refine substDefined_updatedState ?_
      exact substDefined_tail Hdef
    . simp [Imperative.substNodup, createOldStoreSubst] at Hnd ⊢
      have Hnd2 := nodup_middle Hnd.2
      simp_all
    . -- Disjoint
      rw [substOld_create_replace] <;> try assumption
      apply List.Disjoint.mono ?_ ?_ Hdisj
      . simp
      . simp [List.removeAll]

theorem genArgExprIdent_len' : (List.mapM genArgExprIdent t s).fst.length = t.length := by
  induction t generalizing s <;> simp_all
  case nil =>
    simp [pure, StateT.pure]
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map]
    split
    simp [StateT.map, Functor.map]
    apply ih

theorem genArgExprIdent_len : List.mapM genArgExprIdent t s = (a, s') → t.length = a.length := by
  intros Hgen
  generalize Heq : List.mapM genArgExprIdent t s = res at Hgen
  cases res with
  | mk fst snd =>
  have Heq' : (List.mapM genArgExprIdent t s).fst = fst := by simp [Heq]
  cases Hgen
  simp [← Heq']
  symm
  exact genArgExprIdent_len'

theorem genOutExprIdent_len' : (List.mapM genOutExprIdent t s).fst.length = t.length := by
  induction t generalizing s <;> simp_all
  case nil =>
    simp [pure, StateT.pure]
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map]
    split
    simp [StateT.map, Functor.map]
    apply ih

theorem genOldExprIdent_len' : (List.mapM genOldExprIdent t s).fst.length = t.length := by
  induction t generalizing s <;> simp_all
  case nil =>
    simp [pure, StateT.pure]
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map]
    split
    simp [StateT.map, Functor.map]
    apply ih

theorem getIdentTys!_len :
  getIdentTys! p xs s = (Except.ok a,s') →
  xs.length = a.length := by
  intros H
  induction xs generalizing s s' a <;> simp [getIdentTys!] at H
  case nil =>
    cases H
    rfl
  case cons h t ih =>
    simp [bind, ExceptT.bind, StateT.bind,
          ExceptT.bindCont, Functor.map, ExceptT.map, ExceptT.mk] at H
    split at H
    split at H
    . simp [bind, StateT.bind] at H
      split at H
      split at H
      . simp [pure, StateT.pure] at H
        cases H
        simp_all
        apply ih
        assumption
      . cases H
    . cases H

theorem genOutExprIdent_len : List.mapM genOutExprIdent t s = (a, s') → t.length = a.length := by
  intros Hgen
  generalize Heq : List.mapM genOutExprIdent t s = res at Hgen
  cases res with
  | mk fst snd =>
  have Heq' : (List.mapM genOutExprIdent t s).fst = fst := by simp [Heq]
  cases Hgen
  simp [← Heq']
  symm
  exact genOutExprIdent_len'

theorem genArgExprIdentsTrip_snd :
  genArgExprIdentsTrip tys args s = (Except.ok a, s') →
  List.map Prod.snd a = args := by
  intros Hgen
  simp [genArgExprIdentsTrip] at Hgen
  split at Hgen
  . simp [Functor.map, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
          ExceptT.mk, ExceptT.map, bind, StateT.bind] at Hgen
    split at Hgen
    split at Hgen <;> try cases Hgen
    next x a heq =>
    simp [genArgExprIdents] at heq
    induction args <;> simp_all
    case cons h t ih =>
    simp [bind, StateT.bind, Functor.map, StateT.map] at heq
    rw [List.map_snd_zip]
    simp
    split at heq
    cases heq
    next a' e' heq =>
    split at heq
    split at heq
    next a'' e'' heq'' =>
    cases heq
    simp_all
    rw [genArgExprIdent_len (t:=t) (a:=a'')] <;> try assumption
    simp_all
  . simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure] at Hgen
    cases Hgen

theorem genOutExprIdentsTrip_snd :
  genOutExprIdentsTrip tys args s = (Except.ok a, s') →
  List.map Prod.snd a = args := by
  intros Hgen
  simp [genOutExprIdentsTrip] at Hgen
  split at Hgen
  . simp [Functor.map, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
          ExceptT.mk, ExceptT.map, bind, StateT.bind] at Hgen
    split at Hgen
    split at Hgen <;> try cases Hgen
    next x a heq =>
    simp [genOutExprIdents] at heq
    induction args <;> simp_all
    case cons h t ih =>
    simp [bind, StateT.bind, Functor.map, StateT.map] at heq
    rw [List.map_snd_zip]
    simp
    split at heq
    cases heq
    next a' e' heq =>
    split at heq
    split at heq
    next a'' e'' heq'' =>
    cases heq
    simp_all
    rw [genOutExprIdent_len (t:=t) (a:=a'')] <;> try assumption
    simp_all
  . simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure] at Hgen
    cases Hgen

theorem genOldExprIdentsTrip_snd :
  genOldExprIdentsTrip p ids s = (Except.ok a, s') →
  List.map Prod.snd a = ids := by
  intros Hgen
  simp [genOldExprIdentsTrip, Functor.map, liftM, monadLift,
        MonadLift.monadLift, ExceptT.lift, ExceptT.mk, bind, pure, ExceptT.pure, ExceptT.bind,
        StateT.bind, ExceptT.bindCont, StateT.map] at Hgen
  split at Hgen
  next heq =>
  split at Hgen
  . simp [bind, StateT.bind, ExceptT.bindCont] at Hgen
    split at Hgen
    split at Hgen <;> try cases Hgen
    next x a heq' =>
    split at heq <;> simp_all
    next heq'' =>
    simp [genOldExprIdents] at heq''
    cases heq
    have Hlen := genOldExprIdent_len' (t:=ids) (s:=s)
    simp [heq''] at Hlen
    rw [List.map_snd_zip]
    simp [Hlen]
    simp [getIdentTys!_len heq']
  . cases Hgen

theorem Procedure.find.go_in_decls :
  Program.find?.go DeclKind.proc name decls = some (Decl.proc proc md) →
  Decl.proc proc md ∈ decls := by
  intro Hsome
  induction decls generalizing md <;> simp_all
  case nil => cases Hsome
  case cons h t ih =>
    simp [Program.find?.go] at Hsome
    split at Hsome <;> simp_all

theorem Procedure.find_in_decls :
  Program.Procedure.find? p name = some proc →
  ∃ md,
  .proc proc md ∈ p.decls := by
  intros Hsome
  simp [Program.Procedure.find?] at Hsome
  split at Hsome <;> simp_all
  simp [Decl.getProc] at Hsome
  split at Hsome <;> simp_all
  next md heq =>
  exists md
  simp [Program.find?] at heq
  exact find.go_in_decls heq

theorem Program.find.go_decl_kind_match :
  Program.find?.go d name decls = some decl →
  decl.kind = d := by
  intro Hsome
  induction decls
  case nil => cases Hsome
  case cons h t ih =>
    simp [Program.find?.go] at Hsome
    split at Hsome <;> simp_all

theorem Program.find.go_decl_name_match :
  Program.find?.go d name decls = some decl →
  decl.name = name := by
  intro Hsome
  induction decls
  case nil => cases Hsome
  case cons h t ih =>
    simp [Program.find?.go] at Hsome
    split at Hsome <;> simp_all

theorem Program.find.go_var_in_decls :
  Program.find?.go DeclKind.var name decls = some (Decl.var n ty e md) →
  Decl.var n ty e md ∈ decls := by
  intro Hsome
  induction decls generalizing md <;> simp_all
  case nil => cases Hsome
  case cons h t ih =>
    simp [Program.find?.go] at Hsome
    split at Hsome <;> simp_all

theorem Program.find.var_in_decls :
  Program.find? p DeclKind.var name = some decl →
  ∃ ty e md, Decl.var name ty e md ∈ p.decls ∧ decl = Decl.var name ty e md := by
  intros Hsome
  cases decl
  case var ty e md =>
    have H := go_decl_name_match Hsome
    simp [Decl.name] at H
    simp_all
    refine ⟨ty,e,md,?_,?_⟩
    . apply go_var_in_decls (name:=name)
      exact Hsome
    . simp_all
  case type | ax | proc | func =>
    simp [Program.find?] at Hsome
    have HH := Program.find.go_decl_kind_match Hsome
    simp [Decl.kind] at HH

theorem WFProgGlob :
  WF.WFDeclsProp p p.decls →
  PredImplies (isGlobalVar p ·) (BoogieIdent.isGlob ·) := by
  intros Hwf x HH
  simp [isGlobalVar, Option.isSome] at HH
  split at HH <;> simp at HH
  next x val heq =>
  have Hdecl := Program.find.var_in_decls heq
  cases Hdecl with
  | intro ty Hdecl => cases Hdecl with
  | intro e Hdecl => cases Hdecl with
  | intro md Hdecl =>
  have Hwfv := (List.Forall_mem_iff.mp Hwf) _ Hdecl.1
  exact Hwfv.1

theorem genOldExprIdentsEmpty :
  genOldExprIdentsTrip p [] s = (Except.ok trips, cs') → trips = [] := by
  intros Hgen
  simp [genOldExprIdentsTrip, bind, pure, liftM, MonadLift.monadLift, ExceptT.lift,
        ExceptT.bindCont, monadLift, ExceptT.bind, ExceptT.mk, StateT.bind, Functor.map] at Hgen
  split at Hgen
  split at Hgen
  . simp [ExceptT.bindCont, ExceptT.pure, ExceptT.mk, pure, StateT.bind, bind] at Hgen
    split at Hgen
    split at Hgen <;> simp_all
    . simp [StateT.pure,pure] at Hgen
      cases Hgen
      rfl
    . simp [StateT.pure,pure] at Hgen
      cases Hgen
  . simp [StateT.pure,pure] at Hgen
    cases Hgen

theorem genOldExprIdentsFind :
(∀ l, l ∈ ls → (p.find? DeclKind.var l).isSome) →
genOldExprIdentsTrip p ls s_out =
  (Except.ok oldTrips, cs) →
k ∈ oldTrips.unzip.snd →
(p.find? DeclKind.var k).isSome := by
intros Hfa Hgen Hin
induction ls generalizing oldTrips cs s_out <;> simp_all
case nil =>
  have Hempty := genOldExprIdentsEmpty Hgen
  simp [Hempty] at *
case cons h t ih =>
  simp [genOldExprIdentsTrip, bind, pure, liftM, MonadLift.monadLift, ExceptT.lift,
        ExceptT.bindCont, monadLift, ExceptT.bind, ExceptT.mk, StateT.bind, Functor.map] at Hgen
  split at Hgen
  split at Hgen
  . next heq =>
    simp [ExceptT.bindCont, ExceptT.pure, ExceptT.mk, pure, StateT.bind, bind] at Hgen
    split at Hgen
    split at Hgen <;> simp_all
    . simp [StateT.pure,pure] at Hgen
      cases Hgen
      cases Hin with
      | intro a Hin =>
      cases Hin with
      | intro b Hin =>
      have Hin := List.of_mem_zip Hin
      simp at Hin
      cases Hin.2 <;> simp_all
    . simp [StateT.pure,pure] at Hgen
      cases Hgen
  . simp [StateT.pure,pure] at Hgen
    cases Hgen

/--! Theorems about well-formedness of BoogieGen -/

theorem genArgExprIdentTemp :
  genArgExprIdent e s = (l, s') → BoogieIdent.isTemp l :=
  fun Hgen => by exact genBoogieIdentTemp Hgen

theorem genOutExprIdentTemp :
  genOutExprIdent e s = (l, s') → BoogieIdent.isTemp l :=
  fun Hgen => genBoogieIdentTemp Hgen

theorem genBoogieIdentGeneratedWF :
  BoogieGenState.gen pf s = (l, s') → s'.generated = l :: s.generated := by
  intros Hgen
  simp [BoogieGenState.gen] at Hgen
  rw [← Hgen.2]
  simp_all

theorem genIdentGeneratedWF :
  genIdent ident pf s = (l, s') → s'.generated = l :: s.generated :=
  fun Hgen => genBoogieIdentGeneratedWF Hgen

theorem genArgExprIdentGeneratedWF :
  genArgExprIdent e s = (l, s') → s'.generated = l :: s.generated :=
  fun Hgen => genBoogieIdentGeneratedWF Hgen

theorem genArgExprIdentsGeneratedWF :
  genArgExprIdents es s = (ls, s') →
  ls.reverse ++ s.generated = s'.generated
  := by
  intros Hgen
  simp [genArgExprIdents] at Hgen
  induction es generalizing s ls s' <;> simp at Hgen
  case nil =>
    simp [StateT.pure, pure] at Hgen
    cases Hgen <;> simp_all
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map, StateT.map, pure] at Hgen
    split at Hgen
    next a s₁ heq =>
    split at Hgen
    next a' s₂ heq' =>
    cases Hgen
    have HH := genArgExprIdentGeneratedWF heq
    specialize ih heq'
    simp [HH] at ih
    simp_all

theorem genArgExprIdentsTripGeneratedWF { s s' : BoogieGenState } :
  genArgExprIdentsTrip outs xs s = (Except.ok trips, s') →
  trips.unzip.1.unzip.1.reverse ++ s.generated = s'.generated := by
  intros Hgen
  apply genArgExprIdentsGeneratedWF (es:=xs)
  simp [genArgExprIdentsTrip] at *
  split at Hgen
  . simp [Functor.map, ExceptT.map, bind,
          liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
          ExceptT.mk, StateT.bind] at Hgen
    split at Hgen
    split at Hgen
    . next heq =>
      simp [pure, StateT.pure] at Hgen
      cases Hgen
      simp [StateT.map, Functor.map] at heq
      cases heq
      rw [← List.map_map]
      rw [List.map_fst_zip] <;> try simp_all
      rw [List.map_fst_zip] <;> try simp_all
      . rfl
      . simp [genArgExprIdents]
        rw [genArgExprIdent_len'] <;> simp_all
      . simp [genArgExprIdents]
        rw [genArgExprIdent_len'] <;> simp_all
    . simp [StateT.pure, pure] at Hgen
      cases Hgen
  . simp [throw, throwThe, MonadExceptOf.throw,
          ExceptT.mk, StateT.pure, pure] at Hgen
    cases Hgen

theorem genArgExprIdentWFMono :
  BoogieGenState.WF s →
  genArgExprIdent e s = (l, s') →
  BoogieGenState.WF s' :=
  fun Hgen => BoogieGenState.WFMono' Hgen

theorem genArgExprIdentsWFMono :
  BoogieGenState.WF s →
  genArgExprIdents es s = (ls, s') →
  BoogieGenState.WF s' := by
  intros Hwf Hgen
  simp [genArgExprIdents] at Hgen
  induction es generalizing s ls s' <;> simp at Hgen
  case nil =>
    simp [StateT.pure, pure] at Hgen
    cases Hgen <;> simp_all
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map, StateT.map, pure] at Hgen
    split at Hgen
    next a s₁ heq =>
    split at Hgen
    next a' s₂ heq' =>
    cases Hgen
    have HH := genArgExprIdentWFMono Hwf heq
    exact ih HH heq'

theorem genArgExprIdentsTripWFMono :
  BoogieGenState.WF s →
  genArgExprIdentsTrip outs xs s = (Except.ok trips, s') →
  BoogieGenState.WF s' := by
  intros Hwf Hgen
  simp [genArgExprIdentsTrip] at *
  split at Hgen
  . simp [Functor.map, ExceptT.map, bind,
          liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
          ExceptT.mk, StateT.bind] at Hgen
    split at Hgen
    split at Hgen
    . next a heq =>
      simp [pure, StateT.pure] at Hgen
      cases Hgen
      simp [StateT.map, Functor.map] at heq
      generalize Hgen' : (genArgExprIdents xs s) = gen at heq
      cases gen with
      | mk fst snd =>
      simp at heq
      cases heq
      apply genArgExprIdentsWFMono Hwf Hgen'
    . simp [StateT.pure, pure] at Hgen
      cases Hgen
  . simp [throw, throwThe, MonadExceptOf.throw,
          ExceptT.mk, StateT.pure, pure] at Hgen
    cases Hgen

theorem genOutExprIdentGeneratedWF :
  genOutExprIdent e s = (l, s') → s'.generated = l :: s.generated :=
  fun Hgen => genBoogieIdentGeneratedWF Hgen

theorem genOutExprIdentsGeneratedWF :
  genOutExprIdents es s = (ls, s') →
  ls.reverse ++ s.generated = s'.generated
  := by
  intros Hgen
  simp [genOutExprIdents] at Hgen
  induction es generalizing s ls s' <;> simp at Hgen
  case nil =>
    simp [StateT.pure, pure] at Hgen
    cases Hgen <;> simp_all
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map, StateT.map, pure] at Hgen
    split at Hgen
    next a s₁ heq =>
    split at Hgen
    next a' s₂ heq' =>
    cases Hgen
    have HH := genOutExprIdentGeneratedWF heq
    specialize ih heq'
    simp [HH] at ih
    simp_all

theorem genOutExprIdentsTripGeneratedWF { s s' : BoogieGenState } :
  genOutExprIdentsTrip outs xs s = (Except.ok trips, s') →
  trips.unzip.1.unzip.1.reverse ++ s.generated = s'.generated := by
  intros Hgen
  apply genOutExprIdentsGeneratedWF (es:=xs)
  simp [genOutExprIdentsTrip] at *
  split at Hgen
  . simp [Functor.map, ExceptT.map, bind,
          liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
          ExceptT.mk, StateT.bind] at Hgen
    split at Hgen
    split at Hgen
    . next heq =>
      simp [pure, StateT.pure] at Hgen
      cases Hgen
      simp [StateT.map, Functor.map] at heq
      cases heq
      rw [← List.map_map]
      rw [List.map_fst_zip] <;> try simp_all
      rw [List.map_fst_zip] <;> try simp_all
      . rfl
      . simp [genOutExprIdents]
        rw [genOutExprIdent_len'] <;> simp_all
      . simp [genOutExprIdents]
        rw [genOutExprIdent_len'] <;> simp_all
    . simp [StateT.pure, pure] at Hgen
      cases Hgen
  . simp [throw, throwThe, MonadExceptOf.throw,
          ExceptT.mk, StateT.pure, pure] at Hgen
    cases Hgen

theorem genOutExprIdentWFMono :
  BoogieGenState.WF s →
  genOutExprIdent e s = (l, s') →
  BoogieGenState.WF s' :=
  fun Hgen => BoogieGenState.WFMono' Hgen

theorem genOutExprIdentsWFMono :
  BoogieGenState.WF s →
  genOutExprIdents es s = (ls, s') →
  BoogieGenState.WF s' := by
  intros Hwf Hgen
  simp [genOutExprIdents] at Hgen
  induction es generalizing s ls s' <;> simp at Hgen
  case nil =>
    simp [StateT.pure, pure] at Hgen
    cases Hgen <;> simp_all
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map, StateT.map, pure] at Hgen
    split at Hgen
    next a s₁ heq =>
    split at Hgen
    next a' s₂ heq' =>
    cases Hgen
    have HH := genOutExprIdentWFMono Hwf heq
    exact ih HH heq'

theorem genOutExprIdentsTripWFMono :
  BoogieGenState.WF s →
  genOutExprIdentsTrip outs xs s = (Except.ok trips, s') →
  BoogieGenState.WF s' := by
  intros Hwf Hgen
  simp [genOutExprIdentsTrip] at *
  split at Hgen
  . simp [Functor.map, ExceptT.map, bind,
          liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
          ExceptT.mk, StateT.bind] at Hgen
    split at Hgen
    split at Hgen
    . next a heq =>
      simp [pure, StateT.pure] at Hgen
      cases Hgen
      simp [StateT.map, Functor.map] at heq
      generalize Hgen' : (genOutExprIdents xs s) = gen at heq
      cases gen with
      | mk fst snd =>
      simp at heq
      cases heq
      apply genOutExprIdentsWFMono Hwf Hgen'
    . simp [StateT.pure, pure] at Hgen
      cases Hgen
  . simp [throw, throwThe, MonadExceptOf.throw,
          ExceptT.mk, StateT.pure, pure] at Hgen
    cases Hgen

theorem genOldExprIdentGeneratedWF :
  genOldExprIdent e s = (l, s') → s'.generated = l :: s.generated :=
  fun Hgen => genBoogieIdentGeneratedWF Hgen

theorem genOldExprIdentsGeneratedWF :
  genOldExprIdents es s = (ls, s') →
  ls.reverse ++ s.generated = s'.generated
  := by
  intros Hgen
  simp [genOldExprIdents] at Hgen
  induction es generalizing s ls s' <;> simp at Hgen
  case nil =>
    simp [StateT.pure, pure] at Hgen
    cases Hgen <;> simp_all
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map, StateT.map, pure] at Hgen
    split at Hgen
    next a s₁ heq =>
    split at Hgen
    next a' s₂ heq' =>
    cases Hgen
    have HH := genOldExprIdentGeneratedWF heq
    specialize ih heq'
    simp [HH] at ih
    simp_all

theorem genOldExprIdentsTripGeneratedWF { s s' : BoogieGenState } :
  genOldExprIdentsTrip p xs s = (Except.ok trips, s') →
  trips.unzip.1.unzip.1.reverse ++ s.generated = s'.generated := by
  intros Hgen
  apply genOldExprIdentsGeneratedWF (es:=xs)
  simp [genOldExprIdentsTrip, bind, liftM,] at *
  simp [Functor.map, ExceptT.bind, ExceptT.bindCont, bind,
        monadLift, MonadLift.monadLift, ExceptT.lift,
        ExceptT.mk, StateT.bind] at Hgen
  split at Hgen
  split at Hgen
  . next heq =>
    simp [bind, StateT.bind] at Hgen
    split at Hgen
    next heq' =>
    simp [ExceptT.bindCont] at Hgen
    split at Hgen
    . cases Hgen
      simp [StateT.map, Functor.map] at heq
      cases heq
      rw [← List.map_map]
      rw [List.map_fst_zip] <;> try simp_all
      rw [List.map_fst_zip] <;> try simp_all
      rw [← getIdentTys!_store_same heq']
      congr
      . simp [genOldExprIdents]
        rw [← getIdentTys!_len heq']
        rw [genOldExprIdent_len'] <;> simp_all
      . simp [genOldExprIdents]
        rw [← getIdentTys!_len heq']
        rw [genOldExprIdent_len'] <;> simp_all
    . cases Hgen
  . cases Hgen

theorem genOldExprIdentWFMono :
  BoogieGenState.WF s →
  genOldExprIdent e s = (l, s') →
  BoogieGenState.WF s' :=
  fun Hgen => BoogieGenState.WFMono' Hgen

theorem genOldExprIdentsWFMono :
  BoogieGenState.WF s →
  genOldExprIdents es s = (ls, s') →
  BoogieGenState.WF s' := by
  intros Hwf Hgen
  simp [genOldExprIdents] at Hgen
  induction es generalizing s ls s' <;> simp at Hgen
  case nil =>
    simp [StateT.pure, pure] at Hgen
    cases Hgen <;> simp_all
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map, StateT.map, pure] at Hgen
    split at Hgen
    next a s₁ heq =>
    split at Hgen
    next a' s₂ heq' =>
    cases Hgen
    have HH := genOldExprIdentWFMono Hwf heq
    exact ih HH heq'

theorem genOldExprIdentsTripWFMono :
  BoogieGenState.WF s →
  genOldExprIdentsTrip outs xs s = (Except.ok trips, s') →
  BoogieGenState.WF s' := by
  intros Hwf Hgen
  simp [genOldExprIdentsTrip, bind, liftM,] at *
  simp [Functor.map, ExceptT.bind, ExceptT.bindCont, bind,
        monadLift, MonadLift.monadLift, ExceptT.lift,
        ExceptT.mk, StateT.bind] at Hgen
  split at Hgen
  split at Hgen
  . next heq =>
    simp [bind, StateT.bind] at Hgen
    split at Hgen
    next heq' =>
    simp [ExceptT.bindCont] at Hgen
    split at Hgen
    . cases Hgen
      simp [StateT.map, Functor.map] at heq
      cases heq
      generalize Hgen' : (genOldExprIdents xs s) = gen at heq'
      cases gen with
      | mk fst snd =>
      rw [← getIdentTys!_store_same heq']
      exact genOldExprIdentsWFMono Hwf Hgen'
    . cases Hgen
  . cases Hgen

theorem List.Subset.trans :
  List.Subset a b → b.Subset c → a.Subset c := fun H1 H2 _ Hin => H2 (H1 Hin)

theorem List.Subset.app :
  List.Subset a c → b.Subset c → (a ++ b).Subset c := by
  intros H1 H2
  intros x Hin
  simp at Hin
  cases Hin with
  | inl Hin =>
    exact H1 Hin
  | inr Hin =>
    exact H2 Hin

open OldExpressions in
theorem extractedOldExprInVars :
  NormalizedOldExpr post →
  (extractOldExprVars post).Subset
  (Imperative.HasVarsPure.getVars post) := by
  intros Hnorm
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
          Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    . simp [Lambda.LExpr.LExpr.getVars]
      intros x Hin
      exact Hin
    . next Hfalse =>
      cases Hnorm with
      | app H1 H2 Hn =>
      exfalso
      specialize Hn ?_
      constructor
      cases Hn
      apply Hfalse
      rfl
    . cases Hnorm with
      | app H1 H2 Hn =>
      apply List.Subset.app
      . apply List.Subset.trans
        apply fn_ih
        exact H1
        intros x Hin
        simp_all
      . apply List.Subset.trans
        apply e_ih
        exact H2
        intros x Hin
        simp_all
  case mdata ih | abs ih | quant ih =>
    cases Hnorm
    apply ih <;> assumption
  case ite cih tih eih =>
    cases Hnorm
    apply List.Subset.app
    . apply List.Subset.trans
      apply cih <;> assumption
      intros x Hin
      simp_all
    apply List.Subset.app
    . apply List.Subset.trans
      apply tih <;> assumption
      intros x Hin
      simp_all
    . apply List.Subset.trans
      apply eih <;> assumption
      intros x Hin
      simp_all
  case eq ih1 ih2 =>
    cases Hnorm
    apply List.Subset.app
    . apply List.Subset.trans
      apply ih1 <;> assumption
      intros x Hin
      simp_all
    . apply List.Subset.trans
      apply ih2 <;> assumption
      intros x Hin
      simp_all

open OldExpressions in
theorem normalizeOldExprInVarsTrue:
  (Lambda.LExpr.LExpr.getVars (normalizeOldExpr e true)).Subset
  (Lambda.LExpr.LExpr.getVars (normalizeOldExpr e)) := by
  induction e <;>
      simp [normalizeOldExpr, Lambda.LExpr.LExpr.getVars] at * <;>
      try simp_all
  case app fn e fn_ih e_ih =>
    unfold normalizeOldExpr
    split
    split
    split
    . simp [Lambda.LExpr.LExpr.getVars] at *
      intros x Hin
      exact Hin
    . intros x Hin
      exact Hin
    . simp [Lambda.LExpr.LExpr.getVars, normalizeOldExpr] at *
      exact e_ih
    . simp [Lambda.LExpr.LExpr.getVars] at *
      apply List.Subset.app
      . apply List.Subset.trans
        apply fn_ih
        intros x Hin
        simp_all
      . apply List.Subset.trans
        apply e_ih
        intros x Hin
        simp_all
  case fvar => intros x Hin; exact Hin
  case ite cih tih eih =>
    apply List.Subset.app
    . apply List.Subset.trans
      apply cih <;> assumption
      intros x Hin
      simp_all
    apply List.Subset.app
    . apply List.Subset.trans
      apply tih <;> assumption
      intros x Hin
      simp_all
    . apply List.Subset.trans
      apply eih <;> assumption
      intros x Hin
      simp_all
  case eq ih1 ih2 =>
    apply List.Subset.app
    . apply List.Subset.trans
      apply ih1 <;> assumption
      intros x Hin
      simp_all
    . apply List.Subset.trans
      apply ih2 <;> assumption
      intros x Hin
      simp_all

open OldExpressions in
theorem normalizeOldExprInVars :
  (Imperative.HasVarsPure.getVars (P:=Expression) (normalizeOldExpr post)).Subset
  (Imperative.HasVarsPure.getVars post) := by
  induction post <;>
    simp [normalizeOldExpr,
          Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold normalizeOldExpr
    split
    split
    split
    . simp [Lambda.LExpr.LExpr.getVars] at *
      intros x Hin
      exact Hin
    . simp [Lambda.LExpr.LExpr.getVars] at *
      apply List.Subset.trans
      apply normalizeOldExprInVarsTrue
      exact e_ih
    . simp [Lambda.LExpr.LExpr.getVars, normalizeOldExpr] at *
      exact e_ih
    . simp [Lambda.LExpr.LExpr.getVars] at *
      apply List.Subset.app
      . apply List.Subset.trans
        apply fn_ih
        intros x Hin
        simp_all
      . apply List.Subset.trans
        apply e_ih
        intros x Hin
        simp_all
  case fvar => intros x Hin; exact Hin
  case ite cih tih eih =>
    apply List.Subset.app
    . apply List.Subset.trans
      apply cih <;> assumption
      intros x Hin
      simp_all
    apply List.Subset.app
    . apply List.Subset.trans
      apply tih <;> assumption
      intros x Hin
      simp_all
    . apply List.Subset.trans
      apply eih <;> assumption
      intros x Hin
      simp_all
  case eq ih1 ih2 =>
    apply List.Subset.app
    . apply List.Subset.trans
      apply ih1 <;> assumption
      intros x Hin
      simp_all
    . apply List.Subset.trans
      apply ih2 <;> assumption
      intros x Hin
      simp_all

open OldExpressions in
theorem extractedOldVarsInVars :
  ValidExpression post →
  (extractOldExprVars
    (normalizeOldExpr post)).Subset
  (Imperative.HasVarsPure.getVars post) := by
  intros Hvalid
  apply List.Subset.trans
  . apply extractedOldExprInVars
    exact normalizeOldExprSound Hvalid
  . exact normalizeOldExprInVars

open OldExpressions in
theorem substOldPostSubset:
  (Imperative.HasVarsPure.getVars (P:=Expression)
    (substOld h2 (Lambda.LExpr.fvar h1 ty) post)).Subset
    (Imperative.HasVarsPure.getVars (P:=Expression) post ++ [h1]) := by
  induction post <;> simp [substOld]
  case fvar | op | const | bvar =>
    intros x Hin ; simp_all
  case mdata ih | abs ih | quant ih =>
    exact ih
  case ite cih tih eih =>
    simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    apply List.Subset.app
    . apply List.Subset.trans
      apply cih <;> assumption
      intros x Hin
      simp_all
      cases Hin <;> simp_all
    apply List.Subset.app
    . apply List.Subset.trans
      apply tih <;> assumption
      intros x Hin
      simp_all
      cases Hin <;> simp_all
    . apply List.Subset.trans
      apply eih <;> assumption
      intros x Hin
      simp_all
  case app ih1 ih2 =>
    split
    . split
      . simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
        intros x Hin
        simp_all
      . simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
        intros x Hin
        simp_all
    . simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
      apply List.Subset.app
      . apply List.Subset.trans
        apply ih1 <;> assumption
        intros x Hin
        simp_all
        cases Hin <;> simp_all
      . apply List.Subset.trans
        apply ih2 <;> assumption
        intros x Hin
        simp_all
  case eq ih1 ih2 =>
    simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
    apply List.Subset.app
    . apply List.Subset.trans
      apply ih1 <;> assumption
      intros x Hin
      simp_all
      cases Hin <;> simp_all
    . apply List.Subset.trans
      apply ih2 <;> assumption
      intros x Hin
      simp_all

open OldExpressions in
theorem substsOldPostSubset:
  oldTrips.unzip.1.unzip.1.Disjoint oldTrips.unzip.2 →
  (Imperative.HasVarsPure.getVars (substsOldExpr (createOldVarsSubst oldTrips) post)).Subset
    (Imperative.HasVarsPure.getVars post ++ (oldTrips.unzip.1.unzip.1)) := by
  intros Hdisj
  induction oldTrips generalizing post <;>
    simp [createFvar, createOldVarsSubst, createOldVarsSubst.go, substsOldExpr] at *
  case nil =>
    intros x Hin
    exact Hin
  case cons h t ih =>
    apply List.Subset.trans
      (b:=(Imperative.HasVarsPure.getVars
            (P:=Expression) (substOld h.snd (Lambda.LExpr.fvar h.1.fst none) post)) ++
            List.map (Prod.fst ∘ Prod.fst) t)
    . apply ih
      intros x Hin1 Hin2
      apply @Hdisj x <;> simp_all
    . apply List.Subset.app
      apply List.Subset.trans
      apply substOldPostSubset
      . intros x Hin
        simp at Hin
        cases Hin <;> simp_all
      . intros x Hin
        simp_all

set_option maxHeartbeats 500000
-- Second, the program/statement returned by callElim has the same semantics as the pre-transformation program/statement
theorem callElimStatementCorrect :
  -- procedure lookup function is well-behaved
  (∀ pname, π pname = (Program.Procedure.find? p (.unres pname))) →
  -- all global variables in p exist in σ
  (∀ gk, (p.find? .var gk).isSome → (σ gk).isSome) →
  EvalStatementsContract π δ δP σ₀ σ [st] σ' →
  WellFormedBoogieEvalCong δ →
  WF.WFStatementsProp p [st] →
  WF.WFProgramProp p →
  BoogieGenState.WF γ →
  (∀ v, v ∈ γ.generated ↔ ((σ v).isSome ∧ BoogieIdent.isTemp v)) →
  (Except.ok sts, γ') = (CallElim.runCallElimWith' [st] (CallElim.callElimStmts · p) γ) →
  -- NOTE: The theorem does not expect the same store due to inserting new temp variables
  exists σ'',
    Inits σ' σ'' ∧
    EvalStatementsContract π δ δP σ₀ σ sts σ''
    := by
  intros Hp Hgv Heval Hwfc Hwf Hwfp Hwfgen Hwfgenst Helim
  cases st <;>
  simp [StateT.run, callElimStmts, callElimStmt,
        pure, ExceptT.pure, ExceptT.mk, StateT.pure,
        bind, ExceptT.bind, ExceptT.bindCont, StateT.bind,
        ] at Helim
        <;> try simp [Helim]
  case block => exact ⟨σ', Inits.init InitVars.init_none, Heval⟩
  case ite => exact ⟨σ', Inits.init InitVars.init_none, Heval⟩
  case goto => exact ⟨σ', Inits.init InitVars.init_none, Heval⟩
  case loop => exact ⟨σ', Inits.init InitVars.init_none, Heval⟩
  case cmd c =>
  cases c with
  | cmd c' =>
    exists σ'
    refine ⟨?_, ?_⟩
    exact Inits.init InitVars.init_none
    simp [StateT.pure, StateT.bind, ExceptT.bindCont, pure, bind] at Helim
    simp_all
  | call lhs procName args md =>
  split at Helim
  next pair l cs' Helim' =>
  -- NOTE: the simplifier must be invoked in two stages in this case
  -- in order to get to
  -- Helim : sts = a✝ ∧ γ' = cs'
  split at Helim
    <;> simp only [StateT.bind, StateT.pure, ExceptT.bindCont, pure_bind, List.append_nil] at Helim
    <;> simp [pure] at Helim
  next res l =>
    simp [Helim] at *
    cases Hwf with | intro Hwf =>
    cases Hwf with | mk Hwf =>
    simp [Option.isSome] at Hwf
    split at Hwf <;> simp_all
    next decl' proc Hfa Harglen Houtlen Hlhsdisj Hlhs Hwfargs Hfind =>
    cases Heval with | stmts_some_sem Heval Heval2 =>
    cases Heval with
    | cmd_sem Heval Hdef =>
    cases Heval with
    | call_sem lkup Hevalargs Hevalouts Hwfval Hwfvars Hwfb Hwf2 Hwf Hinitin Hinitout Hpre Hhav1 Hhav2 Hpost Hrd Hupdate =>
      next outVals argVals σA σAO σO σR p' modvals =>
      have Hsome : (Program.Procedure.find? p procName).isSome := by simp [Hfind]
      simp [Option.isSome] at Hsome
      have lkup' := lkup
      split at Hsome <;> try contradiction
      next x val Hfind =>
      simp_all [-lkup]
      simp [bind,StateT.bind,ExceptT.bindCont,pure] at Helim'
      split at Helim' <;> try contradiction
      -- refactor arg labels generation expressions
      next res_arg s_arg Heqarg =>
      simp [←lkup'] at *
      split at Helim' <;> try simp [StateT.pure, StateT.bind, ExceptT.bindCont] at Helim' <;> try cases Helim'
      next argTrips =>
      have Heqargs : List.map Prod.snd argTrips = args := genArgExprIdentsTrip_snd Heqarg
      -- refactor out labels generation expressions
      generalize Heqout : (genOutExprIdentsTrip proc.header.outputs.toTrivialLTy lhs s_arg) = pair_out at Helim'
      cases pair_out
      next res_out s_out =>
      simp only [bind] at Helim'
      split at Helim' <;> try simp [pure, StateT.pure] at Helim' <;> try cases Helim'
      next outTrips =>
      have Heqouts : lhs = List.map Prod.snd outTrips := Eq.symm $ genOutExprIdentsTrip_snd Heqout
      have Hrdout := InitStatesReadValues Hinitout
      simp [StateT.bind, ExceptT.bindCont] at Helim'
      -- refactor old expressions generation expressions
      generalize Heqold : (genOldExprIdentsTrip p
          (List.filter (isGlobalVar p)
            (List.flatMap OldExpressions.extractOldExprVars
                (OldExpressions.normalizeOldExprs
                  (List.map Procedure.Check.expr proc.spec.postconditions.values))).eraseDups)
                s_out) = pair_old at Helim'
      cases pair_old <;> simp only at Helim'
      next res_old s_old =>
      simp only [bind] at Helim'
      split at Helim' <;> try simp [pure, StateT.pure] at Helim' <;> try cases Helim'
      next st' oldTrips =>
      -- extract well-formed program properties
      cases Hwfp with
      | mk wfvarnd wfprocnd wffncnd Hwfp =>
      have Hdecl := List.Forall_mem_iff.mp Hwfp
      have HH := Procedure.find_in_decls Hfind
      cases HH with
      | intro md HH =>
      specialize Hdecl (.proc proc md) HH
      cases Hdecl with
      | mk wfstmts wfloclnd Hiodisj Hinnd Houtnd Hmodsnd Hinlc Houtlc wfspec =>
      cases wfspec with
      | mk wfpre wfpost wfmod =>
      have HoldDef : Imperative.isDefined σ oldTrips.unzip.snd := by
        intros k Hin
        apply Hgv
        apply genOldExprIdentsFind ?_ Heqold Hin
        intros l Hin
        have HH := List.mem_filter.mp Hin
        exact HH.2
      have HrdOld := isDefinedReadValues HoldDef
      have Hwfgenargs : BoogieGenState.WF s_arg := genArgExprIdentsTripWFMono Hwfgen Heqarg
      have Hwfgenouts : BoogieGenState.WF s_out := genOutExprIdentsTripWFMono Hwfgenargs Heqout
      have Hwfgenolds : BoogieGenState.WF cs' := genOldExprIdentsTripWFMono Hwfgenouts Heqold
      have Hgenargs := genArgExprIdentsTripGeneratedWF Heqarg
      have Hgenouts := genOutExprIdentsTripGeneratedWF Heqout
      have Hgenolds := genOldExprIdentsTripGeneratedWF Heqold
      have HargTemp : Forall (BoogieIdent.isTemp ·) argTrips.unzip.1.unzip.1 := by
        simp [BoogieGenState.WF] at Hwfgenargs
        have HH := List.Forall_mem_iff.mp Hwfgenargs.2.2
        simp only [← Hgenargs] at HH
        refine List.Forall_mem_iff.mpr ?_
        intros x Hin
        apply HH
        exact List.mem_append_left γ.generated (List.mem_reverse.mpr Hin)
      have HoutTemp : Forall (BoogieIdent.isTemp ·) outTrips.unzip.1.unzip.1 := by
        simp [BoogieGenState.WF] at Hwfgenouts
        have HH := List.Forall_mem_iff.mp Hwfgenouts.2.2
        simp only [← Hgenouts] at HH
        refine List.Forall_mem_iff.mpr ?_
        intros x Hin
        apply HH
        exact List.mem_append_left s_arg.generated (List.mem_reverse.mpr Hin)
      have HoldTemp : Forall (BoogieIdent.isTemp ·) oldTrips.unzip.1.unzip.1 := by
        simp [BoogieGenState.WF] at Hwfgenolds
        have HH := List.Forall_mem_iff.mp Hwfgenolds.2.2
        simp only [← Hgenolds] at HH
        refine List.Forall_mem_iff.mpr ?_
        intros x Hin
        apply HH
        exact List.mem_append_left s_out.generated (List.mem_reverse.mpr Hin)
      have HgenApp : oldTrips.unzip.fst.unzip.fst.reverse ++
                     outTrips.unzip.fst.unzip.fst.reverse ++
                     argTrips.unzip.fst.unzip.fst.reverse ++
                     γ.generated = cs'.generated := by
        simp only [← Hgenargs,← Hgenouts,← Hgenolds]
        simp [List.append_assoc]
      have Hgennd' : (γ.generated.reverse ++
                      argTrips.unzip.fst.unzip.fst ++
                      outTrips.unzip.fst.unzip.fst ++
                      oldTrips.unzip.fst.unzip.fst).Nodup := by
        simp [BoogieGenState.WF] at Hwfgenolds
        have Hnd := nodup_reverse Hwfgenolds.2.1
        simp only [List.reverse_append, List.reverse_reverse, ← List.append_assoc,
                  ← Hgenargs,← Hgenouts,← Hgenolds] at Hnd
        exact Hnd
      have Hgennd : (argTrips.unzip.fst.unzip.fst ++
                      outTrips.unzip.fst.unzip.fst ++
                      oldTrips.unzip.fst.unzip.fst).Nodup := by
        simp only [List.append_assoc] at Hgennd' ⊢
        exact (List.nodup_append.mp Hgennd').2.1
      have Hinoutnd : (ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs).Nodup := by
        apply List.Disjoint_Nodup_iff.mp
        refine ⟨Hinnd, Houtnd, ?_⟩
        . exact Hiodisj
      have Hndefgen : Imperative.isNotDefined σ'
                      (argTrips.unzip.fst.unzip.fst ++
                      outTrips.unzip.fst.unzip.fst ++
                      oldTrips.unzip.fst.unzip.fst) := by
        simp only [EvalStmtsEmpty Heval2] at *
        apply UpdateStatesNotDefMonotone ?_ Hupdate
        intros v Hin
        have Htemp : v.isTemp = true := by
          simp only [List.append_assoc, List.mem_append] at Hin
          cases Hin with
          | inl Hin =>
            exact (List.Forall_mem_iff.mp HargTemp) _ Hin
          | inr Hin => cases Hin with
          | inl Hin =>
            exact (List.Forall_mem_iff.mp HoutTemp) _ Hin
          | inr Hin =>
            exact (List.Forall_mem_iff.mp HoldTemp) _ Hin
        refine Option.not_isSome_iff_eq_none.mp ?_
        intros Hsome
        have Hcontra := List.mem_reverse.mpr ((Hwfgenst v).mpr ⟨Hsome, Htemp⟩)
        simp only [List.append_assoc] at Hin Hgennd'
        exact (List.nodup_append.mp Hgennd').2.2 v Hcontra v Hin rfl
      have Hmodglob : Forall (BoogieIdent.isGlob ·) proc.spec.modifies := by
        simp [WF.WFModsProp] at wfmod
        apply List.Forall_PredImplies
        exact wfmod
        intros x HH
        apply WFProgGlob Hwfp
        exact WF.WFModProp.defined HH
      have Holdsndglob : Forall (BoogieIdent.isGlob ·) oldTrips.unzip.snd := by
        simp [genOldExprIdentsTrip_snd Heqold]
        apply List.Forall_PredImplies
        apply List.Forall_filter
        apply WFProgGlob Hwfp
      -- derive some equivalence between stores
      have Hrd' := ReadValuesAppKeys' Hrd
      cases Hrd' with
      | intro v1 Hrd' => cases Hrd' with
      | intro v2 Hrd' =>
      have Hup1 := HavocVarsUpdateStates Hhav1
      cases Hup1 with
      | intro v1' Hup1 =>
      have Hup2 := HavocVarsUpdateStates Hhav2
      cases Hup2 with
      | intro v2' Hup2 =>
      cases HrdOld with
      | intro oldVals HoldVals =>
      have Hargtriplen : argTrips.length = argVals.length :=
        calc argTrips.length
          _ = argTrips.unzip.snd.length := by simp [List.unzip_eq_map]
          _ = args.length := by simp [← Heqargs]
          _ = argVals.length := by apply EvalExpressionsLength Hevalargs
      have Houttriplen : outTrips.length = outVals.length :=
        calc outTrips.length
          _ = outTrips.unzip.snd.length := by simp [List.unzip_eq_map]
          _ = lhs.length := by simp [← Heqouts]
          _ = (ListMap.keys proc.header.outputs).length := by simp_all [ListMap.keys.length]
          _ = outVals.length := ReadValuesLength Hrdout
      have Holdtriplen : oldTrips.length = oldVals.length :=
        calc oldTrips.length
          _ = oldTrips.unzip.snd.length := by simp [List.unzip_eq_map]
          _ = oldVals.length := by apply ReadValuesLength HoldVals
      have Hinit := updatedStatesInit ?_ ?_ ?_ (σ:=σ')
          (hs:=argTrips.unzip.fst.unzip.fst ++
              outTrips.unzip.fst.unzip.fst ++
              oldTrips.unzip.fst.unzip.fst)
          (vs:=argVals ++ outVals ++ oldVals)
      rotate_left
      . simp [Hargtriplen, Houttriplen, Holdtriplen]
      . exact Hndefgen
      . exact Hgennd
      . have Heq := EvalStatementsContractEmpty Heval2
        simp only [Heq] at *
        have Hinit' := InitsUpdatesComm Hupdate Hinit
        cases Hinit' with
        | intro σ₁ Hinit' =>
        exists (updatedStates σ'
              (argTrips.unzip.1.unzip.1 ++ outTrips.unzip.1.unzip.1 ++ oldTrips.unzip.1.unzip.1)
              (argVals ++ outVals ++ oldVals))
        apply And.intro
        . exact InitStatesInits Hinit
        . apply EvalStatementsContractApp
          . -- Prove args expression initialization is correct
            apply EvalStatementsContractInits
            . assumption
            . assumption
            . assumption
            . simp [genArgExprIdentsTrip_snd Heqarg]
              apply List.PredDisjoint_Disjoint
                (P:=(BoogieIdent.isTemp ·))
                (Q:=(BoogieIdent.isGlobOrLocl ·))
              . simp at HargTemp
                apply HargTemp
              . apply List.Forall_flatMap.mp
                apply List.Forall_PredImplies Hwfargs
                intros x Hp
                exact WF.WFargProp.glarg Hp
              . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
            . apply List.Sublist.nodup (List.sublist_append_left _ _) ?_
              . exact outTrips.unzip.fst.unzip.fst
              apply List.Sublist.nodup (List.sublist_append_left _ _) ?_
              . exact oldTrips.unzip.fst.unzip.fst
              exact Hgennd
            . simp
              simp [Heqargs]
              assumption
            . -- arg vars generated are not defined
              apply UpdateStatesNotDefMonotone' (σ':=σ') ?_ Hupdate
              simp [Imperative.isNotDefined] at *
              intros v x x' Hin
              apply Hndefgen
              left; exact ⟨x, x', Hin⟩
          -- Reused assumption : lhs and modifies are defined
          have Hdeflm : Imperative.isDefined σ (lhs ++ proc.spec.modifies) := by
                  simp [Imperative.isDefinedOver,
                        Imperative.HasVarsTrans.allVarsTrans,
                        Statement.allVarsTrans,
                        Statement.touchedVarsTrans,
                        Command.definedVarsTrans,
                        Command.definedVars,
                        Command.modifiedVarsTrans,
                        Imperative.HasVarsTrans.modifiedVarsTrans,
                        Procedure.modifiedVarsTrans,
                        lkup] at Hwf
                  simp [Imperative.isDefined] at *
                  intros v Hin
                  apply Hwf
                  cases Hin with
                  | inl a => right; left; exact a
                  | inr a => right; right; left; exact a
          apply EvalStatementsContractApp (σ':=(updatedStates (updatedStates σ
                                            argTrips.unzip.fst.unzip.fst argVals)
                                            outTrips.unzip.fst.unzip.fst outVals))
          . -- Prove output variables initialization is correct
            apply EvalStatementsContractInitVars
            . assumption
            . apply List.Disjoint_Nodup_iff.mp
              refine ⟨?_, ?_, ?_⟩
              . exact (List.nodup_append.mp (List.nodup_append.mp Hgennd).1).2.1
              . simp [genOutExprIdentsTrip_snd Heqout]
                exact Hlhs.1
              . -- Disjoint between localGlob and Temp
                simp [genOutExprIdentsTrip_snd Heqout]
                apply List.PredDisjoint_Disjoint
                  (P:=(BoogieIdent.isTemp ·))
                  (Q:=(BoogieIdent.isLocl ·))
                . simp at HoutTemp
                  exact HoutTemp
                . exact Hlhs.2
                . apply List.PredDisjoint_PredImplies_right
                  exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                  exact BoogieIdent.isLocl_isGlobOrLocl
            . simp
              refine ReadValuesUpdatedStates ?_ ?_ ?_
              . simp [Hargtriplen]
              . apply List.PredDisjoint_Disjoint
                  (P:=(BoogieIdent.isTemp ·))
                  (Q:=(BoogieIdent.isLocl ·))
                . simp at HargTemp
                  exact HargTemp
                . simp [← Heqouts]
                  exact Hlhs.2
                . apply List.PredDisjoint_PredImplies_right
                  exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                  exact BoogieIdent.isLocl_isGlobOrLocl
              . simp [← Heqouts]
                exact Hevalouts
            . -- out vars generated are not defined
              apply UpdatedStatesDisjNotDefMonotone
              . have Hnd' := List.Disjoint_Nodup_iff.mpr (List.nodup_append.mp Hgennd).1
                exact Hnd'.2.2
              . simp [← Hargtriplen]
              . apply UpdateStatesNotDefMonotone' (σ':=σ') ?_ Hupdate
                simp [Imperative.isNotDefined] at *
                intros v x x' Hin
                apply Hndefgen
                right; left; exact ⟨x, x', Hin⟩
          apply EvalStatementsContractApp (σ':=(updatedStates (updatedStates (updatedStates σ
                                            argTrips.unzip.fst.unzip.fst argVals)
                                            outTrips.unzip.fst.unzip.fst outVals)
                                            oldTrips.unzip.fst.unzip.fst oldVals))
          . -- Prove old expressions initialization is correct
            apply EvalStatementsContractInitVars Hwfvars
            . apply List.Disjoint_Nodup_iff.mp
              refine ⟨?_, ?_, ?_⟩
              . exact (List.nodup_append.mp Hgennd).2.1
              . simp [genOldExprIdentsTrip_snd Heqold]
                apply filter_nodup
                apply eraseDups_Nodup
              . apply List.PredDisjoint_Disjoint
                  (P:=(BoogieIdent.isTemp ·))
                  (Q:=(BoogieIdent.isGlob ·))
                . exact HoldTemp
                . simp [genOldExprIdentsTrip_snd Heqold]
                  apply List.Forall_PredImplies
                  . apply List.Forall_filter
                  . exact WFProgGlob Hwfp
                . apply List.PredDisjoint_PredImplies_right
                  exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                  exact BoogieIdent.isGlob_isGlobOrLocl
            . simp
              apply ReadValuesUpdatedStates
              . simp [Houttriplen]
              . apply List.PredDisjoint_Disjoint
                  (P:=(BoogieIdent.isTemp ·))
                  (Q:=(BoogieIdent.isGlob ·))
                . simp at HoutTemp
                  exact HoutTemp
                . simp [genOldExprIdentsTrip_snd Heqold]
                  apply List.Forall_PredImplies
                  . apply List.Forall_filter
                  . exact WFProgGlob Hwfp
                . apply List.PredDisjoint_PredImplies_right
                  exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                  exact BoogieIdent.isGlob_isGlobOrLocl
              apply ReadValuesUpdatedStates
              . simp [Hargtriplen]
              . apply List.PredDisjoint_Disjoint
                  (P:=(BoogieIdent.isTemp ·))
                  (Q:=(BoogieIdent.isGlob ·))
                . simp at HargTemp
                  exact HargTemp
                . simp [genOldExprIdentsTrip_snd Heqold]
                  apply List.Forall_PredImplies
                  . apply List.Forall_filter
                  . exact WFProgGlob Hwfp
                . apply List.PredDisjoint_PredImplies_right
                  exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                  exact BoogieIdent.isGlob_isGlobOrLocl
              . simp at HoldVals
                exact HoldVals
            . -- old vars generated are not defined
              apply UpdatedStatesDisjNotDefMonotone
              . simp only [List.append_assoc] at Hgennd
                exact (List.Disjoint_Nodup_iff.mpr (List.nodup_append.mp Hgennd).2.1).2.2
              . simp [← Houttriplen]
              apply UpdatedStatesDisjNotDefMonotone
              . simp only [nodup_swap'] at Hgennd
                simp only [← List.append_assoc] at Hgennd
                have Hnd' := (List.Disjoint_Nodup_iff.mpr (List.nodup_append.mp Hgennd).1).2.2
                exact List.Disjoint.symm Hnd'
              . simp [← Hargtriplen]
              . apply UpdateStatesNotDefMonotone' (σ:=σ) (σ':=σ') ?_ Hupdate
                intros x Hin
                apply Hndefgen
                simp_all
          -- σA contains inputs as keys, while σ₁ contains the generated keys as keys
          have Hinit2 := InitStatesApp' Hinit'.2.1 (by simp_all) (by simp_all)
          cases Hinit2 with
          | intro σ₁' Hinit2 =>
          have Hinit3 := InitStatesApp' Hinit2.2.1 (by simp_all) (by simp_all)
          cases Hinit3 with
          | intro σ₁'' Hinit3 =>
            -- NOTE: We split the single InitStates into three stages
            -- σ |-- init argVal --> σ₁'' |-- init outVal --> σ₁' |-- init oldVal --> σ₁
            simp [← List.append_assoc]
            apply EvalStatementsContractApp (σ':=
                      (updatedStates (updatedStates (updatedStates (updatedStates σ
                      (List.map (Prod.fst ∘ Prod.fst) argTrips) argVals)
                      (List.map (Prod.fst ∘ Prod.fst) outTrips) outVals)
                      (List.map (Prod.fst ∘ Prod.fst) oldTrips) oldVals)
                      (lhs ++ proc.spec.modifies) modvals))
            . simp [List.append_assoc]
              apply EvalStatementsContractApp
              . -- asserts
                have Hrdin : ReadValues σAO (ListMap.keys proc.header.inputs) argVals := by
                  apply InitStatesReadValuesMonotone (σ:=σA) ?_ Hinitout
                  exact InitStatesReadValues Hinitin
                have Hrdinout : ReadValues σAO
                      (ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs)
                      (argVals ++ outVals) := ReadValuesApp Hrdin Hrdout
                have Hlen : (ListMap.keys proc.header.inputs).length =
                            (createFvars (List.map (Prod.fst ∘ Prod.fst) argTrips)).length := by calc
                            _ = argVals.length := InitStatesLength Hinitin
                            _ = argTrips.length := by simp_all
                            _ = (List.map (Prod.fst ∘ Prod.fst) argTrips).length := by simp_all
                            _ = _ := by rw [createFvarsLength]
                rw [← (List.zip_append Hlen)]
                rw [← createFvarsApp]
                apply createAssertsCorrect (σA:=σAO) Hwfb Hwfvars
                . assumption
                . assumption
                . simp_all
                  rw [createFvarsLength]
                  simp [← Hargtriplen]
                . -- substNodup
                  have Hlen := ReadValuesLength Hrdin
                  simp [Imperative.substNodup]
                  rw [List.map_fst_zip, List.map_snd_zip] <;> simp_all
                  -- TODO: input names of function not overlapping with generated variables
                  -- can come from local/global distinction
                  conv => arg 1; rw [← List.append_assoc]
                  refine List.Disjoint_Nodup_iff.mp ⟨?_, ?_, ?_⟩
                  . exact Hinoutnd
                  . apply List.Disjoint_Nodup_iff.mp ⟨?_, ?_, ?_⟩
                    . exact (List.Disjoint_Nodup_iff.mpr Hgennd).1
                    . exact Hlhs.1
                    . apply List.PredDisjoint_Disjoint
                        (P:=(BoogieIdent.isTemp ·))
                        (Q:=(BoogieIdent.isLocl ·))
                      . exact HargTemp
                      . exact Hlhs.2
                      . apply List.PredDisjoint_PredImplies_right
                        exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                        exact BoogieIdent.isLocl_isGlobOrLocl
                  . apply List.Disjoint.symm
                    apply List.Disjoint_app.mp ⟨?_, ?_⟩
                    . apply List.PredDisjoint_Disjoint
                        (P:=(BoogieIdent.isTemp ·))
                        (Q:=(BoogieIdent.isGlobOrLocl ·))
                      . exact HargTemp
                      . apply List.Forall_append.mpr ⟨?_, ?_⟩
                        . exact List.Forall_PredImplies Hinlc BoogieIdent.isLocl_isGlobOrLocl
                        . exact List.Forall_PredImplies Houtlc BoogieIdent.isLocl_isGlobOrLocl
                      . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                    . intros x Hin1 Hin2
                      apply Hlhsdisj Hin1
                      simp_all
                . -- substDefined
                  intros k1 k2 Hin
                  have Hmem := List.of_mem_zip Hin
                  simp only [List.mem_append] at Hmem
                  apply And.intro
                  . cases Hmem.1 with
                    | inl Hmem =>
                    have Hdef : Imperative.isDefined σAO (ListMap.keys proc.header.inputs) := by
                      apply InitStatesDefMonotone ?_ Hinitout
                      exact InitStatesDefined Hinitin
                    exact Hdef k1 Hmem
                    | inr Hmem =>
                    have Hdef : Imperative.isDefined σAO (ListMap.keys proc.header.outputs) := by
                      exact InitStatesDefined Hinitout
                    exact Hdef k1 Hmem
                  . cases Hmem.2 with
                    | inl Hmem =>
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefined
                      simp_all
                    | inr Hmem =>
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefMonotone <;> try assumption
                . -- precondition correct
                  intros pre Hin; simp_all
                  apply And.intro
                  . simp [updatedStates]
                    rw [← updatedStates'App]
                    rw [← updatedStates'App]
                    rw [← List.zip_append] <;> try simp_all
                    rw [← List.zip_append] <;> try simp_all
                    rw [← updatedStates]
                    apply InvStoresExceptInvStores
                    apply Imperative.invStoresExceptComm
                    apply InvStoresExceptUpdated
                    apply Imperative.invStoresExceptComm
                    apply InvStoresExceptInitStates (σ:=σA) (ks':=ListMap.keys proc.header.outputs)
                    apply InvStoresExceptInitStates (σ:=σ) (ks':=ListMap.keys proc.header.inputs)
                    exact InvStoresExceptEmpty
                    exact Hinitin
                    exact Hinitout
                    simp_all
                    simp_all
                    simp [← List.append_assoc]
                    generalize ListMap.keys proc.header.inputs ++
                               ListMap.keys proc.header.outputs ++
                               List.map (Prod.fst ∘ Prod.fst) argTrips
                               = inoutarg
                    simp [List.append_assoc]
                    simp [List.removeAll_app]
                    rw [List.removeAll_comm]
                    apply List.Disjoint.removeAll
                    apply List.Disjoint.mono_right
                    . exact List.removeAll_Sublist
                    . apply List.PredDisjoint_Disjoint
                        (P:=(BoogieIdent.isTemp ·))
                        (Q:=(BoogieIdent.isGlobOrLocl ·))
                      . apply List.Forall_append.mpr
                        exact ⟨HoutTemp, HoldTemp⟩
                      . have HH := prepostconditions_unwrap Hin
                        cases HH with
                        | intro label HH =>
                        cases HH with
                        | intro attr HH =>
                        have Hwf := (List.Forall_mem_iff.mp wfpre _ HH).glvars
                        simp at Hwf
                        exact Hwf
                      . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                  . have HH := prepostconditions_unwrap Hin
                    cases HH with
                    | intro label HH =>
                    cases HH with
                    | intro attr HH =>
                    apply List.Disjoint_app.mp ⟨?_, ?_⟩
                    . apply List.PredDisjoint_Disjoint
                        (P:=(BoogieIdent.isTemp ·))
                        (Q:=(BoogieIdent.isGlobOrLocl ·))
                      . exact HargTemp
                      . have Hwf := (List.Forall_mem_iff.mp wfpre _ HH).glvars
                        simp at Hwf
                        exact Hwf
                      . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                    . have Hpre := (List.Forall_mem_iff.mp wfpre _ HH)
                      have Hlcl := List.Forall_mem_iff.mp Hpre.lvars
                      have Hgl := List.Forall_mem_iff.mp Hpre.glvars
                      simp at Hlcl Hgl
                      intros x Hin1 Hin2
                      specialize Hgl x Hin2
                      simp [BoogieIdent.isGlobOrLocl] at Hgl
                      cases Hgl with
                      | inl Hg =>
                        -- disjoint of local and global
                        have Hlhs := List.Forall_mem_iff.mp Hlhs.2
                        specialize Hlhs x Hin1
                        exact BoogieIdent.Disjoint_isLocl_isGlob _ Hlhs Hg
                      | inr Hl =>
                        -- disjoint because of WF
                        specialize Hlcl x Hin2 Hl
                        apply Hlhsdisj Hin1
                        simp_all
                . apply createFvarsSubstStores (σ:=σ₁') (σA:=σAO)
                        (ks2:=(ListMap.keys proc.header.inputs) ++ (ListMap.keys proc.header.outputs))
                  . -- length
                    simp_all
                    rw [createFvarsLength]
                    simp [← Hargtriplen]
                  . assumption
                  . -- substDefined
                    intros k1 k2 Hin
                    have Hmem := List.of_mem_zip Hin
                    apply And.intro
                    . simp only [List.mem_append] at Hmem
                      cases Hmem.1 with
                      | inl Hmem =>
                      have Hdef : Imperative.isDefined σ₁' argTrips.unzip.1.unzip.1 := by
                        apply InitStatesDefMonotone ?_ Hinit3.2.2
                        exact InitStatesDefined Hinit3.2.1
                      simp at Hdef
                      exact Hdef k1 Hmem
                      | inr Hmem =>
                      have Hdef : Imperative.isDefined σ₁' lhs := by
                        simp [Hinit2.1]
                        apply updatedStatesDefMonotone
                        intros k Hin
                        apply Hdeflm
                        exact List.mem_append_left proc.spec.modifies Hin
                      exact Hdef _ Hmem
                    . apply ReadValuesIsDefined Hrdinout
                      exact Hmem.2
                  . -- substStores
                    simp_all
                    apply ReadValuesSubstStores ?_ Hrdinout
                    apply ReadValuesApp
                    simp [updatedStates]
                    rw [List.zip_append]
                    rw [updatedStates'App]
                    apply ReadValuesUpdatedStates
                    . simp [Houttriplen]
                    . intros a Hin1 Hin2
                      apply (List.nodup_append.mp Hgennd).2.2 a ?_ a ?_
                      . rfl
                      . simp only at Hin2 ⊢
                        exact Hin2
                      . simp only at Hin1 ⊢
                        exact List.mem_append_left _ Hin1
                    . apply ReadValuesUpdatedStatesSame
                      simp [Hargtriplen]
                      grind
                    . -- length, provable
                      simp [Hargtriplen]
                    . apply ReadValuesUpdatedStates
                      . -- length, provable
                        simp [Hargtriplen, Houttriplen]
                      . apply List.PredDisjoint_Disjoint
                          (P:=(BoogieIdent.isTemp ·))
                          (Q:=(BoogieIdent.isLocl ·))
                        . apply List.Forall_append.mpr ⟨HargTemp, HoutTemp⟩
                        . exact Hlhs.2
                        . apply List.PredDisjoint_PredImplies_right
                          exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                          exact BoogieIdent.isLocl_isGlobOrLocl
                      . exact Hevalouts
                  . exact Hrdinout
                . -- Read Values
                  exact Hrdinout
                . -- substStores
                  apply ReadValuesSubstStores ?_ Hrdinout
                  apply ReadValuesApp
                  simp [updatedStates]
                  apply ReadValuesUpdatedStates
                  . simp [Holdtriplen]
                  . intros a Hin1 Hin2
                    apply (List.nodup_append.mp Hgennd).2.2 a ?_ a ?_
                    . rfl
                    . simp at Hin2 ⊢
                      exact Or.inl Hin2
                    . simp at Hin1 ⊢
                      exact Hin1
                  apply ReadValuesUpdatedStates
                  . simp [Houttriplen]
                  . intros a Hin1 Hin2
                    apply (List.nodup_append.mp (List.nodup_append.mp Hgennd).1).2.2 a ?_ a ?_
                    . rfl
                    . simp at Hin2 ⊢
                      exact Hin2
                    . simp at Hin1 ⊢
                      exact Hin1
                  . apply ReadValuesUpdatedStatesSame
                    simp [Hargtriplen]
                    grind
                  . apply ReadValuesUpdatedStates
                    . simp [Holdtriplen]
                    . apply List.PredDisjoint_Disjoint
                        (P:=(BoogieIdent.isTemp ·))
                        (Q:=(BoogieIdent.isLocl ·))
                      . simp at HoldTemp
                        exact HoldTemp
                      . exact Hlhs.2
                      . apply List.PredDisjoint_PredImplies_right
                        exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                        exact BoogieIdent.isLocl_isGlobOrLocl
                    . apply ReadValuesUpdatedStates
                      . simp [Houttriplen]
                      . apply List.PredDisjoint_Disjoint
                          (P:=(BoogieIdent.isTemp ·))
                          (Q:=(BoogieIdent.isLocl ·))
                        . simp at HoutTemp
                          exact HoutTemp
                        . exact Hlhs.2
                        . apply List.PredDisjoint_PredImplies_right
                          exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                          exact BoogieIdent.isLocl_isGlobOrLocl
                      . apply ReadValuesUpdatedStates
                        . simp [Hargtriplen]
                        . apply List.PredDisjoint_Disjoint
                            (P:=(BoogieIdent.isTemp ·))
                            (Q:=(BoogieIdent.isLocl ·))
                          . simp at HargTemp
                            exact HargTemp
                          . exact Hlhs.2
                          . apply List.PredDisjoint_PredImplies_right
                            exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                            exact BoogieIdent.isLocl_isGlobOrLocl
                        . exact Hevalouts
              . -- Prove havocs correct
                simp [← createHavocsApp]
                apply EvalStatementsContractHavocVars (σ':=
                      (updatedStates (updatedStates (updatedStates (updatedStates σ
                      (List.map (Prod.fst ∘ Prod.fst) argTrips) argVals)
                      (List.map (Prod.fst ∘ Prod.fst) outTrips) outVals)
                      (List.map (Prod.fst ∘ Prod.fst) oldTrips) oldVals)
                      (lhs ++ proc.spec.modifies) modvals))
                . assumption
                . apply updatedStatesDefMonotone
                  apply updatedStatesDefMonotone
                  apply updatedStatesDefMonotone
                  exact Hdeflm
                . apply UpdateStatesHavocVars (modvals:=modvals)
                  refine updatedStatesUpdate ?_ ?_
                  exact UpdateStatesLength Hupdate
                  apply updatedStatesDefMonotone
                  apply updatedStatesDefMonotone
                  apply updatedStatesDefMonotone
                  exact Hdeflm
            . -- Prove assumes correct
              -- transform to the same store
              simp [updatedStates]
              rw [updatedStatesComm]
              rw [updatedStatesComm (kvs':=(lhs ++ proc.spec.modifies).zip modvals)]
              rw [updatedStatesComm (kvs':=(lhs ++ proc.spec.modifies).zip modvals)]
              simp [UpdateStatesUpdated Hupdate, updatedStates]
              rw [List.zip_append] <;> simp_all
              rw [List.zip_append]
              rw [updatedStates'App]
              rw [updatedStates'App]
              rw [← List.zip_append]
              -- combine fvars
              rw [← createFvarsApp]
              . -- createAssumesCorrect
                -- NOTE: σR here should be σR with the temporary old variables
                generalize HσR₁ : (updatedStates (updatedStates σR
                                  (List.map (Prod.fst ∘ Prod.fst) outTrips) outVals))
                                  (List.map (Prod.fst ∘ Prod.fst) oldTrips) oldVals = σR₁
                apply createAssumesCorrect (σ₀':=σ₁) (σA:=σR₁) Hwfb Hwfvars
                . assumption
                . assumption
                . -- length
                  simp_all
                  exact EvalExpressionsLength Hevalargs
                . -- substNoDup
                  simp [Imperative.substNodup]
                  rw [List.map_fst_zip]
                  rw [List.map_snd_zip]
                  . apply List.Disjoint_Nodup_iff.mp
                    refine ⟨Hinoutnd, ?_, ?_⟩
                    . simp [← List.append_assoc] at Hgennd
                      have HH := List.nodup_append.mp Hgennd
                      apply List.Disjoint_Nodup_iff.mp
                      refine ⟨?_, ?_, ?_⟩
                      . exact (List.nodup_append.mp HH.1).1
                      . exact Hlhs.1
                      . apply List.PredDisjoint_Disjoint
                          (P:=(BoogieIdent.isTemp ·))
                          (Q:=(BoogieIdent.isLocl ·))
                        . exact HargTemp
                        . exact Hlhs.2
                        . apply List.PredDisjoint_PredImplies_right
                          exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                          exact BoogieIdent.isLocl_isGlobOrLocl
                    . apply List.Disjoint.symm
                      apply List.Disjoint_app.mp ⟨?_, ?_⟩
                      . apply List.PredDisjoint_Disjoint
                          (P:=(BoogieIdent.isTemp ·))
                          (Q:=(BoogieIdent.isGlobOrLocl ·))
                        . exact HargTemp
                        . apply List.Forall_append.mpr ⟨?_, ?_⟩
                          . exact List.Forall_PredImplies Hinlc BoogieIdent.isLocl_isGlobOrLocl
                          . exact List.Forall_PredImplies Houtlc BoogieIdent.isLocl_isGlobOrLocl
                        . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                      . intros x Hin1 Hin2
                        apply Hlhsdisj Hin1
                        simp_all
                  . simp_all
                    simp [← Hargtriplen, ← Heqargs]
                  . simp_all
                    simp [← Hargtriplen, ← Heqargs]
                . -- substDefined
                  intros k1 k2 Hin
                  have Hmem := List.of_mem_zip Hin
                  simp only [List.mem_append] at Hmem
                  apply And.intro
                  -- inputs and outputs defined in σR
                  . cases Hmem.1 with
                    | inl Hmem =>
                    have Hdef : Imperative.isDefined σR₁ (ListMap.keys proc.header.inputs) := by
                      simp [← HσR₁]
                      apply updatedStatesDefMonotone
                      apply updatedStatesDefMonotone
                      apply HavocVarsDefMonotone ?_ Hhav2
                      apply HavocVarsDefMonotone ?_ Hhav1
                      apply InitStatesDefMonotone ?_ Hinitout
                      exact InitStatesDefined Hinitin
                    exact Hdef k1 Hmem
                    | inr Hmem =>
                    have Hdef : Imperative.isDefined σR₁ (ListMap.keys proc.header.outputs) := by
                      simp [← HσR₁]
                      apply updatedStatesDefMonotone
                      apply updatedStatesDefMonotone
                      apply HavocVarsDefMonotone ?_ Hhav2
                      apply HavocVarsDefMonotone ?_ Hhav1
                      exact InitStatesDefined Hinitout
                    exact Hdef k1 Hmem
                  . cases Hmem.2 with
                    | inl Hmem =>
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefined
                      simp_all
                    | inr Hmem =>
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefMonotone <;> try assumption
                      apply updatedStatesDefMonotone <;> try assumption
                    -- args and outs are defined in σ₁
                . intros substPost HinSubst
                  refine ⟨?_, ?_, ?_⟩
                  . -- store invariant
                    have Hndrd1 : (ListMap.keys proc.header.outputs ++ proc.spec.modifies).Nodup := by
                      refine List.Disjoint_Nodup_iff.mp ⟨Houtnd, Hmodsnd, ?_⟩
                      -- disjoint between local and global
                      apply List.PredDisjoint_Disjoint
                          (P:=(BoogieIdent.isLocl ·))
                          (Q:=(BoogieIdent.isGlob ·))
                      . exact Houtlc
                      . exact Hmodglob
                      . exact BoogieIdent.Disjoint_isLocl_isGlob
                    have Hrd1 := UpdateStatesReadValues Houtnd Hup1
                    have Hrd2 := UpdateStatesReadValues Hmodsnd Hup2
                    have Heq2 := ReadValuesInjective Hrd2 Hrd'.2.2
                    -- start reducing the update operation
                    apply InvStoresExceptInvStores (ks:=
                          (ListMap.keys proc.header.inputs ++
                          ListMap.keys proc.header.outputs ++
                          (List.map (Prod.fst ∘ Prod.fst) argTrips ++
                          List.map Prod.snd outTrips)))
                    . apply Imperative.invStoresExceptComm
                      rw [← HσR₁]
                      apply InvStoresExceptUpdatedSame
                      apply InvStoresExceptUpdatedSame
                      . apply InvStoresExceptUpdatedMem
                        . rw [← Hrd'.1]
                          rw [List.zip_append]
                          rw [updatedStates'App]
                          rw [updatedStatesComm]
                          . apply InvStoresExceptUpdatedMem
                            . simp [UpdateStatesUpdated Hup2]
                              simp [← Heq2]
                              apply InvStoresExceptUpdatedSame
                              . apply Imperative.invStoresExceptComm
                                simp [UpdateStatesUpdated Hup1]
                                simp [InitStatesUpdated Hinitout]
                                simp [InitStatesUpdated Hinitin]
                                apply InvStoresExceptUpdatedMem
                                apply InvStoresExceptUpdatedMem
                                apply InvStoresExceptUpdatedMem
                                apply InvStoresExceptId
                                . simp [Harglen, ← Heqargs, Hargtriplen]
                                . intros x Hin
                                  simp_all
                                . simp [Houtlen]
                                . intros x Hin
                                  simp_all
                                . exact ReadValuesLength Hrd1
                                . intros x Hin
                                  simp_all
                              . exact ReadValuesLength Hrd2
                              . exact Hmodsnd
                            . simp [← Houtlen , Houttriplen]
                              have Hlen := ReadValuesLength Hrd'.2.1
                              simp at Hlen
                              exact Hlen
                            . intros x Hin
                              simp_all
                          . -- lhs disjoint from modifies, from WF
                            rw [List.unzip_zip]
                            rw [List.unzip_zip]
                            simp
                            . exact List.DisjointAppRight' Hlhsdisj
                            . simp [← Heq2]
                              exact ReadValuesLength Hrd2
                            . have Hlen := ReadValuesLength Hrd'.2.1
                              simp_all
                          . simp [← Houtlen , Houttriplen]
                            have Hlen := ReadValuesLength Hrd'.2.1
                            simp at Hlen
                            exact Hlen
                        . simp [Hargtriplen]
                        . intros x Hin
                          simp_all
                          -- NOTE: can also use equivalent proof term:
                          -- exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl Hin)))
                      . simp [Houttriplen]
                      . exact (List.nodup_append.mp (List.nodup_append.mp Hgennd).2.1).1
                      . simp [Holdtriplen]
                      . exact (List.nodup_append.mp (List.nodup_append.mp Hgennd).2.1).2.1
                    . apply List.Disjoint.symm
                      exact List.removeAll_Disjoint
                  . -- TODO : all vars in substPost is a subset of subst ++ fst fst oldTrips
                    have Hin := postconditions_subst_unwrap HinSubst
                    cases Hin with
                    | intro post Hin =>
                    have HH := prepostconditions_unwrap Hin.1
                    cases HH with
                    | intro label HH =>
                    cases HH with
                    | intro attr HH =>
                    have Hpost := (List.Forall_mem_iff.mp wfpost _ HH)
                    have Hlcl := List.Forall_mem_iff.mp Hpost.lvars
                    have Hgl := List.Forall_mem_iff.mp Hpost.glvars
                    simp at Hlcl Hgl
                    intros x Hin1 Hin2
                    have Hdisj : oldTrips.unzip.fst.unzip.fst.Disjoint oldTrips.unzip.snd := by
                      apply List.PredDisjoint_Disjoint
                        (P:=(BoogieIdent.isTemp ·))
                        (Q:=(BoogieIdent.isGlob ·))
                      . simp; exact HoldTemp
                      . simp; exact Holdsndglob
                      . apply List.PredDisjoint_PredImplies_right
                        exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                        exact BoogieIdent.isGlob_isGlobOrLocl
                    have Hsubset := substsOldPostSubset (post:=(OldExpressions.normalizeOldExpr post)) (oldTrips:=oldTrips) Hdisj
                    have Hin : x ∈ (Imperative.HasVarsPure.getVars (P:=Expression) (OldExpressions.normalizeOldExpr post) ++
                                oldTrips.unzip.fst.unzip.fst) := by
                      apply Hsubset
                      simp [Hin.2] at Hin2
                      exact Hin2
                    simp only [List.mem_append] at Hin Hin1
                    cases Hin1 with
                    | inl Hin1 =>
                      cases Hin with
                      | inl Hin =>
                        -- disjoint of global/local with temp
                        have Hin := normalizeOldExprInVars Hin
                        specialize Hgl x Hin
                        apply BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                        . exact List.Forall_mem_iff.mp HargTemp x Hin1
                        . exact Hgl
                      | inr Hin =>
                        -- disjoint among temp
                        simp only [List.unzip_fst, List.map_map] at Hin
                        simp [BoogieIdent.isGlobOrLocl] at Hgl
                        have HH := (List.nodup_append.mp Hgennd).2.2
                        apply HH x Hin1 x
                        apply List.mem_append.mpr
                        apply (Or.inr Hin)
                        rfl
                    | inr Hin1 =>
                    cases Hin with
                    | inl Hin =>
                      have Hin := normalizeOldExprInVars Hin
                      specialize Hgl x Hin
                      -- x is either global or local
                      simp [BoogieIdent.isGlobOrLocl] at Hgl
                      cases Hgl with
                      | inl Hg =>
                        -- x is global
                        have Hlhs := List.Forall_mem_iff.mp Hlhs.2
                        specialize Hlhs x Hin1
                        exact BoogieIdent.Disjoint_isLocl_isGlob _ Hlhs Hg
                      | inr Hl =>
                        -- x is local, use wf
                        specialize Hlcl x Hin Hl
                        apply Hlhsdisj Hin1
                        simp_all
                    | inr Hin =>
                      -- oldTrips disjoint from lhs
                      simp only [List.unzip_fst, List.map_map] at Hin
                      apply BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                      . exact List.Forall_mem_iff.mp HoldTemp x Hin
                      . apply BoogieIdent.isLocl_isGlobOrLocl
                        exact List.Forall_mem_iff.mp Hlhs.2 _ Hin1
                  . -- post condition correct
                    have Hmem := SubstPostsMem HinSubst
                    cases Hmem with
                    | intro post Hin =>
                    specialize Hpost post Hin.1
                    simp [Hin.2]
                    simp [Imperative.WellFormedSemanticEvalBool] at Hwfb
                    apply (Hwfb _ _ _).1.1.mp
                    have Hsubst' :
                      δ σO σR₁ post =
                      δ σ₁ σR₁ (OldExpressions.substsOldExpr (createOldVarsSubst oldTrips) (OldExpressions.normalizeOldExpr post))
                      := by
                        cases Hwf2 with
                        | intro e Hwf2 =>
                        rw [Hwf2.2 (e:=post)]
                        apply substsOldCorrect
                        -- wf
                        . assumption
                        . assumption
                        . assumption
                        -- wfTwoState, should be provable by setting inits to the oldVars created
                        . simp [WellFormedBoogieEvalTwoState]
                          refine ⟨?_, ?_, Hwf2.2⟩
                          . -- split into havoc and init, by setting inits to the oldVars created
                            simp [← HσR₁]
                            refine ⟨proc.spec.modifies,
                                    (List.map (Prod.fst ∘ Prod.fst) outTrips) ++
                                    (List.map (Prod.fst ∘ Prod.fst) oldTrips), σR, ?_, ?_⟩
                            . exact Hhav2
                            . simp [updatedStates]
                              rw [← updatedStates'App]
                              rw [← List.zip_append]
                              rw [← updatedStates]
                              apply InitStatesInitVars
                              refine updatedStatesInit ?_ ?_ ?_
                              . simp [Houttriplen, Holdtriplen]
                              . -- not defined
                                apply UpdateStatesNotDefMonotone _ Hup2
                                apply UpdateStatesNotDefMonotone _ Hup1
                                simp [InitStatesUpdated Hinitout]
                                apply UpdatedStatesDisjNotDefMonotone
                                . -- Disjoint between local and temp
                                  apply List.Disjoint.symm
                                  apply List.PredDisjoint_Disjoint
                                    (P:=(BoogieIdent.isTemp ·))
                                    (Q:=(BoogieIdent.isGlobOrLocl ·))
                                  . exact List.Forall_append.mpr ⟨HoutTemp, HoldTemp⟩
                                  . exact List.Forall_PredImplies Houtlc BoogieIdent.isLocl_isGlobOrLocl
                                  . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                                . simp [Houtlen]
                                . simp [InitStatesUpdated Hinitin]
                                  apply UpdatedStatesDisjNotDefMonotone
                                  . -- Disjoint between local and temp
                                    apply List.Disjoint.symm
                                    apply List.PredDisjoint_Disjoint
                                      (P:=(BoogieIdent.isTemp ·))
                                      (Q:=(BoogieIdent.isGlobOrLocl ·))
                                    . exact List.Forall_append.mpr ⟨HoutTemp, HoldTemp⟩
                                    . exact List.Forall_PredImplies Hinlc BoogieIdent.isLocl_isGlobOrLocl
                                    . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                                  . simp [← Hargtriplen, Harglen, ← Heqargs]
                                  . have Hndef := (Imperative.isNotDefinedApp' Hndefgen).2
                                    exact UpdateStatesNotDefMonotone' Hndef Hupdate
                              . exact (List.nodup_append.mp Hgennd).2.1
                              . simp [Houttriplen]
                          . intros vs vs' σ₀ σ₁ σ Hhav Hinit
                            have HH := Hwf2.1 vs vs' σ₀ σ₁ σ ⟨Hhav,Hinit⟩
                            apply HH
                        -- normalized
                        . apply OldExpressions.normalizeOldExprSound
                          have HH := prepostconditions_unwrap Hin.1
                          cases HH with
                          | intro label HH =>
                          cases HH with
                          | intro attr HH =>
                          have Hwfpost := (List.Forall_mem_iff.mp wfpost _ HH).oldexprs
                          simp at Hwfpost
                          exact Hwfpost
                        . rw [createOldStoreSubstEq]
                          have Hhav := HavocVarsUpdateStates Hhav1
                          cases Hhav with
                          | intro modvals Hhav =>
                          apply ReadValuesSubstStores
                          apply UpdateStatesReadValuesMonotone (σ:=σAO) (vs:=oldVals) _ ?_ Hhav
                          . -- Nodup
                            apply List.Disjoint_Nodup_iff.mp
                            refine ⟨?_, ?_, ?_⟩
                            . have Heq := genOldExprIdentsTrip_snd Heqold
                              simp [Heq]
                              apply filter_nodup
                              apply eraseDups_Nodup
                            . exact Houtnd
                            . -- Disjoint between local and temp
                              apply List.Disjoint.symm
                              apply List.PredDisjoint_Disjoint
                                  (P:=(BoogieIdent.isLocl ·))
                                  (Q:=(BoogieIdent.isGlob ·))
                              . exact Houtlc
                              . simp [genOldExprIdentsTrip_snd Heqold]
                                apply List.Forall_PredImplies
                                . apply List.Forall_filter
                                . exact WFProgGlob Hwfp
                              . exact BoogieIdent.Disjoint_isLocl_isGlob
                          . apply InitStatesReadValuesMonotone (σ:=σA) ?_ Hinitout
                            . apply InitStatesReadValuesMonotone (σ:=σ) ?_ Hinitin
                              simp only [List.unzip_snd]
                              exact HoldVals
                          . simp [← HσR₁]
                            apply ReadValuesUpdatedStatesSame
                            simp [Holdtriplen]
                            exact (List.nodup_append.mp (List.nodup_append.mp Hgennd).2.1).2.1
                        . rw [createOldStoreSubstEq]
                          intros k1 k2 Hin
                          have Hmem := List.of_mem_zip Hin
                          apply And.intro
                          . have Hdef : Imperative.isDefined σO (oldTrips.unzip.snd) := by
                              apply HavocVarsDefMonotone ?_ Hhav1
                              apply InitStatesDefMonotone ?_ Hinitout
                              apply InitStatesDefMonotone ?_ Hinitin
                              simp only [List.unzip_snd]
                              exact HoldDef
                            exact Hdef k1 Hmem.1
                          . have Hdef : Imperative.isDefined σR₁ oldTrips.unzip.fst.unzip.fst := by
                              simp [← HσR₁]
                              apply updatedStatesDefined
                              simp [Holdtriplen]
                            exact Hdef k2 Hmem.2
                        . rw [createOldStoreSubstEq]
                          simp [Imperative.substNodup]
                          simp [← List.unzip_fst, ← List.unzip_snd]
                          rw [List.unzip_zip]
                          simp
                          apply List.Disjoint_Nodup_iff.mp
                          . refine ⟨?_, ?_, ?_⟩
                            . -- oldTrips.unzip.2 Nodup. needs some equivalence
                              have Heq := genOldExprIdentsTrip_snd Heqold
                              simp only [Heq]
                              apply filter_nodup
                              apply eraseDups_Nodup
                            . exact (List.nodup_append.mp (List.nodup_append.mp Hgennd).2.1).2.1
                            . apply List.Disjoint.symm
                              apply List.PredDisjoint_Disjoint
                                  (P:=(BoogieIdent.isTemp ·))
                                  (Q:=(BoogieIdent.isGlob ·))
                              . exact HoldTemp
                              . simp [genOldExprIdentsTrip_snd Heqold]
                                apply List.Forall_PredImplies
                                . apply List.Forall_filter
                                . exact WFProgGlob Hwfp
                              . apply List.PredDisjoint_PredImplies_right
                                exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                                exact BoogieIdent.isGlob_isGlobOrLocl
                          . simp [Holdtriplen]
                        . apply List.Disjoint_Subset (ks:=(Imperative.HasVarsPure.getVars post))
                          . apply List.PredDisjoint_Disjoint
                                (P:=(BoogieIdent.isTemp ·))
                                (Q:=(BoogieIdent.isGlobOrLocl ·))
                            . simp
                              exact HoldTemp
                            . have HH := prepostconditions_unwrap Hin.1
                              cases HH with
                              | intro label HH =>
                              cases HH with
                              | intro attr HH =>
                              have Hwf := (List.Forall_mem_iff.mp wfpost _ HH).glvars
                              simp at Hwf
                              exact Hwf
                            . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                          . refine extractedOldVarsInVars ?_
                            have HH := prepostconditions_unwrap Hin.1
                            cases HH with
                            | intro label HH =>
                            cases HH with
                            | intro attr HH =>
                            have Hwf := (List.Forall_mem_iff.mp wfpost _ HH).oldexprs
                            simp at Hwf
                            exact Hwf
                    rw [← Hsubst']
                    simp [← HσR₁]
                    apply EvalExpressionUpdatedStates <;> try assumption
                    . simp [Holdtriplen]
                    . exact (List.nodup_append.mp (List.nodup_append.mp Hgennd).2.1).2.1
                    . apply List.PredDisjoint_Disjoint
                          (P:=(BoogieIdent.isTemp ·))
                          (Q:=(BoogieIdent.isGlobOrLocl ·))
                      . exact HoldTemp
                      . have HH := prepostconditions_unwrap Hin.1
                        cases HH with
                        | intro label HH =>
                        cases HH with
                        | intro attr HH =>
                        have Hwf := (List.Forall_mem_iff.mp wfpost _ HH).glvars
                        simp at Hwf
                        exact Hwf
                      . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                    apply EvalExpressionUpdatedStates <;> try assumption
                    . simp [Houttriplen]
                    . exact (List.nodup_append.mp (List.nodup_append.mp Hgennd).2.1).1
                    . apply List.PredDisjoint_Disjoint
                          (P:=(BoogieIdent.isTemp ·))
                          (Q:=(BoogieIdent.isGlobOrLocl ·))
                      . exact HoutTemp
                      . have HH := prepostconditions_unwrap Hin.1
                        cases HH with
                        | intro label HH =>
                        cases HH with
                        | intro attr HH =>
                        have Hwf := (List.Forall_mem_iff.mp wfpost _ HH).glvars
                        simp at Hwf
                        exact Hwf
                      . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                    apply (Hwfb _ _ _).1.1.mpr
                    exact Hpost.2
                . -- substStores, provable
                  apply ReadValuesSubstStores (vs:=argVals ++ v1)
                  . apply ReadValuesApp
                    . simp [← HσR₁]
                      apply InitStatesReadValuesMonotone (σ:=σR)
                      . -- read values
                        apply UpdateStatesReadValuesMonotone (σ:=σO) _ ?_ Hup2
                        . -- nodup between inputs and modifies
                          apply List.Disjoint_Nodup_iff.mp
                          refine ⟨?_, ?_, ?_⟩
                          . exact Hinnd
                          . exact Hmodsnd
                          . -- Disjoint between local and temp
                            apply List.PredDisjoint_Disjoint
                                (P:=(BoogieIdent.isLocl ·))
                                (Q:=(BoogieIdent.isGlob ·))
                            . exact Hinlc
                            . exact Hmodglob
                            . exact BoogieIdent.Disjoint_isLocl_isGlob
                        . apply UpdateStatesReadValuesMonotone (σ:=σAO) _ ?_ Hup1
                          . exact Hinoutnd
                          . apply InitStatesReadValuesMonotone (σ:=σA) _ Hinitout
                            . apply InitStatesReadValues (σ:=σ) Hinitin
                      . simp [updatedStates]
                        rw [← updatedStates'App]
                        rw [← List.zip_append]
                        rw [← updatedStates]
                        apply updatedStatesInit
                        . simp [Holdtriplen, Houttriplen]
                        . -- not defined
                          apply UpdateStatesNotDefMonotone _ Hup2
                          apply UpdateStatesNotDefMonotone _ Hup1
                          simp [InitStatesUpdated Hinitout]
                          apply UpdatedStatesDisjNotDefMonotone
                          . -- Disjoint between local and temp
                            apply List.Disjoint.symm
                            apply List.PredDisjoint_Disjoint
                              (P:=(BoogieIdent.isTemp ·))
                              (Q:=(BoogieIdent.isGlobOrLocl ·))
                            . exact List.Forall_append.mpr ⟨HoutTemp, HoldTemp⟩
                            . refine List.Forall_PredImplies Houtlc BoogieIdent.isLocl_isGlobOrLocl
                            . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                          . simp [Houtlen]
                          . simp [InitStatesUpdated Hinitin]
                            apply UpdatedStatesDisjNotDefMonotone
                            . -- Disjoint between local and temp
                              apply List.Disjoint.symm
                              apply List.PredDisjoint_Disjoint
                                (P:=(BoogieIdent.isTemp ·))
                                (Q:=(BoogieIdent.isGlobOrLocl ·))
                              . exact List.Forall_append.mpr ⟨HoutTemp, HoldTemp⟩
                              . refine List.Forall_PredImplies Hinlc BoogieIdent.isLocl_isGlobOrLocl
                              . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                            . simp [← Hargtriplen, Harglen, ← Heqargs]
                            . have Hndef := (Imperative.isNotDefinedApp' Hndefgen).2
                              exact UpdateStatesNotDefMonotone' Hndef Hupdate
                        . exact (List.nodup_append.mp Hgennd).2.1
                        . simp [Houttriplen]
                    . simp [← HσR₁]
                      apply ReadValuesUpdatedStates
                      . simp [Holdtriplen]
                      . -- Disjoint between local and temp
                        apply List.PredDisjoint_Disjoint
                          (P:=(BoogieIdent.isTemp ·))
                          (Q:=(BoogieIdent.isGlobOrLocl ·))
                        . exact HoldTemp
                        . refine List.Forall_PredImplies Houtlc BoogieIdent.isLocl_isGlobOrLocl
                        . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                      . apply ReadValuesUpdatedStates
                        . simp [Houttriplen]
                        . -- Disjoint between local and temp
                          apply List.PredDisjoint_Disjoint
                            (P:=(BoogieIdent.isTemp ·))
                            (Q:=(BoogieIdent.isGlobOrLocl ·))
                          . exact HoutTemp
                          . refine List.Forall_PredImplies Houtlc BoogieIdent.isLocl_isGlobOrLocl
                          . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                        . exact Hrd'.2.1
                  . apply ReadValuesApp
                    . apply ReadValuesUpdatedStates
                      . simp [Holdtriplen]
                      . simp only [nodup_swap'] at Hgennd
                        simp only [List.append_assoc] at Hgennd
                        exact (List.Disjoint_Nodup_iff.mpr (List.nodup_append.mp Hgennd).2.1).2.2
                      . apply ReadValuesUpdatedStates
                        . simp [Houttriplen]
                        . simp only [← List.append_assoc] at Hgennd
                          exact List.Disjoint.symm (List.Disjoint_Nodup_iff.mpr (List.nodup_append.mp Hgennd).1).2.2
                        . apply ReadValuesUpdatedStatesSame
                          . simp [Hargtriplen]
                          . exact (List.nodup_append.mp Hgennd).1
                    . simp [← Hrd'.1]
                      rw [List.zip_append, updatedStates'App]
                      . apply ReadValuesUpdatedStates
                        . simp [Holdtriplen]
                        . -- Disjoint between local and temp
                          apply List.PredDisjoint_Disjoint
                            (P:=(BoogieIdent.isTemp ·))
                            (Q:=(BoogieIdent.isLocl ·))
                          . exact HoldTemp
                          . exact Hlhs.2
                          . apply List.PredDisjoint_PredImplies_right
                            exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                            exact BoogieIdent.isLocl_isGlobOrLocl
                        . apply ReadValuesUpdatedStates
                          . simp [Houttriplen]
                          . -- Disjoint between local and temp
                            apply List.PredDisjoint_Disjoint
                              (P:=(BoogieIdent.isTemp ·))
                              (Q:=(BoogieIdent.isLocl ·))
                            . exact HoutTemp
                            . exact Hlhs.2
                            . apply List.PredDisjoint_PredImplies_right
                              exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                              exact BoogieIdent.isLocl_isGlobOrLocl
                          . apply ReadValuesUpdatedStates
                            . simp [Hargtriplen]
                            . -- Disjoint between local and temp
                              apply List.PredDisjoint_Disjoint
                                (P:=(BoogieIdent.isTemp ·))
                                (Q:=(BoogieIdent.isLocl ·))
                              . exact HargTemp
                              . exact Hlhs.2
                              . apply List.PredDisjoint_PredImplies_right
                                exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                                exact BoogieIdent.isLocl_isGlobOrLocl
                            . apply ReadValuesUpdatedStates
                              . exact ReadValuesLength Hrd'.2.2
                              . intros x Hin1 Hin2
                                apply Hlhsdisj Hin2
                                simp_all
                              . apply ReadValuesUpdatedStatesSame
                                . simp [Houttriplen, ← Houtlen]
                                  have HH := ReadValuesLength Hrd'.2.1
                                  simp at HH
                                  exact HH
                                . exact Hlhs.1
                      . simp [Houttriplen, ← Houtlen]
                        have HH := ReadValuesLength Hrd'.2.1
                        simp at HH
                        exact HH
              . -- length of input and argTrips
                simp [createFvars]
                have Heq := InitStatesLength Hinitin
                simp_all
              . -- length of output and outVals
                simp_all
              . simp
                have Hlen := UpdateStatesLength Hupdate
                rw [List.map_fst_zip]
                rw [List.map_fst_zip]
                . -- Disjoint between old labels and lhs, modified, and modvals
                  apply List.PredDisjoint_Disjoint
                    (P:=(BoogieIdent.isTemp ·))
                    (Q:=(BoogieIdent.isGlobOrLocl ·))
                  . simp at HargTemp
                    exact HargTemp
                  . apply List.Forall_append.mpr ⟨?_, ?_⟩
                    . exact List.Forall_PredImplies Hlhs.2 BoogieIdent.isLocl_isGlobOrLocl
                    . exact List.Forall_PredImplies Hmodglob BoogieIdent.isGlob_isGlobOrLocl
                  . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                . simp_all
                . simp_all
              . -- Disjoint between old labels and lhs, modified, and modvals
                simp
                rw [List.map_fst_zip]
                rw [List.map_fst_zip (l₂:=modvals)]
                apply List.PredDisjoint_Disjoint
                  (P:=(BoogieIdent.isTemp ·))
                  (Q:=(BoogieIdent.isGlobOrLocl ·))
                . simp at HoutTemp
                  exact HoutTemp
                . apply List.Forall_append.mpr ⟨?_, ?_⟩
                  . exact List.Forall_PredImplies Hlhs.2 BoogieIdent.isLocl_isGlobOrLocl
                  . exact List.Forall_PredImplies Hmodglob BoogieIdent.isGlob_isGlobOrLocl
                . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                . have Hlen := UpdateStatesLength Hupdate
                  omega
                . simp_all
              . -- Disjoint between generated out labels and lhs ++ modifies
                simp
                rw [List.map_fst_zip]
                rw [List.map_fst_zip (l₂:=modvals)]
                apply List.PredDisjoint_Disjoint
                  (P:=(BoogieIdent.isTemp ·))
                  (Q:=(BoogieIdent.isGlobOrLocl ·))
                . simp at HoldTemp
                  exact HoldTemp
                . apply List.Forall_append.mpr ⟨?_, ?_⟩
                  . exact List.Forall_PredImplies Hlhs.2 BoogieIdent.isLocl_isGlobOrLocl
                  . exact List.Forall_PredImplies Hmodglob BoogieIdent.isGlob_isGlobOrLocl
                . exact BoogieIdent.Disjoint_isTemp_isGlobOrLocl
                . have Hlen := UpdateStatesLength Hupdate
                  omega
                . simp_all

end CallElimCorrect
