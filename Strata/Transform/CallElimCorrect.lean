/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Init.Data.List.Basic
import Init.Data.List.Lemmas
public import Strata.Languages.Core.Env
public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.ProgramType
public import Strata.Languages.Core.WF
public import Strata.DL.Lambda.Lambda
public import Strata.Transform.CoreTransform
public import Strata.Transform.CallElim
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.StatementSemanticsProps
public import Strata.Transform.SubstSemantics
import Strata.Transform.CoreTransformSemantics
import Strata.DL.Util.ListUtils
public import Strata.DL.Util.String

/-! # Call Elimination Correctness Proof

  This file contains the main proof that the call elimination transformation is
  semantics preserving (see `callElimStatementCorrect`), formulated against the
  small-step `Stmt` semantics in `Strata.Languages.Core.StatementSemanticsProps`.
-/

namespace CallElimCorrect
open Core Core.Transform CallElim

public section

-- inidividual lemmas

private theorem createHavocsApp :
createHavocs (a ++ b) md = createHavocs a md ++ createHavocs b md := by
simp [createHavocs]

private theorem createFvarsApp :
createFvars (a ++ b) = createFvars a ++ createFvars b := by
simp [createFvars]

private theorem createFvarsLength :
(createFvars ls).length = ls.length := by
induction ls <;> simp [createFvars]


/-! ## Helper block-evaluator lemmas (small-step)

  The block-evaluator family (`singleCmdToStmts`, `H_havocs`, `H_init`,
  `H_initVars`, `H_inits`, `evalExpression_updatedState`,
  `evalExpressions_updatedState`, `readValues_updatedState`) has been
  migrated to `Strata.Languages.Core.CoreTransformSemantics`.  They are
  re-exported under the `Core` namespace via the import above. -/

-- The bridge `WellFormedCoreEvalTwoState_old_havoc` is inlined at the
-- L6 spike (line ~5326); see git history for the blocked-helper rationale.


/-! ### Pure list-shape analogues of `createAsserts` / `createAssumes`.

    The monadic `Core.Transform.createAsserts` / `createAssumes` use a fresh
    label generator. For the small-step proof we need a pure-list version that
    we can induct over directly. -/

/-- Pure-list analogue of `Core.Transform.createAsserts` (without the
    monadic label generator). Produces `Statement.assert` statements,
    one per entry, with substituted predicates. -/
private def createAsserts_list
    (entries : List (CoreLabel × Procedure.Check))
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String) :
    List Statement :=
  entries.mapIdx (fun i (l, check) =>
    Statement.assert s!"{labelPrefix}{i}_{l}"
                     (Lambda.LExpr.substFvars check.expr subst)
                     (check.md.setCallSiteFileRange md))

/-- Pure-list analogue of `Core.Transform.createAssumes`. -/
private def createAssumes_list
    (entries : List (CoreLabel × Procedure.Check))
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String) :
    List Statement :=
  entries.mapIdx (fun i (l, check) =>
    Statement.assume s!"{labelPrefix}{i}_{l}"
                     (Lambda.LExpr.substFvars check.expr subst)
                     (check.md.setCallSiteFileRange md))

/-! ### Small-step block helpers for assert/assume sequences -/

/-- A list of `Statement.assert` with substituted predicates evaluates from
    σ' to σ' (store unchanged) under contract semantics, given that each
    substituted predicate evaluates to `tt` in σ' and the substitution
    well-formedness assumptions hold. -/
private theorem H_asserts
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {pres : List (CoreLabel × Procedure.Check)}
    {md : Imperative.MetaData Expression}
    {labelPrefix : String}
    (Hwfb  : Imperative.WellFormedSemanticEvalBool δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σ' σA (ks'.zip ks))
    (Hpres : ∀ entry, entry ∈ pres →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      (createAsserts_list pres (ks.zip (Core.Transform.createFvars ks')) md labelPrefix)
      ⟨σ', δ, false⟩ := by
  -- Generalize over the starting index of mapIdx so we can induct on the list.
  suffices Hgen :
      ∀ (i : Nat) (l : List (CoreLabel × Procedure.Check)),
        (∀ entry, entry ∈ l →
           Imperative.invStores σA σ'
             ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
                (ks ++ ks')) ∧
           ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
           δ σA entry.snd.expr = some Imperative.HasBool.tt) →
        EvalStatementsContract π φ ⟨σ', δ, false⟩
          (l.mapIdx (fun j (lbl, check) =>
            Statement.assert s!"{labelPrefix}{i + j}_{lbl}"
              (Lambda.LExpr.substFvars check.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (check.md.setCallSiteFileRange md)))
          ⟨σ', δ, false⟩ by
    have := Hgen 0 pres Hpres
    simp [createAsserts_list] at this ⊢
    exact this
  intros i l Hl
  induction l generalizing i with
  | nil =>
    simp [List.mapIdx]
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons head tail ih =>
    obtain ⟨lbl, check⟩ := head
    -- Apply IH at index i+1.
    have HtailHyp :
        ∀ entry, entry ∈ tail →
          Imperative.invStores σA σ'
            ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
              (ks ++ ks')) ∧
          ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
          δ σA entry.snd.expr = some Imperative.HasBool.tt := by
      intros entry hin; exact Hl entry (List.mem_cons_of_mem _ hin)
    have Htail := ih (i + 1) HtailHyp
    -- Use Hl on the head entry to evaluate the substituted predicate.
    have HlHead := Hl (lbl, check) List.mem_cons_self
    obtain ⟨HinvHead, HnininHead, HevHead⟩ := HlHead
    -- Apply subst_fvars_correct to relate δ σA expr to δ σ' (substFvars expr ...)
    have Hsubst' : Imperative.substStores σA σ' (ks.zip ks') := by
      apply Imperative.substStoresFlip'
      simp [Imperative.substSwap, zip_swap]
      exact Hsubst
    have Heq : δ σA check.expr =
                δ σ' (Lambda.LExpr.substFvars check.expr
                        (ks.zip (Core.Transform.createFvars ks'))) :=
      subst_fvars_correct Hwfc Hwfvr Hwfvl Hlen Hdef Hnd Hsubst' HnininHead HinvHead
    have HevSubst : δ σ' (Lambda.LExpr.substFvars check.expr
                          (ks.zip (Core.Transform.createFvars ks'))) =
                    some Imperative.HasBool.tt := by
      rw [← Heq]; exact HevHead
    -- Build the assert command derivation
    have Hassert :
        Core.EvalCommandContract π δ σ'
          (Core.CmdExt.cmd
            (Imperative.Cmd.assert
              s!"{labelPrefix}{i}_{lbl}"
              (Lambda.LExpr.substFvars check.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (check.md.setCallSiteFileRange md)))
          σ' false :=
      Core.EvalCommandContract.cmd_sem (Imperative.EvalCmd.eval_assert_pass HevSubst Hwfb)
    have HheadStmts := singleCmdToStmts (π := π) (φ := φ) Hassert
    -- Combined head ++ tail trace.
    have Hcombined :
        EvalStatementsContract π φ ⟨σ', δ, false⟩
          ([Statement.assert s!"{labelPrefix}{i}_{lbl}"
              (Lambda.LExpr.substFvars check.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (check.md.setCallSiteFileRange md)] ++
           tail.mapIdx (fun j p =>
              Statement.assert s!"{labelPrefix}{i + 1 + j}_{p.fst}"
                (Lambda.LExpr.substFvars p.snd.expr
                  (ks.zip (Core.Transform.createFvars ks')))
                (p.snd.md.setCallSiteFileRange md)))
          ⟨σ', δ, false⟩ := EvalStatementsContractApp HheadStmts Htail
    -- Massage to match the goal shape produced by mapIdx on cons.
    have Hgoal_eq :
        ((lbl, check) :: tail).mapIdx (fun j p =>
            Statement.assert s!"{labelPrefix}{i + j}_{p.fst}"
              (Lambda.LExpr.substFvars p.snd.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (p.snd.md.setCallSiteFileRange md)) =
        [Statement.assert s!"{labelPrefix}{i}_{lbl}"
            (Lambda.LExpr.substFvars check.expr
              (ks.zip (Core.Transform.createFvars ks')))
            (check.md.setCallSiteFileRange md)] ++
        tail.mapIdx (fun j p =>
            Statement.assert s!"{labelPrefix}{i + 1 + j}_{p.fst}"
              (Lambda.LExpr.substFvars p.snd.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (p.snd.md.setCallSiteFileRange md)) := by
      rw [List.mapIdx_cons]
      simp only [List.singleton_append, List.cons.injEq, Nat.add_zero, true_and]
      -- Goal: tail.mapIdx (fun j ... i + (j+1) ...) = tail.mapIdx (fun j ... i + 1 + j ...)
      apply List.mapIdx_eq_iff.mpr
      intros k
      simp [List.getElem?_mapIdx]
      cases hh : tail[k]? with
      | none => rfl
      | some p =>
        have : i + 1 + k = i + (k + 1) := by omega
        rw [this]
    show EvalStatementsContract π φ ⟨σ', δ, false⟩
      (((lbl, check) :: tail).mapIdx (fun j p =>
        Statement.assert s!"{labelPrefix}{i + j}_{p.fst}"
          (Lambda.LExpr.substFvars p.snd.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (p.snd.md.setCallSiteFileRange md))) ⟨σ', δ, false⟩
    rw [Hgoal_eq]
    exact Hcombined

/-- Symmetric to `H_asserts`: a list of `Statement.assume` with substituted
    predicates evaluates from σ' to σ'. -/
private theorem H_assumes
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {posts : List (CoreLabel × Procedure.Check)}
    {md : Imperative.MetaData Expression}
    {labelPrefix : String}
    (Hwfb  : Imperative.WellFormedSemanticEvalBool δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σA σ' (ks.zip ks'))
    (Hposts : ∀ entry, entry ∈ posts →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      (createAssumes_list posts (ks.zip (Core.Transform.createFvars ks')) md labelPrefix)
      ⟨σ', δ, false⟩ := by
  suffices Hgen :
      ∀ (i : Nat) (l : List (CoreLabel × Procedure.Check)),
        (∀ entry, entry ∈ l →
           Imperative.invStores σA σ'
             ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
                (ks ++ ks')) ∧
           ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
           δ σA entry.snd.expr = some Imperative.HasBool.tt) →
        EvalStatementsContract π φ ⟨σ', δ, false⟩
          (l.mapIdx (fun j (lbl, check) =>
            Statement.assume s!"{labelPrefix}{i + j}_{lbl}"
              (Lambda.LExpr.substFvars check.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (check.md.setCallSiteFileRange md)))
          ⟨σ', δ, false⟩ by
    have := Hgen 0 posts Hposts
    simp [createAssumes_list] at this ⊢
    exact this
  intros i l Hl
  induction l generalizing i with
  | nil =>
    simp [List.mapIdx]
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons head tail ih =>
    obtain ⟨lbl, check⟩ := head
    have HtailHyp :
        ∀ entry, entry ∈ tail →
          Imperative.invStores σA σ'
            ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
              (ks ++ ks')) ∧
          ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
          δ σA entry.snd.expr = some Imperative.HasBool.tt := by
      intros entry hin; exact Hl entry (List.mem_cons_of_mem _ hin)
    have Htail := ih (i + 1) HtailHyp
    have HlHead := Hl (lbl, check) List.mem_cons_self
    obtain ⟨HinvHead, HnininHead, HevHead⟩ := HlHead
    have Heq : δ σA check.expr =
                δ σ' (Lambda.LExpr.substFvars check.expr
                        (ks.zip (Core.Transform.createFvars ks'))) :=
      subst_fvars_correct Hwfc Hwfvr Hwfvl Hlen Hdef Hnd Hsubst HnininHead HinvHead
    have HevSubst : δ σ' (Lambda.LExpr.substFvars check.expr
                          (ks.zip (Core.Transform.createFvars ks'))) =
                    some Imperative.HasBool.tt := by
      rw [← Heq]; exact HevHead
    have Hassume :
        Core.EvalCommandContract π δ σ'
          (Core.CmdExt.cmd
            (Imperative.Cmd.assume
              s!"{labelPrefix}{i}_{lbl}"
              (Lambda.LExpr.substFvars check.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (check.md.setCallSiteFileRange md)))
          σ' false :=
      Core.EvalCommandContract.cmd_sem (Imperative.EvalCmd.eval_assume HevSubst Hwfb)
    have HheadStmts := singleCmdToStmts (π := π) (φ := φ) Hassume
    -- Combined chain. mapIdx_cons unfolds head with index 0, then tail with j+1
    have Hcombined :
        EvalStatementsContract π φ ⟨σ', δ, false⟩
          ([Statement.assume s!"{labelPrefix}{i}_{lbl}"
              (Lambda.LExpr.substFvars check.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (check.md.setCallSiteFileRange md)] ++
           tail.mapIdx (fun j p =>
              Statement.assume s!"{labelPrefix}{i + 1 + j}_{p.fst}"
                (Lambda.LExpr.substFvars p.snd.expr
                  (ks.zip (Core.Transform.createFvars ks')))
                (p.snd.md.setCallSiteFileRange md)))
          ⟨σ', δ, false⟩ := EvalStatementsContractApp HheadStmts Htail
    -- Massage to match the goal shape produced by mapIdx on cons.
    have Hgoal_eq :
        ((lbl, check) :: tail).mapIdx (fun j p =>
            Statement.assume s!"{labelPrefix}{i + j}_{p.fst}"
              (Lambda.LExpr.substFvars p.snd.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (p.snd.md.setCallSiteFileRange md)) =
        [Statement.assume s!"{labelPrefix}{i}_{lbl}"
            (Lambda.LExpr.substFvars check.expr
              (ks.zip (Core.Transform.createFvars ks')))
            (check.md.setCallSiteFileRange md)] ++
        tail.mapIdx (fun j p =>
            Statement.assume s!"{labelPrefix}{i + 1 + j}_{p.fst}"
              (Lambda.LExpr.substFvars p.snd.expr
                (ks.zip (Core.Transform.createFvars ks')))
              (p.snd.md.setCallSiteFileRange md)) := by
      rw [List.mapIdx_cons]
      simp only [List.singleton_append, List.cons.injEq, Nat.add_zero, true_and]
      apply List.mapIdx_eq_iff.mpr
      intros k
      simp [List.getElem?_mapIdx]
      cases hh : tail[k]? with
      | none => rfl
      | some p =>
        have : i + 1 + k = i + (k + 1) := by omega
        rw [this]
    show EvalStatementsContract π φ ⟨σ', δ, false⟩
      (((lbl, check) :: tail).mapIdx (fun j p =>
        Statement.assume s!"{labelPrefix}{i + j}_{p.fst}"
          (Lambda.LExpr.substFvars p.snd.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (p.snd.md.setCallSiteFileRange md))) ⟨σ', δ, false⟩
    rw [Hgoal_eq]
    exact Hcombined

/-- Labels-aware variant of `H_asserts`: takes a separate `labels`
    list (paired positionally with `pres` via `zip`) rather than a
    `labelOf` projection.  This matches the shape exposed by the
    `HassertsShape` clause of `callElimCmd_call_eq` (B3 layer), which
    forms the asserts list as `(pres.zip labels).map (fun (entry, lbl) => …)`. -/
private theorem H_asserts_zip
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {pres : List (CoreLabel × Procedure.Check)}
    {labels : List String}
    {md : Imperative.MetaData Expression}
    (Hwfb  : Imperative.WellFormedSemanticEvalBool δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σ' σA (ks'.zip ks))
    (Hpres : ∀ entry, entry ∈ pres →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      ((pres.zip labels).map (fun (entry, lbl) =>
        Statement.assert lbl
          (Lambda.LExpr.substFvars entry.snd.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (entry.snd.md.setCallSiteFileRange md)))
      ⟨σ', δ, false⟩ := by
  induction pres generalizing labels with
  | nil =>
    simp [List.zip_nil_left, List.map_nil]
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons head tail ih =>
    cases labels with
    | nil =>
      simp [List.zip_nil_right, List.map_nil]
      exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
    | cons lbl labels' =>
      obtain ⟨_, check⟩ := head
      have HtailHyp :
          ∀ entry, entry ∈ tail →
            Imperative.invStores σA σ'
              ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
                (ks ++ ks')) ∧
            ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
            δ σA entry.snd.expr = some Imperative.HasBool.tt := by
        intros entry hin; exact Hpres entry (List.mem_cons_of_mem _ hin)
      have Htail := ih (labels := labels') HtailHyp
      have HlHead := Hpres _ List.mem_cons_self
      obtain ⟨HinvHead, HnininHead, HevHead⟩ := HlHead
      have Hsubst' : Imperative.substStores σA σ' (ks.zip ks') := by
        apply Imperative.substStoresFlip'
        simp [Imperative.substSwap, zip_swap]
        exact Hsubst
      have Heq : δ σA check.expr =
                  δ σ' (Lambda.LExpr.substFvars check.expr
                          (ks.zip (Core.Transform.createFvars ks'))) :=
        subst_fvars_correct Hwfc Hwfvr Hwfvl Hlen Hdef Hnd Hsubst' HnininHead HinvHead
      have HevSubst : δ σ' (Lambda.LExpr.substFvars check.expr
                            (ks.zip (Core.Transform.createFvars ks'))) =
                      some Imperative.HasBool.tt := by
        rw [← Heq]; exact HevHead
      have Hassert :
          Core.EvalCommandContract π δ σ'
            (Core.CmdExt.cmd
              (Imperative.Cmd.assert
                lbl
                (Lambda.LExpr.substFvars check.expr
                  (ks.zip (Core.Transform.createFvars ks')))
                (check.md.setCallSiteFileRange md)))
            σ' false :=
        Core.EvalCommandContract.cmd_sem (Imperative.EvalCmd.eval_assert_pass HevSubst Hwfb)
      have HheadStmts := singleCmdToStmts (π := π) (φ := φ) Hassert
      simp only [List.zip_cons_cons, List.map_cons, List.singleton_append]
      exact EvalStatementsContractApp HheadStmts Htail

/-- Labels-aware variant of `H_assumes`: takes a separate `labels`
    list (paired positionally with `posts` via `zip`) rather than a
    `labelOf` projection.  This matches the shape exposed by the
    `HassumesShape` clause of `callElimCmd_call_eq` (B3 layer), which
    forms the assumes list as `(posts.zip labels).map (fun (entry, lbl) => …)`. -/
private theorem H_assumes_zip
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σA σ' : CoreStore}
    {ks ks' : List Expression.Ident}
    {posts : List (CoreLabel × Procedure.Check)}
    {labels : List String}
    {md : Imperative.MetaData Expression}
    (Hwfb  : Imperative.WellFormedSemanticEvalBool δ)
    (Hwfvr : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc  : Core.WellFormedCoreEvalCong δ)
    (Hlen  : ks.length = ks'.length)
    (Hnd   : Imperative.substNodup (ks.zip ks'))
    (Hdef  : Imperative.substDefined σA σ' (ks.zip ks'))
    (Hsubst : Imperative.substStores σA σ' (ks.zip ks'))
    (Hposts : ∀ entry, entry ∈ posts →
       Imperative.invStores σA σ'
         ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
            (ks ++ ks')) ∧
       ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
       δ σA entry.snd.expr = some Imperative.HasBool.tt) :
    EvalStatementsContract π φ ⟨σ', δ, false⟩
      ((posts.zip labels).map (fun (entry, lbl) =>
        Statement.assume lbl
          (Lambda.LExpr.substFvars entry.snd.expr
            (ks.zip (Core.Transform.createFvars ks')))
          (entry.snd.md.setCallSiteFileRange md)))
      ⟨σ', δ, false⟩ := by
  induction posts generalizing labels with
  | nil =>
    simp [List.zip_nil_left, List.map_nil]
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons head tail ih =>
    cases labels with
    | nil =>
      simp [List.zip_nil_right, List.map_nil]
      exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
    | cons lbl labels' =>
      obtain ⟨_, check⟩ := head
      have HtailHyp :
          ∀ entry, entry ∈ tail →
            Imperative.invStores σA σ'
              ((Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr).removeAll
                (ks ++ ks')) ∧
            ks'.Disjoint (Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr) ∧
            δ σA entry.snd.expr = some Imperative.HasBool.tt := by
        intros entry hin; exact Hposts entry (List.mem_cons_of_mem _ hin)
      have Htail := ih (labels := labels') HtailHyp
      have HlHead := Hposts _ List.mem_cons_self
      obtain ⟨HinvHead, HnininHead, HevHead⟩ := HlHead
      have Heq : δ σA check.expr =
                  δ σ' (Lambda.LExpr.substFvars check.expr
                          (ks.zip (Core.Transform.createFvars ks'))) :=
        subst_fvars_correct Hwfc Hwfvr Hwfvl Hlen Hdef Hnd Hsubst HnininHead HinvHead
      have HevSubst : δ σ' (Lambda.LExpr.substFvars check.expr
                            (ks.zip (Core.Transform.createFvars ks'))) =
                      some Imperative.HasBool.tt := by
        rw [← Heq]; exact HevHead
      have Hassume :
          Core.EvalCommandContract π δ σ'
            (Core.CmdExt.cmd
              (Imperative.Cmd.assume
                lbl
                (Lambda.LExpr.substFvars check.expr
                  (ks.zip (Core.Transform.createFvars ks')))
                (check.md.setCallSiteFileRange md)))
            σ' false :=
        Core.EvalCommandContract.cmd_sem (Imperative.EvalCmd.eval_assume HevSubst Hwfb)
      have HheadStmts := singleCmdToStmts (π := π) (φ := φ) Hassume
      simp only [List.zip_cons_cons, List.map_cons, List.singleton_append]
      exact EvalStatementsContractApp HheadStmts Htail

/-- Helper: lifting `ReadValues σ ks vs` across an `updatedStates` extension
    by names disjoint from `ks`. Live-code analogue of the legacy
    `ReadValuesUpdatedStates` (which lives inside the deprecated comment
    block at line 393). -/
private theorem readValues_updatedStates
    {σ : CoreStore} {ks ks' : List Expression.Ident}
    {vs : List Expression.Expr} {vs' : List Expression.Expr}
    (Hlen : ks'.length = vs'.length)
    (Hdisj : ks.Disjoint ks')
    (Hrd : ReadValues σ ks vs) :
    ReadValues (updatedStates σ ks' vs') ks vs := by
  induction ks' generalizing σ vs' with
  | nil =>
    cases vs' <;> simp_all [updatedStates, updatedStates']
  | cons k' ks'' ih =>
    cases vs' with
    | nil => simp at Hlen
    | cons v' vs'' =>
      simp only [updatedStates, List.zip_cons_cons, updatedStates']
      have Hdisj' : ks.Disjoint ks'' := by
        intro x Hin1 Hin2
        exact Hdisj Hin1 (List.mem_cons_of_mem _ Hin2)
      -- Prove ReadValues (updatedState σ k' v') ks vs using readValues_updatedState.
      have Hk'_notin : ¬ k' ∈ ks := by
        intro Hin
        exact Hdisj Hin List.mem_cons_self
      have Hrd_step : ReadValues (updatedState σ k' v') ks vs :=
        readValues_updatedState (k:=k') (v:=v') Hk'_notin Hrd
      have Hlen' : ks''.length = vs''.length := by
        simp at Hlen
        exact Hlen
      -- Apply ih on the remaining list.
      exact ih (σ:=updatedState σ k' v') Hlen' Hdisj' Hrd_step

/-! ### Temp-extension lift helpers and the `EvalCallElim_glue` combinator

`updateState_updatedStates_lift` / `havocVars_updatedStates_lift` lift a
single `UpdateState` / `HavocVars` derivation across an `updatedStates` temp
extension, given suitable disjointness. `EvalCallElim_glue` chains the six
call-elim segments (argument init, output init, old init, asserts, havocs,
assumes) through `EvalStatementsContractApp`. -/

/-- A single `UpdateState` lifts across an `updatedStates` temp extension as
    long as the updated variable `x` is disjoint from the temp variables. -/
private theorem updateState_updatedStates_lift
    {σ σ' : CoreStore} {x : Expression.Ident} {v : Expression.Expr}
    {tempVars : List Expression.Ident} {tempVals : List Expression.Expr}
    (Hnotin : ¬ x ∈ tempVars)
    (Hup : Imperative.UpdateState (P:=Expression) σ x v σ') :
    Imperative.UpdateState (P:=Expression)
      (updatedStates σ tempVars tempVals) x v
      (updatedStates σ' tempVars tempVals) := by
  cases Hup with
  | update Hsome Hsome' Hother =>
    rename_i v'
    -- Lookup x in extended σ.
    have HlookupL :
        (updatedStates σ tempVars tempVals) x = some v' := by
      simp [updatedStates]
      have : ∀ (ts : List Expression.Ident) (vs : List Expression.Expr) (s : CoreStore),
          ¬ x ∈ ts → s x = some v' →
          (updatedStates' s (ts.zip vs)) x = some v' := by
        intro ts
        induction ts with
        | nil => intros vs s _ Hs; simp [updatedStates']; exact Hs
        | cons t ts ih =>
          intro vs s Hxn Hs
          cases vs with
          | nil => simp [updatedStates', List.zip]; exact Hs
          | cons w ws =>
            simp [updatedStates', List.zip, List.zipWith]
            have Hxt : x ≠ t := fun h => Hxn (h ▸ List.mem_cons_self)
            have Hxts : ¬ x ∈ ts := fun h => Hxn (List.mem_cons_of_mem _ h)
            have HsTail : (updatedState s t w) x = some v' := by
              simp [updatedState, Hxt]; exact Hs
            exact ih ws (updatedState s t w) Hxts HsTail
      exact this tempVars tempVals σ Hnotin Hsome
    have HlookupR :
        (updatedStates σ' tempVars tempVals) x = some v := by
      simp [updatedStates]
      have : ∀ (ts : List Expression.Ident) (vs : List Expression.Expr) (s : CoreStore),
          ¬ x ∈ ts → s x = some v →
          (updatedStates' s (ts.zip vs)) x = some v := by
        intro ts
        induction ts with
        | nil => intros vs s _ Hs; simp [updatedStates']; exact Hs
        | cons t ts ih =>
          intro vs s Hxn Hs
          cases vs with
          | nil => simp [updatedStates', List.zip]; exact Hs
          | cons w ws =>
            simp [updatedStates', List.zip, List.zipWith]
            have Hxt : x ≠ t := fun h => Hxn (h ▸ List.mem_cons_self)
            have Hxts : ¬ x ∈ ts := fun h => Hxn (List.mem_cons_of_mem _ h)
            have HsTail : (updatedState s t w) x = some v := by
              simp [updatedState, Hxt]; exact Hs
            exact ih ws (updatedState s t w) Hxts HsTail
      exact this tempVars tempVals σ' Hnotin Hsome'
    have Hframe : ∀ y, x ≠ y →
        (updatedStates σ' tempVars tempVals) y =
        (updatedStates σ tempVars tempVals) y := by
      intro y Hne
      simp [updatedStates]
      -- Induct over tempVars, tempVals together.
      have : ∀ (ts : List Expression.Ident) (vs : List Expression.Expr)
              (s s2 : CoreStore),
          (∀ z, x ≠ z → s2 z = s z) →
          (updatedStates' s2 (ts.zip vs)) y =
          (updatedStates' s (ts.zip vs)) y := by
        intro ts
        induction ts with
        | nil => intros vs s s2 Hs2; simp [updatedStates']; exact Hs2 y Hne
        | cons t ts ih =>
          intro vs s s2 Hs2
          cases vs with
          | nil => simp [updatedStates', List.zip]; exact Hs2 y Hne
          | cons w ws =>
            simp [updatedStates', List.zip, List.zipWith]
            apply ih ws (updatedState s t w) (updatedState s2 t w)
            intro z Hxz
            simp [updatedState]
            split
            · rfl
            · exact Hs2 z Hxz
      exact this tempVars tempVals σ σ' Hother
    exact Imperative.UpdateState.update HlookupL HlookupR Hframe

/-- Lift a `HavocVars` derivation across a temp-extension, given the havoc'd
    variables are disjoint from the temp variables. -/
private theorem havocVars_updatedStates_lift
    {σ σ' : CoreStore} {ks tempVars : List Expression.Ident}
    {tempVals : List Expression.Expr}
    (Hdisj : ks.Disjoint tempVars)
    (Hhav : HavocVars σ ks σ') :
    HavocVars (updatedStates σ tempVars tempVals) ks
              (updatedStates σ' tempVars tempVals) := by
  induction Hhav with
  | update_none => exact HavocVars.update_none
  | @update_some σ_a x v σ_b ks_t σ_c hUp hTail ih =>
    have Hxnotin : ¬ x ∈ tempVars :=
      fun hin => Hdisj (List.mem_cons_self) hin
    have Hdisj_t : ks_t.Disjoint tempVars := by
      intro y Hy_in_t Hy_in_temp
      exact Hdisj (List.mem_cons_of_mem _ Hy_in_t) Hy_in_temp
    have hUp' : Imperative.UpdateState (P:=Expression)
                  (updatedStates σ_a tempVars tempVals) x v
                  (updatedStates σ_b tempVars tempVals) :=
      updateState_updatedStates_lift Hxnotin hUp
    have hTail' : HavocVars (updatedStates σ_b tempVars tempVals) ks_t
                            (updatedStates σ_c tempVars tempVals) :=
      ih Hdisj_t
    exact HavocVars.update_some hUp' hTail'

/-- Glue lemma: chain L1–L6 via `EvalStatementsContractApp` to produce the
    full call-elim block evaluation from σ to σ_havoc. -/
private theorem EvalCallElim_glue
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σ σ_arg σ_out σ_old σ_havoc : CoreStore}
    {argInit outInit oldInit asserts havocs assumes : List Statement}
    (HL1 : EvalStatementsContract π φ ⟨σ, δ, false⟩ argInit ⟨σ_arg, δ, false⟩)
    (HL2 : EvalStatementsContract π φ ⟨σ_arg, δ, false⟩ outInit ⟨σ_out, δ, false⟩)
    (HL3 : EvalStatementsContract π φ ⟨σ_out, δ, false⟩ oldInit ⟨σ_old, δ, false⟩)
    (HL4 : EvalStatementsContract π φ ⟨σ_old, δ, false⟩ asserts ⟨σ_old, δ, false⟩)
    (HL5 : EvalStatementsContract π φ ⟨σ_old, δ, false⟩ havocs ⟨σ_havoc, δ, false⟩)
    (HL6 : EvalStatementsContract π φ ⟨σ_havoc, δ, false⟩ assumes ⟨σ_havoc, δ, false⟩) :
    EvalStatementsContract π φ ⟨σ, δ, false⟩
      (argInit ++ outInit ++ oldInit ++ asserts ++ havocs ++ assumes)
      ⟨σ_havoc, δ, false⟩ := by
  have H12 := EvalStatementsContractApp HL1 HL2
  have H123 := EvalStatementsContractApp H12 HL3
  have H1234 := EvalStatementsContractApp H123 HL4
  have H12345 := EvalStatementsContractApp H1234 HL5
  exact EvalStatementsContractApp H12345 HL6

/-! ### Top-level call-elimination correctness theorem -/

/-- Returns the call-elim transformation result of a single command:
    either the rewritten statement list (for a `.call`) or `[s]`
    unchanged (for a non-call statement). -/
@[expose]
def callElimStmt (s : Statement) (p : Program)
    : CoreTransformM (List Statement) := do
  modify (fun σ => { σ with currentProgram := .some p })
  match s with
  | .cmd (CmdExt.call procName args md) => do
      match (← CallElim.callElimCmd (CmdExt.call procName args md)) with
      | .none    => return [s]
      | .some s' => return s'
  | _ => return [s]

/-- A `CoreIdent` is a call-elim temp if its name has the `tmp_` prefix
    used by `Strata.Transform.CoreTransform.tmpVarPrefix`. This is the
    live replacement for the legacy (now-removed) `CoreIdent.isTemp`
    predicate that was referenced by the big-step proof.

    The check is implemented via `List.isPrefixOf` on the `toList`
    representation rather than `String.startsWith` so that we can
    discharge it via the elementary `isPrefixOf_append_self` lemma
    without going through the opaque `String.Slice`/`Pattern`
    machinery. -/
def isTempIdent (v : Expression.Ident) : Bool :=
  "tmp_".toList.isPrefixOf v.name.toList

/-- Mirror of `isTempIdent` for `old`-prefixed identifiers (those generated
    by `oldVarPrefix` via `genOldExprIdent`).  See
    `Strata.Transform.CoreTransform.oldVarPrefix`. -/
def isOldTempIdent (v : Expression.Ident) : Bool :=
  "old_".toList.isPrefixOf v.name.toList

/-- `tmp_*` and `old_*` prefixed identifiers are pairwise disjoint:
    no identifier can be both `isTempIdent` and `isOldTempIdent`.

    Used to discharge `argTemps.Disjoint genOldIdents`-style facts at
    the L6 site. -/
private theorem isTempIdent_isOldTempIdent_disjoint
    {x : Expression.Ident}
    (Htmp : isTempIdent x = true) (Hold : isOldTempIdent x = true) : False := by
  -- isTempIdent x = "tmp_".toList.isPrefixOf x.name.toList
  -- isOldTempIdent x = "old_".toList.isPrefixOf x.name.toList
  -- The first characters differ: 't' vs 'o'.
  unfold isTempIdent at Htmp
  unfold isOldTempIdent at Hold
  match hL : x.name.toList with
  | [] =>
    rw [hL] at Htmp
    simp at Htmp
  | c :: cs =>
    rw [hL] at Htmp Hold
    simp [List.isPrefixOf] at Htmp Hold
    have h1 : 't' = c := Htmp.1
    have h2 : 'o' = c := Hold.1
    rw [← h1] at h2
    exact absurd h2 (by decide)

/-- An inline analogue of the inner-`go` walk inside
    `Procedure.Spec.updateCheckExprs`: given a substituted-expression
    list and an original-checks list, produce the per-entry checks with
    the new expression.  This mirrors the `where go` clause of
    `Procedure.Spec.updateCheckExprs` so we can reason about its result
    without referring to the where-private constant. -/
private def updateCheckExprs_walk
    (es : List Expression.Expr) (checks : List Procedure.Check) :
    List Procedure.Check :=
  match es, checks with
  | [], _ => checks
  | _, [] => checks
  | e :: erest, c :: crest =>
    { c with expr := e } :: updateCheckExprs_walk erest crest

/-- The walk preserves length when `es = checks.map f`. -/
private theorem updateCheckExprs_walk_length_map
    (vs : List Procedure.Check)
    (f : Procedure.Check → Expression.Expr) :
    (updateCheckExprs_walk (vs.map f) vs).length = vs.length := by
  induction vs with
  | nil => simp [updateCheckExprs_walk]
  | cons hd tl ih =>
    simp only [List.map_cons, updateCheckExprs_walk,
               List.length_cons]
    exact congrArg (· + 1) ih

/-- Positional access into `updateCheckExprs_walk (vs.map (substFvars ·.expr sm)) vs`. -/
private theorem updateCheckExprs_walk_getElem_substFvars
    {sm : Map Expression.Ident Expression.Expr}
    (vs : List Procedure.Check)
    (i : Nat)
    (Hi : i < vs.length)
    (Hi' : i < (updateCheckExprs_walk
                  (vs.map (fun c =>
                    Lambda.LExpr.substFvars c.expr sm))
                  vs).length) :
    ((updateCheckExprs_walk
        (vs.map (fun c => Lambda.LExpr.substFvars c.expr sm))
        vs)[i]'Hi').expr =
    Lambda.LExpr.substFvars (vs[i]'Hi).expr sm := by
  induction vs generalizing i with
  | nil =>
    exact absurd Hi (by simp)
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.map_cons, updateCheckExprs_walk,
                 List.getElem_cons_zero]
    | succ k =>
      have Hk : k < tl.length := by
        simp only [List.length_cons] at Hi; omega
      have Hk' : k < (updateCheckExprs_walk
                      (tl.map (fun c =>
                        Lambda.LExpr.substFvars c.expr sm))
                      tl).length := by
        simp only [List.map_cons, updateCheckExprs_walk,
                   List.length_cons] at Hi'
        omega
      have HiH := ih k Hk Hk'
      simp only [List.map_cons, updateCheckExprs_walk,
                 List.getElem_cons_succ]
      exact HiH

/-- The local `updateCheckExprs_walk` mirror agrees pointwise with the
    where-private `Procedure.Spec.updateCheckExprs.go`.  Both walk the two
    lists in parallel and return the original `checks` list when either
    argument is exhausted; the equality holds for all input shapes. -/
private theorem updateCheckExprs_walk_eq_go :
    ∀ (es : List Expression.Expr) (cs : List Procedure.Check),
    updateCheckExprs_walk es cs =
    Procedure.Spec.updateCheckExprs.go es cs := by
  intro es cs
  induction es generalizing cs with
  | nil =>
    cases cs with
    | nil =>
      simp [updateCheckExprs_walk,
            Procedure.Spec.updateCheckExprs.go]
    | cons hd tl =>
      simp [updateCheckExprs_walk,
            Procedure.Spec.updateCheckExprs.go]
  | cons e es' ih =>
    cases cs with
    | nil =>
      simp [updateCheckExprs_walk,
            Procedure.Spec.updateCheckExprs.go]
    | cons hd tl =>
      simp [updateCheckExprs_walk,
            Procedure.Spec.updateCheckExprs.go,
            ih]

/-- For each entry in `updateCheckExprs (conds.values.map (substFvars · sm))
    conds`, the entry's expression is exactly `substFvars c.expr sm` for some
    `c ∈ conds.values`.  This is the per-entry correspondence used by D2f
    to lift `δ σO original_post = tt` (Hpost) to the substituted
    postcondition form.

    Note: the proof relies on the `where`-clause `Procedure.Spec.updateCheckExprs.go`
    walking the lists in parallel; we mirror this via `updateCheckExprs_walk`
    and use definitional unfolding via `show`. -/
private theorem updateCheckExprs_substFvars_mem
    {sm : Map Expression.Ident Expression.Expr}
    {conds : ListMap CoreLabel Procedure.Check}
    {entry : CoreLabel × Procedure.Check}
    (Hentry : entry ∈
      (conds.keys.zip
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values))) :
    ∃ c ∈ conds.values,
      entry.snd.expr = Lambda.LExpr.substFvars c.expr sm := by
  rcases List.mem_iff_get.mp Hentry with ⟨n, Hn⟩
  have Hn_lt_zip := n.isLt
  have Hzip_len :
      (conds.keys.zip
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values)).length =
      Nat.min conds.keys.length
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values).length := List.length_zip
  have Hwalk_len :
      (updateCheckExprs_walk
        (conds.values.map (fun c =>
          Lambda.LExpr.substFvars c.expr sm))
        conds.values).length = conds.values.length :=
    updateCheckExprs_walk_length_map _ _
  have Hn_lt_zip' : n.val <
      Nat.min conds.keys.length
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values).length := Hzip_len ▸ Hn_lt_zip
  have Hn_lt_keys : n.val < conds.keys.length :=
    Nat.lt_of_lt_of_le Hn_lt_zip' (Nat.min_le_left _ _)
  have Hn_lt_walk :
      n.val < (updateCheckExprs_walk
                (conds.values.map (fun c =>
                  Lambda.LExpr.substFvars c.expr sm))
                conds.values).length :=
    Nat.lt_of_lt_of_le Hn_lt_zip' (Nat.min_le_right _ _)
  have Hn_lt_vs : n.val < conds.values.length := Hwalk_len ▸ Hn_lt_walk
  have HzipGet :
      (conds.keys.zip
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values))[n.val]'Hn_lt_zip =
        (conds.keys[n.val]'Hn_lt_keys,
         (updateCheckExprs_walk
            (conds.values.map
              (fun c => Lambda.LExpr.substFvars c.expr sm))
            conds.values)[n.val]'Hn_lt_walk) :=
    List.getElem_zip
  have HhE : (conds.keys.zip _).get n = entry := Hn
  have HhE_get : (conds.keys.zip _)[n.val]'Hn_lt_zip = entry := by
    have : (conds.keys.zip _).get n =
           (conds.keys.zip _)[n.val]'Hn_lt_zip := rfl
    rw [← this]; exact HhE
  rw [HzipGet] at HhE_get
  have Hsnd_eq :
      entry.snd =
        (updateCheckExprs_walk
          (conds.values.map (fun c =>
            Lambda.LExpr.substFvars c.expr sm))
          conds.values)[n.val]'Hn_lt_walk :=
    ((Prod.mk.injEq _ _ _ _).mp HhE_get).2.symm
  refine ⟨conds.values[n.val]'Hn_lt_vs, List.getElem_mem _, ?_⟩
  rw [Hsnd_eq]
  exact updateCheckExprs_walk_getElem_substFvars
    conds.values n.val Hn_lt_vs Hn_lt_walk

/-! ### Producing-side `genIdent → isTempIdent` lemmas

The `CoreGenState.gen pf s` operation produces an identifier whose name is
`pf.name ++ "_" ++ toString counter` (cf. `StringGenState.gen`).  When
`pf.name` itself begins with the literal `"tmp_"` (resp. `"old_"`)
prefix — as it does for `genIdent _ tmpVarPrefix` (resp.
`genIdent _ oldVarPrefix`) — the resulting identifier satisfies
`isTempIdent` (resp. `isOldTempIdent`).

These helpers are kept as their own block so that the producing-side
prefix reasoning is encapsulated in two short proofs rather than scattered
through the inductive helpers below. -/

/-- A single application of `CoreGenState.gen` against the `tmpVarPrefix`
    family of prefixes produces an identifier satisfying `isTempIdent`. -/
private theorem genIdent_tmp_isTempIdent
    {ident : String} {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : (CoreGenState.gen ⟨tmpVarPrefix ident, ()⟩ s) = (l, s')) :
    isTempIdent l = true := by
  -- Unfold the gen step to expose the produced string.
  unfold CoreGenState.gen StringGenState.gen tmpVarPrefix at Hgen
  -- `Hgen` is now a `Prod.mk` equation; project out the identifier component.
  have Hl : l = ⟨"tmp_" ++ ident ++ "_" ++ toString (Counter.genCounter s.cs.cs).fst, ()⟩ := by
    have := congrArg Prod.fst Hgen
    simp at this
    -- Reduce `s!` interpolation.
    rw [show (s!"tmp_{ident}" : String) = "tmp_" ++ ident from rfl] at this
    exact this.symm
  rw [Hl]
  simp only [isTempIdent]
  -- Goal:
  --   "tmp_".toList.isPrefixOf ("tmp_" ++ ident ++ "_" ++ toString counter).toList
  simp only [String.toList_append, List.append_assoc]
  exact isPrefixOf_append_self _ _

/-- Mirror of `genIdent_tmp_isTempIdent` for the `oldVarPrefix` family. -/
private theorem genIdent_old_isOldTempIdent
    {ident : String} {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : (CoreGenState.gen ⟨oldVarPrefix ident, ()⟩ s) = (l, s')) :
    isOldTempIdent l = true := by
  unfold CoreGenState.gen StringGenState.gen oldVarPrefix at Hgen
  have Hl : l = ⟨"old_" ++ ident ++ "_" ++ toString (Counter.genCounter s.cs.cs).fst, ()⟩ := by
    have := congrArg Prod.fst Hgen
    simp at this
    rw [show (s!"old_{ident}" : String) = "old_" ++ ident from rfl] at this
    exact this.symm
  rw [Hl]
  simp only [isOldTempIdent]
  simp only [String.toList_append, List.append_assoc]
  exact isPrefixOf_append_self _ _

/-! ### Generic `mapM`-over-`CoreGenM` helpers

The Arg/Out/Old gen-ident families share the structural shape
`List.mapM (g : α → CoreGenM Ident) l`, where the only difference is
`α` (Unit for Arg, Ident for Out/Old) and the per-element generator `g`.
The four facts below — length preservation, generated-stack accounting,
WF preservation, and `Forall`-lifting — depend only on (i) `mapM`'s
recursion shape and (ii) a pointwise hypothesis on the per-element
generator.  We prove each generically once and derive the 12
single-iterator specializations (3 each for Arg/Out/Old × length /
GeneratedWF / WFMono / Forall) as one-line corollaries. -/

/-- Length preservation for any `List.mapM` against `CoreGenM`. -/
private theorem genIdentMapM_length' {α : Type}
    {g : α → CoreGenM Expression.Ident}
    {l : List α} {s : CoreGenState} :
    (List.mapM g l s).fst.length = l.length := by
  induction l generalizing s <;> simp_all
  case nil =>
    simp [pure, StateT.pure]
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map]
    split
    simp [StateT.map, Functor.map]
    apply ih

/-- Generated-stack accounting for `List.mapM` once the per-element
    generator is known to push exactly one element onto `generated`. -/
private theorem genIdentMapM_GeneratedWF {α : Type}
    {g : α → CoreGenM Expression.Ident}
    (Hone : ∀ {a : α} {s s' : CoreGenState} {l : Expression.Ident},
              g a s = (l, s') → s'.generated = l :: s.generated)
    {l : List α} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : List.mapM g l s = (ls, s')) :
    s'.generated = ls.reverse ++ s.generated := by
  induction l generalizing s s' ls with
  | nil =>
      simp only [List.mapM_nil, pure, StateT.pure] at Hgen
      cases Hgen
      simp
  | cons h t ih =>
      simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure] at Hgen
      cases hg1 : g h s with
      | mk a₁ s₁ =>
        rw [hg1] at Hgen
        simp only at Hgen
        cases hg2 : List.mapM g t s₁ with
        | mk a₂ s₂ =>
          rw [hg2] at Hgen
          cases Hgen
          have HH₁ := Hone hg1
          have HH₂ := ih hg2
          rw [HH₂, HH₁]
          simp

/-- WF preservation for `List.mapM` once the per-element generator
    preserves WF. -/
private theorem genIdentMapM_WFMono {α : Type}
    {g : α → CoreGenM Expression.Ident}
    (Hone : ∀ {a : α} {s s' : CoreGenState} {l : Expression.Ident},
              CoreGenState.WF s → g a s = (l, s') → CoreGenState.WF s')
    {l : List α} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : List.mapM g l s = (ls, s')) :
    CoreGenState.WF s' := by
  induction l generalizing s s' ls with
  | nil =>
      simp only [List.mapM_nil, pure, StateT.pure] at Hgen
      cases Hgen
      exact Hwf
  | cons h t ih =>
      simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure] at Hgen
      cases hg1 : g h s with
      | mk a₁ s₁ =>
        rw [hg1] at Hgen
        simp only at Hgen
        cases hg2 : List.mapM g t s₁ with
        | mk a₂ s₂ =>
          rw [hg2] at Hgen
          cases Hgen
          exact ih (Hone Hwf hg1) hg2

/-- `Forall`-lifting for `List.mapM` once the per-element generator
    produces values satisfying the predicate. -/
private theorem genIdentMapM_Forall {α : Type} {P : Expression.Ident → Prop}
    {g : α → CoreGenM Expression.Ident}
    (Hone : ∀ {a : α} {s s' : CoreGenState} {l : Expression.Ident},
              g a s = (l, s') → P l)
    {l : List α} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : List.mapM g l s = (ls, s')) :
    Forall P ls := by
  induction l generalizing s s' ls with
  | nil =>
      simp only [List.mapM_nil, pure, StateT.pure] at Hgen
      cases Hgen
      simp [Forall]
  | cons h t ih =>
      simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure] at Hgen
      cases hg1 : g h s with
      | mk a₁ s₁ =>
        rw [hg1] at Hgen
        simp only at Hgen
        cases hg2 : List.mapM g t s₁ with
        | mk a₂ s₂ =>
          rw [hg2] at Hgen
          cases Hgen
          simp [Forall]
          exact ⟨Hone hg1, ih hg2⟩

/-! ### Length lemmas for the `gen*ExprIdents{,Trip}` family

The `_snd` and `*GeneratedWF` helpers below need to know that
`genArgExprIdents n` produces a list of length exactly `n`, etc.  These
follow inductively from `genIdent`'s contract.  Proved here so that the
trip-level helpers can quote them directly. -/

/-- The fst-projection of running `genArgExprIdent` `t.length`-many times
    (with `t : List Unit`) is a list of length `t.length`.  This is the
    raw form; `genArgExprIdents_length'` specializes to `n = t.length`. -/
private theorem genArgExprIdent_len'
    {t : List Unit} {s : CoreGenState} :
    (List.mapM (fun _ => genArgExprIdent) t s).fst.length = t.length :=
  genIdentMapM_length'

private theorem genArgExprIdents_length'
    (n : Nat) (s : CoreGenState) :
    (genArgExprIdents n s).fst.length = n := by
  simp only [genArgExprIdents]
  rw [genArgExprIdent_len']
  simp

private theorem genArgExprIdents_length
    {n : Nat} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : genArgExprIdents n s = (ls, s')) :
    ls.length = n := by
  have := genArgExprIdents_length' n s
  rw [Hgen] at this
  exact this

private theorem genOutExprIdent_len'
    {t : List Expression.Ident} {s : CoreGenState} :
    (List.mapM genOutExprIdent t s).fst.length = t.length :=
  genIdentMapM_length'

private theorem genOutExprIdents_length'
    (idents : List Expression.Ident) (s : CoreGenState) :
    (genOutExprIdents idents s).fst.length = idents.length := by
  simp only [genOutExprIdents]
  exact genOutExprIdent_len'

private theorem genOutExprIdents_length
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : genOutExprIdents idents s = (ls, s')) :
    ls.length = idents.length := by
  have := genOutExprIdents_length' idents s
  rw [Hgen] at this
  exact this

private theorem genOldExprIdent_len'
    {t : List Expression.Ident} {s : CoreGenState} :
    (List.mapM genOldExprIdent t s).fst.length = t.length :=
  genIdentMapM_length'

private theorem genOldExprIdents_length'
    (idents : List Expression.Ident) (s : CoreGenState) :
    (genOldExprIdents idents s).fst.length = idents.length := by
  simp only [genOldExprIdents]
  exact genOldExprIdent_len'

private theorem genOldExprIdents_length
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : genOldExprIdents idents s = (ls, s')) :
    ls.length = idents.length := by
  have := genOldExprIdents_length' idents s
  rw [Hgen] at this
  exact this

/-! ### Trip-level success extractors

The Arg and Out trip wrappers share a uniform success-branch shape: they
length-check, run a `genXxxExprIdents` call, and `return
(gen_idents.zip ys).zip xs`.  Extracting the post-condition once removes
~80 LoC of repeated monad-layer simping. -/

private theorem genArgExprIdentsTrip_extract
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hgen : genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    let gen_idents := (genArgExprIdents args.length s.genState).fst
    let s_gen     := (genArgExprIdents args.length s.genState).snd
    (gen_idents.zip (List.map Prod.snd inputs)).zip args = argTrips ∧
    s' = { s with genState := s_gen } ∧
    inputs.length = args.length := by
  simp only [genArgExprIdentsTrip] at Hgen
  split at Hgen
  case isTrue Hne =>
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure] at Hgen
    cases Hgen
  case isFalse Hlen =>
    simp [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.lift,
          ExceptT.pure, StateT.bind, StateT.pure, pure, monadLift,
          MonadLift.monadLift, liftM, Functor.map, StateT.map,
          liftCoreGenM] at Hgen
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg Prod.fst Hgen
      simp at this
      exact this
    · have := congrArg Prod.snd Hgen
      simp at this
      exact this.symm
    · simp at Hlen; exact Hlen

private theorem genOutExprIdentsTrip_extract
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hgen : genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    let gen_idents := (genOutExprIdents lhs s.genState).fst
    let s_gen     := (genOutExprIdents lhs s.genState).snd
    (gen_idents.zip (List.map Prod.snd outputs)).zip lhs = outTrips ∧
    s' = { s with genState := s_gen } ∧
    outputs.length = lhs.length := by
  simp only [genOutExprIdentsTrip] at Hgen
  split at Hgen
  case isTrue Hne =>
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure] at Hgen
    cases Hgen
  case isFalse Hlen =>
    simp [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.lift,
          ExceptT.pure, StateT.bind, StateT.pure, pure, monadLift,
          MonadLift.monadLift, liftM, Functor.map, StateT.map,
          liftCoreGenM] at Hgen
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg Prod.fst Hgen
      simp at this
      exact this
    · have := congrArg Prod.snd Hgen
      simp at this
      exact this.symm
    · simp at Hlen; exact Hlen

/-! ### Trip-shape geometry helpers

The Arg/Out/Old trip lemmas all share a `((g.zip ys).zip xs)` outer
shape and project either the `.unzip.snd` (= `xs`, given length
agreement) or `.unzip.fst.unzip.fst` (= `g`, ditto).  These pure list
facts are extracted once so that the trip-level lemmas can short-cut
their unzip/zip ceremony. -/

private theorem zip_zip_unzip_snd_of_lengths {α β γ}
    {g : List α} {ys : List β} {xs : List γ}
    (Hgx : g.length = xs.length) (Hyx : ys.length = xs.length) :
    ((g.zip ys).zip xs).unzip.snd = xs := by
  rw [List.unzip_zip_right]
  rw [List.length_zip]
  omega

private theorem zip_zip_unzip_fst_unzip_fst_of_lengths {α β γ}
    {g : List α} {ys : List β} {xs : List γ}
    (Hgx : g.length = xs.length) (Hyx : ys.length = xs.length) :
    ((g.zip ys).zip xs).unzip.fst.unzip.fst = g := by
  rw [List.unzip_zip_left (l₁ := (g.zip ys)) (l₂ := xs)]
  · rw [List.unzip_zip_left (l₁ := g) (l₂ := ys)]
    omega
  · rw [List.length_zip]
    omega

/-! ### `_snd` projection lemmas for the `gen*ExprIdentsTrip` family

These say: the `Prod.snd` projection of the trip list is exactly the
input arguments/lhs/old-vars list.  The legacy proofs went through
intricate splittings; the live forms are short reductions through the
monad layers because we have the structural form
`(gen_idents.zip inputs.unzip.2).zip args` directly visible. -/

private theorem genArgExprIdentsTrip_snd
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hgen : genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    argTrips.unzip.snd = args := by
  obtain ⟨Hat, _, Hilen⟩ := genArgExprIdentsTrip_extract Hgen
  rw [← Hat]
  exact zip_zip_unzip_snd_of_lengths
          (genArgExprIdents_length' args.length s.genState)
          (by simp [List.length_map]; omega)

private theorem genOutExprIdentsTrip_snd
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hgen : genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    outTrips.unzip.snd = lhs := by
  obtain ⟨Hot, _, Hilen⟩ := genOutExprIdentsTrip_extract Hgen
  rw [← Hot]
  exact zip_zip_unzip_snd_of_lengths
          (genOutExprIdents_length' lhs s.genState)
          (by simp [List.length_map]; omega)

/-- The "snd" projection lemma for the `oldTripsRaw` shape used in the
    live `callElimCmd`: `oldTripsRaw = (genOldIdents.zip oldTys).zip oldVars`,
    so its `snd` projection is `oldVars` provided
    `genOldIdents.length = oldVars.length` and `oldTys.length = oldVars.length`.

    Unlike the arg/out cases, the live `callElimCmd` does not call a
    dedicated `genOldExprIdentsTrip` wrapper; instead it constructs
    `oldTripsRaw` inline.  This helper provides the equivalent
    structural fact. -/
private theorem genOldExprIdentsTrip_snd
    {oldVars : List Expression.Ident}
    {oldTys : List Lambda.LTy}
    {s s' : CoreGenState}
    {genOldIdents : List Expression.Ident}
    (Hgen : genOldExprIdents oldVars s = (genOldIdents, s'))
    (Htylen : oldTys.length = oldVars.length) :
    ((genOldIdents.zip oldTys).zip oldVars).unzip.snd = oldVars :=
  zip_zip_unzip_snd_of_lengths (genOldExprIdents_length Hgen) Htylen

/-! ### `*GeneratedWF` lemmas: each generator pushes its results to `generated`

`CoreGenState.gen` extends `generated` by one cons; running `mapM` of a
generator over a list extends `generated` by the produced list reversed.
The trip-wrapper variants quote these and additionally lift the
`generated` accounting through `CoreTransformState`. -/

private theorem genCoreIdentGeneratedWF
    {pf : Expression.Ident} {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : CoreGenState.gen pf s = (l, s')) :
    s'.generated = l :: s.generated := by
  unfold CoreGenState.gen at Hgen
  have Hl : l = ⟨(StringGenState.gen pf.name s.cs).fst, ()⟩ := by
    have := congrArg Prod.fst Hgen
    simp at this
    exact this.symm
  have Hs : s' = { cs := (StringGenState.gen pf.name s.cs).snd,
                   generated := ⟨(StringGenState.gen pf.name s.cs).fst, ()⟩ :: s.generated } := by
    have := congrArg Prod.snd Hgen
    simp at this
    exact this.symm
  rw [Hl, Hs]

private theorem genIdentGeneratedWF
    {ident : Expression.Ident} {pf : String → String}
    {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : genIdent ident pf s = (l, s')) :
    s'.generated = l :: s.generated :=
  genCoreIdentGeneratedWF Hgen

private theorem genArgExprIdentGeneratedWF
    {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : genArgExprIdent s = (l, s')) :
    s'.generated = l :: s.generated :=
  genCoreIdentGeneratedWF Hgen

private theorem genOutExprIdentGeneratedWF
    {e : Expression.Ident} {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : genOutExprIdent e s = (l, s')) :
    s'.generated = l :: s.generated :=
  genCoreIdentGeneratedWF Hgen

private theorem genOldExprIdentGeneratedWF
    {e : Expression.Ident} {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : genOldExprIdent e s = (l, s')) :
    s'.generated = l :: s.generated :=
  genCoreIdentGeneratedWF Hgen

private theorem genArgExprIdents_GeneratedWF
    {n : Nat} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : genArgExprIdents n s = (ls, s')) :
    s'.generated = ls.reverse ++ s.generated :=
  genIdentMapM_GeneratedWF
    (g := fun (_ : Unit) => genArgExprIdent)
    (fun H => genArgExprIdentGeneratedWF H) Hgen

private theorem genOutExprIdents_GeneratedWF
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : genOutExprIdents idents s = (ls, s')) :
    s'.generated = ls.reverse ++ s.generated :=
  genIdentMapM_GeneratedWF
    (g := genOutExprIdent)
    (fun H => genOutExprIdentGeneratedWF H) Hgen

private theorem genOldExprIdents_GeneratedWF
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : genOldExprIdents idents s = (ls, s')) :
    s'.generated = ls.reverse ++ s.generated :=
  genIdentMapM_GeneratedWF
    (g := genOldExprIdent)
    (fun H => genOldExprIdentGeneratedWF H) Hgen

/-- Trip-level GeneratedWF for arg trips: the generated list is extended
    with `argTrips.unzip.fst.unzip.fst.reverse`. -/
private theorem genArgExprIdentsTripGeneratedWF
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hgen : genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    s'.genState.generated =
        argTrips.unzip.fst.unzip.fst.reverse ++ s.genState.generated := by
  obtain ⟨Hat, Hs', Hilen⟩ := genArgExprIdentsTrip_extract Hgen
  rw [Hs']; simp only
  rw [genArgExprIdents_GeneratedWF (s := s.genState)
        (s' := (genArgExprIdents args.length s.genState).snd)
        (ls := (genArgExprIdents args.length s.genState).fst) rfl]
  congr 1
  rw [← Hat]
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genArgExprIdents_length' args.length s.genState)
        (by simp [List.length_map]; omega)]

private theorem genOutExprIdentsTripGeneratedWF
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hgen : genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    s'.genState.generated =
        outTrips.unzip.fst.unzip.fst.reverse ++ s.genState.generated := by
  obtain ⟨Hot, Hs', Hilen⟩ := genOutExprIdentsTrip_extract Hgen
  rw [Hs']; simp only
  rw [genOutExprIdents_GeneratedWF (s := s.genState)
        (s' := (genOutExprIdents lhs s.genState).snd)
        (ls := (genOutExprIdents lhs s.genState).fst) rfl]
  congr 1
  rw [← Hot]
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genOutExprIdents_length' lhs s.genState)
        (by simp [List.length_map]; omega)]

/-! ### `gen*ExprIdents{,Trip}_isTempIdent` lemmas

Each fresh identifier produced by `gen{Arg,Out}ExprIdent` (which calls
`genIdent _ tmpVarPrefix`) satisfies `isTempIdent`; each produced by
`genOldExprIdent` satisfies `isOldTempIdent`.  These lift through the
list-mapM iterators (`gen*ExprIdents`) and the trip wrappers
(`gen*ExprIdentsTrip`). -/

private theorem genArgExprIdent_isTempIdent
    {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : genArgExprIdent s = (l, s')) :
    isTempIdent l = true := by
  simp only [genArgExprIdent, genIdent] at Hgen
  exact genIdent_tmp_isTempIdent Hgen

private theorem genOutExprIdent_isTempIdent
    {ident : Expression.Ident} {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : genOutExprIdent ident s = (l, s')) :
    isTempIdent l = true := by
  simp only [genOutExprIdent, genIdent] at Hgen
  exact genIdent_tmp_isTempIdent Hgen

private theorem genOldExprIdent_isOldTempIdent
    {ident : Expression.Ident} {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : genOldExprIdent ident s = (l, s')) :
    isOldTempIdent l = true := by
  simp only [genOldExprIdent, genIdent] at Hgen
  exact genIdent_old_isOldTempIdent Hgen

private theorem genArgExprIdents_isTempIdent
    {n : Nat} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : genArgExprIdents n s = (ls, s')) :
    Forall (fun x => isTempIdent x) ls :=
  genIdentMapM_Forall
    (g := fun (_ : Unit) => genArgExprIdent)
    (fun H => genArgExprIdent_isTempIdent H) Hgen

private theorem genOutExprIdents_isTempIdent
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : genOutExprIdents idents s = (ls, s')) :
    Forall (fun x => isTempIdent x) ls :=
  genIdentMapM_Forall
    (g := genOutExprIdent)
    (fun H => genOutExprIdent_isTempIdent H) Hgen

private theorem genOldExprIdents_isOldTempIdent
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : genOldExprIdents idents s = (ls, s')) :
    Forall (fun x => isOldTempIdent x) ls :=
  genIdentMapM_Forall
    (g := genOldExprIdent)
    (fun H => genOldExprIdent_isOldTempIdent H) Hgen

/-- Trip-level isTempIdent for arg trips: every fresh ident produced by
    `genArgExprIdentsTrip` satisfies `isTempIdent`. -/
private theorem genArgExprIdentsTrip_isTempIdent
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hgen : genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    Forall (fun x => isTempIdent x) argTrips.unzip.fst.unzip.fst := by
  obtain ⟨Hat, _, Hilen⟩ := genArgExprIdentsTrip_extract Hgen
  rw [← Hat]
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genArgExprIdents_length' args.length s.genState)
        (by simp [List.length_map]; omega)]
  exact genArgExprIdents_isTempIdent (s := s.genState)
          (s' := (genArgExprIdents args.length s.genState).snd)
          (ls := (genArgExprIdents args.length s.genState).fst) rfl

private theorem genOutExprIdentsTrip_isTempIdent
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hgen : genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    Forall (fun x => isTempIdent x) outTrips.unzip.fst.unzip.fst := by
  obtain ⟨Hot, _, Hilen⟩ := genOutExprIdentsTrip_extract Hgen
  rw [← Hot]
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genOutExprIdents_length' lhs s.genState)
        (by simp [List.length_map]; omega)]
  exact genOutExprIdents_isTempIdent (s := s.genState)
          (s' := (genOutExprIdents lhs s.genState).snd)
          (ls := (genOutExprIdents lhs s.genState).fst) rfl

/-- For the live `callElimCmd`, `oldTrips`'s `fst.fst` projection is exactly
    the fresh `genOldIdents` produced by `genOldExprIdents`, since the trip
    structure is `((freshIdent, ty), origVar)`. -/
private theorem genOldExprIdentsTrip_isOldTempIdent
    {oldVars : List Expression.Ident}
    {oldTys : List Lambda.LTy}
    {s s' : CoreGenState}
    {genOldIdents : List Expression.Ident}
    (Hgen : genOldExprIdents oldVars s = (genOldIdents, s'))
    (Htylen : oldTys.length = oldVars.length) :
    Forall (fun x => isOldTempIdent x)
      ((genOldIdents.zip oldTys).zip oldVars).unzip.fst.unzip.fst := by
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genOldExprIdents_length Hgen) Htylen]
  exact genOldExprIdents_isOldTempIdent Hgen

/-! ### `*WFMono` lemmas: each generator preserves `CoreGenState.WF`

These lift `CoreGenState.WFMono'` through the inductive structure of
`gen*ExprIdents` and the `CoreTransformM` wrapping of `gen*ExprIdentsTrip`. -/

private theorem genArgExprIdentWFMono
    {s s' : CoreGenState} {l : Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : genArgExprIdent s = (l, s')) :
    CoreGenState.WF s' :=
  CoreGenState.WFMono' Hwf Hgen

private theorem genOutExprIdentWFMono
    {e : Expression.Ident} {s s' : CoreGenState} {l : Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : genOutExprIdent e s = (l, s')) :
    CoreGenState.WF s' :=
  CoreGenState.WFMono' Hwf Hgen

private theorem genOldExprIdentWFMono
    {e : Expression.Ident} {s s' : CoreGenState} {l : Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : genOldExprIdent e s = (l, s')) :
    CoreGenState.WF s' :=
  CoreGenState.WFMono' Hwf Hgen

private theorem genArgExprIdents_WFMono
    {n : Nat} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : genArgExprIdents n s = (ls, s')) :
    CoreGenState.WF s' :=
  genIdentMapM_WFMono
    (g := fun (_ : Unit) => genArgExprIdent)
    (fun H1 H2 => genArgExprIdentWFMono H1 H2) Hwf Hgen

private theorem genOutExprIdents_WFMono
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : genOutExprIdents idents s = (ls, s')) :
    CoreGenState.WF s' :=
  genIdentMapM_WFMono
    (g := genOutExprIdent)
    (fun H1 H2 => genOutExprIdentWFMono H1 H2) Hwf Hgen

private theorem genOldExprIdents_WFMono
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : genOldExprIdents idents s = (ls, s')) :
    CoreGenState.WF s' :=
  genIdentMapM_WFMono
    (g := genOldExprIdent)
    (fun H1 H2 => genOldExprIdentWFMono H1 H2) Hwf Hgen

/-- Trip-level WFMono for arg trips. -/
private theorem genArgExprIdentsTripWFMono
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hwf : CoreGenState.WF s.genState)
    (Hgen : genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    CoreGenState.WF s'.genState := by
  obtain ⟨_, Hs', _⟩ := genArgExprIdentsTrip_extract Hgen
  rw [Hs']; simp only
  exact genArgExprIdents_WFMono (s := s.genState)
          (s' := (genArgExprIdents args.length s.genState).snd)
          (ls := (genArgExprIdents args.length s.genState).fst) Hwf rfl

/-- Trip-level WFMono for out trips. -/
private theorem genOutExprIdentsTripWFMono
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hwf : CoreGenState.WF s.genState)
    (Hgen : genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    CoreGenState.WF s'.genState := by
  obtain ⟨_, Hs', _⟩ := genOutExprIdentsTrip_extract Hgen
  rw [Hs']; simp only
  exact genOutExprIdents_WFMono (s := s.genState)
          (s' := (genOutExprIdents lhs s.genState).snd)
          (ls := (genOutExprIdents lhs s.genState).fst) Hwf rfl

/-- Bare WFMono for old vars (live `callElimCmd` builds `oldTripsRaw` inline). -/
private theorem genOldExprIdentsTripWFMono
    {oldVars : List Expression.Ident}
    {s s' : CoreGenState} {genOldIdents : List Expression.Ident}
    (Hwf : CoreGenState.WF s)
    (Hgen : genOldExprIdents oldVars s = (genOldIdents, s')) :
    CoreGenState.WF s' :=
  genOldExprIdents_WFMono Hwf Hgen

/-- Trip-level GeneratedWF for old trips, parameterized over the bare
    `genOldExprIdents` (since the live `callElimCmd` constructs its
    `oldTripsRaw` inline rather than through a wrapper). -/
private theorem genOldExprIdentsTripGeneratedWF
    {oldVars : List Expression.Ident} {oldTys : List Lambda.LTy}
    {s s' : CoreGenState} {genOldIdents : List Expression.Ident}
    (Hgen : genOldExprIdents oldVars s = (genOldIdents, s'))
    (Htylen : oldTys.length = oldVars.length) :
    s'.generated =
        ((genOldIdents.zip oldTys).zip oldVars).unzip.fst.unzip.fst.reverse ++ s.generated := by
  rw [genOldExprIdents_GeneratedWF Hgen]
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genOldExprIdents_length Hgen) Htylen]

/-! ## Call-case helper lemmas

These helpers bridge the post-`Visibility`-removal WF infrastructure to the
disjointness/Nodup obligations the L1–L6 wrappers need.  See
`docs/superpowers/research/2026-05-21-wf-infrastructure-survey.md` and
`docs/superpowers/research/2026-05-21-legacy-call-case-recipe.md` for
context.

Most helpers here *consume* a `Forall isTempIdent` (resp.
`Forall isOldTempIdent`) hypothesis on a list of newly-generated names
rather than producing one from `genIdent` semantics directly: producing
`isTempIdent` requires reasoning about `String.startsWith`, which goes
through opaque `Slice`/`Pattern` infrastructure (cf.
`Strata.DL.Util.String` for context).  The producing-side derivation is
deferred to Task 6e along with the open `sorry`. -/

/-- Identifiers in a procedure header's input keys are also names of `p`
    (via `Decl.names`) when `proc` is found by `Program.Procedure.find?`.
    Useful for combining `WFProgramProp.namesNodup` with per-procedure
    `inputsNodup` to derive disjointness facts. -/
private theorem program_def_not_temp
    {x : Expression.Ident}
    (Hpfresh : ¬ isTempIdent x ∧ ¬ isOldTempIdent x) :
    ¬ isTempIdent x := Hpfresh.1

/-- Mirror of `program_def_not_temp` for the `old_` prefix. -/
private theorem program_def_not_oldTemp
    {x : Expression.Ident}
    (Hpfresh : ¬ isTempIdent x ∧ ¬ isOldTempIdent x) :
    ¬ isOldTempIdent x := Hpfresh.2

/-- A `Forall isTempIdent` list is disjoint from any list of identifiers
    none of which is `isTempIdent`.  This is the canonical disjointness
    bridge between freshly-generated temps and program-defined names. -/
private theorem isTemp_disjoint_notTemp
    {temps progNames : List Expression.Ident}
    (Htemps : Forall (fun x => isTempIdent x) temps)
    (Hprog : ∀ x ∈ progNames, ¬ isTempIdent x) :
    temps.Disjoint progNames := by
  intro x Hin1 Hin2
  have Htemp : isTempIdent x := (List.Forall_mem_iff.mp Htemps) x Hin1
  exact (Hprog x Hin2) Htemp

/-- Mirror of `isTemp_disjoint_notTemp` for the `old_` prefix. -/
private theorem isOldTemp_disjoint_notOldTemp
    {olds progNames : List Expression.Ident}
    (Holds : Forall (fun x => isOldTempIdent x) olds)
    (Hprog : ∀ x ∈ progNames, ¬ isOldTempIdent x) :
    olds.Disjoint progNames := by
  intro x Hin1 Hin2
  have Hold : isOldTempIdent x := (List.Forall_mem_iff.mp Holds) x Hin1
  exact (Hprog x Hin2) Hold

/-- Bridge from the `tmp_` half of `Hwfgenst` to `isNotDefined` for a list
    of fresh temp names: if a name is `isTempIdent` and is *not* in
    `γ.generated`, then it must be undefined in σ (otherwise the iff in
    `Hwfgentmp` would put it in `γ.generated`).

    Takes the dual-clause `tmp_` half: for every `v`, `v ∈ generated ∧
    isTempIdent v ↔ (σ v).isSome ∧ isTempIdent v`. -/
private theorem fresh_temps_not_defined
    {σ : CoreStore} {γ : CoreTransformState}
    (Hwfgentmp : ∀ v, v ∈ γ.genState.generated ∧ isTempIdent v ↔
                  ((σ v).isSome ∧ isTempIdent v))
    {newTemps : List Expression.Ident}
    (Hnotgen : ∀ x ∈ newTemps, x ∉ γ.genState.generated)
    (HtempPred : Forall (fun x => isTempIdent x) newTemps) :
    Imperative.isNotDefined σ newTemps := by
  intro v Hin
  have Htemp : isTempIdent v := (List.Forall_mem_iff.mp HtempPred) v Hin
  have Hnotin : v ∉ γ.genState.generated := Hnotgen v Hin
  -- If σ v = some _ then `Hwfgentmp.mpr` would put v in `γ.generated`,
  -- contradicting `Hnotin`.  Case split on `σ v` directly.
  match hσ : σ v with
  | none => rfl
  | some w =>
      exfalso
      apply Hnotin
      have Hbundle : (σ v).isSome ∧ isTempIdent v := by
        refine ⟨?_, Htemp⟩
        simp [hσ]
      exact ((Hwfgentmp v).mpr Hbundle).1

/-- Bridge from the `old_` half of `Hwfgenst` to `isNotDefined` for a list
    of fresh `old_`-prefixed names: if every name is `isOldTempIdent`, then
    each must be undefined in σ by the freshness clause. -/
private theorem fresh_olds_not_defined
    {σ : CoreStore}
    (Hwfgenold : ∀ v, isOldTempIdent v → (σ v).isNone)
    {newOlds : List Expression.Ident}
    (HoldPred : Forall (fun x => isOldTempIdent x) newOlds) :
    Imperative.isNotDefined σ newOlds := by
  intro v Hin
  have Hold : isOldTempIdent v := (List.Forall_mem_iff.mp HoldPred) v Hin
  exact Option.isNone_iff_eq_none.mp (Hwfgenold v Hold)


/-- Positional decomposition for `Map.find?` against the L6 canonical
    `createOldVarsSubst` map.  Given a hit
    `Map.find? (createOldVarsSubst (...zip-form...)) k = some w`, extract
    the positional witness `i < oldVars.length` together with the shape
    facts `k = mkOld oldVars[i].name` and `w = createFvar genOldIdents[i]`.

    Absorbs the verbatim ~125-LoC `HCanonLen → Hni_lt → HtripGet → Htrip_shape →
    HoldG_get → HgoEq → HkwEq → Hk_eq / Hw_eq` chain that recurs at three
    `createOldVarsSubst`-flavoured sites in `callElimStatementCorrect`
    (`HoldSubBridge`, `Hinv` class-(b1), `Hpred_disj` class-(b1)). -/
private theorem createOldVarsSubst_pos_decomp
    {genOldIdents : List Expression.Ident}
    {oldTys : List Lambda.LTy}
    {oldVars : List Expression.Ident}
    (HgenOldLen : genOldIdents.length = oldVars.length)
    (HoldTysLen : oldTys.length = oldVars.length)
    {k : Expression.Ident} {w : Expression.Expr}
    (Hf : Map.find?
      (Core.Transform.createOldVarsSubst
        ((((genOldIdents.zip oldTys).zip oldVars).zip
          (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
            (fun (((fresh, ty), _orig), oldG) =>
              ((fresh, ty), oldG)))) k = some w) :
    ∃ (i : Nat) (Hi : i < oldVars.length),
      k = CoreIdent.mkOld (oldVars[i]'Hi).name ∧
      w = Core.Transform.createFvar
            (genOldIdents[i]'(by rw [HgenOldLen]; exact Hi)) := by
  -- Local abbreviations matching the call-site canonical names.
  let oldGVars : List Expression.Ident :=
    oldVars.map (fun g => CoreIdent.mkOld g.name)
  let oldTripsCanonical :
      List ((Expression.Ident × Expression.Ty) × Expression.Ident) :=
    (((genOldIdents.zip oldTys).zip oldVars).zip oldGVars).map
      (fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG))
  -- Bring `Hf` into the canonical-named form.
  have Hf : Map.find?
      (Core.Transform.createOldVarsSubst oldTripsCanonical) k = some w := Hf
  -- (k, w) ∈ createOldVarsSubst oldTripsCanonical (as List).
  have Hkw_mem_list :
      List.Mem (k, w)
        (Core.Transform.createOldVarsSubst oldTripsCanonical) :=
    Map.find?_mem _ k w Hf
  -- createOldVarsSubst trips = trips.map go (definitional).
  have HsubstUnfold :
      Core.Transform.createOldVarsSubst oldTripsCanonical =
        oldTripsCanonical.map
          (fun trip => Core.Transform.createOldVarsSubst.go trip) := rfl
  rw [HsubstUnfold] at Hkw_mem_list
  rcases List.mem_map.mp Hkw_mem_list with ⟨trip, Htrip_in, Htrip_eq⟩
  rcases List.mem_iff_get.mp Htrip_in with ⟨ni, Hni⟩
  -- Length facts.
  have HoldGLen : oldGVars.length = oldVars.length := by
    show (oldVars.map _).length = oldVars.length
    simp [List.length_map]
  have HCanonLen : oldTripsCanonical.length = oldVars.length := by
    show ((((genOldIdents.zip oldTys).zip oldVars).zip oldGVars).map _).length
        = oldVars.length
    simp only [List.length_map, List.length_zip, HgenOldLen, HoldTysLen,
               HoldGLen]
    omega
  have Hni_lt : ni.val < oldVars.length := by
    have HiLt := ni.isLt
    omega
  -- Position-wise length facts.
  have HziptyLen :
      (genOldIdents.zip oldTys).length = oldVars.length := by
    simp [List.length_zip, HgenOldLen, HoldTysLen]
  have Hni_lt_zipty : ni.val < (genOldIdents.zip oldTys).length := by
    rw [HziptyLen]; exact Hni_lt
  have Hni_lt_oldGVars : ni.val < oldGVars.length := by
    show ni.val < (oldVars.map _).length
    simp [List.length_map]; exact Hni_lt
  have Hni_lt_genOld : ni.val < genOldIdents.length := by
    have := HgenOldLen; omega
  have Hni_lt_oldTys : ni.val < oldTys.length := by
    have := HoldTysLen; omega
  have Hni_lt_canon : ni.val < oldTripsCanonical.length := ni.isLt
  -- Project the canonical trip via two-step zip-getElem reduction.
  have HtripGet :
      oldTripsCanonical[ni.val]'Hni_lt_canon =
        ((genOldIdents[ni.val]'Hni_lt_genOld,
          oldTys[ni.val]'Hni_lt_oldTys),
         oldGVars[ni.val]'Hni_lt_oldGVars) := by
    show (((((genOldIdents.zip oldTys).zip oldVars).zip
      oldGVars).map _)[ni.val]'Hni_lt_canon) = _
    rw [List.getElem_map]
    have HouterLt :
        ni.val < (((genOldIdents.zip oldTys).zip oldVars).zip
            oldGVars).length := by
      simp only [List.length_zip]; omega
    have Houter :
        (((genOldIdents.zip oldTys).zip oldVars).zip
            oldGVars)[ni.val]'HouterLt =
          ((((genOldIdents.zip oldTys).zip oldVars))[ni.val]'(by
            simp [List.length_zip, HziptyLen]; exact Hni_lt),
           oldGVars[ni.val]'Hni_lt_oldGVars) :=
      List.getElem_zip
    rw [Houter]
    have Hmid :
        ((genOldIdents.zip oldTys).zip oldVars)[ni.val]'(by
          simp [List.length_zip, HziptyLen]; exact Hni_lt) =
          ((genOldIdents.zip oldTys)[ni.val]'Hni_lt_zipty,
           oldVars[ni.val]'Hni_lt) :=
      List.getElem_zip
    rw [Hmid]
    have Hinner :
        (genOldIdents.zip oldTys)[ni.val]'Hni_lt_zipty =
          (genOldIdents[ni.val]'Hni_lt_genOld,
           oldTys[ni.val]'Hni_lt_oldTys) :=
      List.getElem_zip
    rw [Hinner]
  have HtripEq_get :
      oldTripsCanonical[ni.val]'Hni_lt_canon = trip := by
    have HhE := Hni
    have HgetEq : oldTripsCanonical.get ni =
            oldTripsCanonical[ni.val]'Hni_lt_canon := rfl
    rw [HgetEq] at HhE
    exact HhE
  have Htrip_shape :
      trip = ((genOldIdents[ni.val]'Hni_lt_genOld,
               oldTys[ni.val]'Hni_lt_oldTys),
              oldGVars[ni.val]'Hni_lt_oldGVars) := by
    rw [← HtripEq_get]; exact HtripGet
  have HoldG_get :
      oldGVars[ni.val]'Hni_lt_oldGVars =
        CoreIdent.mkOld (oldVars[ni.val]'Hni_lt).name := by
    show (oldVars.map (fun g => CoreIdent.mkOld g.name))[ni.val]'_ = _
    rw [List.getElem_map]
  have HgoEq :
      Core.Transform.createOldVarsSubst.go trip =
        (oldGVars[ni.val]'Hni_lt_oldGVars,
         Core.Transform.createFvar
           (genOldIdents[ni.val]'Hni_lt_genOld)) := by
    rw [Htrip_shape]; rfl
  have HkwEq :
      (k, w) = (oldGVars[ni.val]'Hni_lt_oldGVars,
                Core.Transform.createFvar
                  (genOldIdents[ni.val]'Hni_lt_genOld)) := by
    rw [← HgoEq]; exact Htrip_eq.symm
  refine ⟨ni.val, Hni_lt, ?_, ?_⟩
  · -- k = mkOld oldVars[ni.val].name.
    have Hk_eq :
        k = oldGVars[ni.val]'Hni_lt_oldGVars :=
      ((Prod.mk.injEq _ _ _ _).mp HkwEq).1
    rw [Hk_eq, HoldG_get]
  · -- w = createFvar genOldIdents[ni.val].
    exact ((Prod.mk.injEq _ _ _ _).mp HkwEq).2

/-- Positional decomposition for `Map.find?` against the L6
    `inputOnlyOldSubst` map.  Given a hit
    `Map.find? (inputOnlyOldSubst inputs inputArgs outputs posts) k = some w`,
    extract the positional witness `ni < inputs.length` (with the
    matching `ni < inputArgs.length`) together with the shape facts
    `k = mkOld inputs[ni].name` and `w = inputArgs[ni]`, plus the
    guard byproduct `inputs[ni] ∉ outputs`.

    Absorbs the verbatim ~80-LoC `List.mem_filterMap` + `by_cases Hg` +
    positional `List.mem_iff_get` + `getElem_zip` chain that recurs at
    three `inputOnlyOldSubst`-flavoured sites in `callElimStatementCorrect`
    (`HinputSubBridge`, `Hinv` class-(b2), `Hpred_disj` class-(b2)).

    Mirror of `createOldVarsSubst_pos_decomp` for the input-only old
    substitution map. -/
private theorem inputOnlyOldSubst_pos_decomp
    {inputs : List Expression.Ident}
    {inputArgs : List Expression.Expr}
    {outputs : List Expression.Ident}
    {posts : List Expression.Expr}
    {k : Expression.Ident} {w : Expression.Expr}
    (Hf : Map.find?
      ((inputs.zip inputArgs).filterMap
        (fun (paramId, argExpr) =>
          let oldVar := CoreIdent.mkOld paramId.name
          if !outputs.contains paramId &&
             posts.any (fun e => Lambda.LExpr.freeVars e |>.any
               (fun (id, _) => id == oldVar))
          then some (oldVar, argExpr)
          else none)) k = some w) :
    ∃ (ni : Nat) (Hi : ni < inputs.length)
        (Hi' : ni < inputArgs.length),
      k = CoreIdent.mkOld (inputs[ni]'Hi).name ∧
      w = inputArgs[ni]'Hi' ∧
      (inputs[ni]'Hi) ∉ outputs := by
  -- (k, w) ∈ inputOnlyOldSubst (as List).
  have Hkw_mem_list :
      List.Mem (k, w)
        ((inputs.zip inputArgs).filterMap
          (fun (paramId, argExpr) =>
            let oldVar := CoreIdent.mkOld paramId.name
            if !outputs.contains paramId &&
               posts.any (fun e => Lambda.LExpr.freeVars e |>.any
                 (fun (id, _) => id == oldVar))
            then some (oldVar, argExpr)
            else none)) :=
    Map.find?_mem _ k w Hf
  -- Apply List.mem_filterMap to extract a witness pair.
  rcases List.mem_filterMap.mp Hkw_mem_list with
    ⟨pair, Hpair_in, Hpair_eq⟩
  -- Case-split on the guard.
  by_cases Hg :
      (!outputs.contains pair.fst &&
       posts.any
         (fun e => Lambda.LExpr.freeVars e |>.any
           (fun (id, _) => id == CoreIdent.mkOld pair.fst.name))) = true
  · -- guard = true branch.
    have Hpair_eq' :
        (CoreIdent.mkOld pair.fst.name, pair.snd) = (k, w) := by
      have HH := Hpair_eq
      simp only [Hg, if_true] at HH
      exact (Option.some_inj.mp HH)
    have Hk_eq : k = CoreIdent.mkOld pair.fst.name :=
      ((Prod.mk.injEq _ _ _ _).mp Hpair_eq').1.symm
    have Hw_eq : w = pair.snd :=
      ((Prod.mk.injEq _ _ _ _).mp Hpair_eq').2.symm
    -- pair ∈ inputs.zip inputArgs.
    rcases List.mem_iff_get.mp Hpair_in with ⟨ni, Hni⟩
    have Hni_lt_zip :
        ni.val < (inputs.zip inputArgs).length := ni.isLt
    have HzipLen : (inputs.zip inputArgs).length =
          min inputs.length inputArgs.length :=
      List.length_zip
    have Hni_lt_min :
        ni.val < min inputs.length inputArgs.length := by
      rw [← HzipLen]; exact Hni_lt_zip
    have Hni_lt_inputs : ni.val < inputs.length := by
      have := Hni_lt_min; omega
    have Hni_lt_inputArgs : ni.val < inputArgs.length := by
      have := Hni_lt_min; omega
    -- Project pair to its components positionally.
    have HpairGet :
        (inputs.zip inputArgs)[ni.val]'Hni_lt_zip =
          (inputs[ni.val]'Hni_lt_inputs,
           inputArgs[ni.val]'Hni_lt_inputArgs) :=
      List.getElem_zip
    have HpairEq_get :
        (inputs.zip inputArgs)[ni.val]'Hni_lt_zip = pair := by
      have Hge : (inputs.zip inputArgs).get ni =
            (inputs.zip inputArgs)[ni.val]'Hni_lt_zip := rfl
      rw [Hge] at Hni
      exact Hni
    have Hpair_shape :
        pair = (inputs[ni.val]'Hni_lt_inputs,
                inputArgs[ni.val]'Hni_lt_inputArgs) := by
      rw [← HpairEq_get]; exact HpairGet
    have Hpair_fst : pair.fst = inputs[ni.val]'Hni_lt_inputs := by
      rw [Hpair_shape]
    have Hpair_snd : pair.snd = inputArgs[ni.val]'Hni_lt_inputArgs := by
      rw [Hpair_shape]
    -- Extract `inputs[ni.val] ∉ outputs` from the guard.
    have Hin_notin_outs : (inputs[ni.val]'Hni_lt_inputs) ∉ outputs := by
      have HgL : (!outputs.contains pair.fst) = true :=
        (Bool.and_eq_true _ _).mp Hg |>.1
      have HgL2 : outputs.contains pair.fst = false := by
        have := HgL
        simp only [Bool.not_eq_true'] at this
        exact this
      have HgL3 : pair.fst ∉ outputs := by
        intro Hin
        have := List.contains_iff_mem.mpr Hin
        rw [HgL2] at this
        exact Bool.false_ne_true this
      rw [← Hpair_fst]
      exact HgL3
    refine ⟨ni.val, Hni_lt_inputs, Hni_lt_inputArgs, ?_, ?_, Hin_notin_outs⟩
    · -- k = mkOld inputs[ni.val].name.
      rw [Hk_eq, Hpair_fst]
    · -- w = inputArgs[ni.val].
      rw [Hw_eq, Hpair_snd]
  · -- guard = false: contradiction.
    have HH := Hpair_eq
    simp only [Hg] at HH
    exact absurd HH (by simp)

/-- For an entry of `conds.filter f`, its `.snd.expr` is contained in
    `getCheckExprs conds` (in `.contains` form).  Used at both the
    pre-filtered and post-filtered sites of `callElimStatementCorrect` to
    bridge filter membership to the `.contains` argument expected by the
    `Hpre`/`Hpost` hypotheses from `call_sem`. -/
private theorem filterCheck_in_getCheckExprs [LawfulBEq Expression.Expr]
    {conds : ListMap CoreLabel Procedure.Check}
    {f : CoreLabel × Procedure.Check → Bool}
    {entry : CoreLabel × Procedure.Check}
    (Hentry : entry ∈ conds.filter f) :
    (Procedure.Spec.getCheckExprs conds).contains entry.snd.expr := by
  have Hin_full := (List.mem_filter.mp Hentry).1
  apply List.contains_iff_mem.mpr
  simp only [Procedure.Spec.getCheckExprs, List.mem_map]
  refine ⟨entry.snd, ?_, rfl⟩
  rw [ListMap.values_eq_map_snd]
  exact List.mem_map_of_mem Hin_full

/-- Membership form of `filterCheck_in_getCheckExprs`: the entry's
    `.snd.expr` lies in `getCheckExprs conds` (as a `List` membership
    predicate, not the `.contains` boolean form). -/
private theorem filterCheck_mem_getCheckExprs
    {conds : ListMap CoreLabel Procedure.Check}
    {f : CoreLabel × Procedure.Check → Bool}
    {entry : CoreLabel × Procedure.Check}
    (Hentry : entry ∈ conds.filter f) :
    entry.snd.expr ∈ Procedure.Spec.getCheckExprs conds := by
  have Hin_full := (List.mem_filter.mp Hentry).1
  simp only [Procedure.Spec.getCheckExprs, List.mem_map]
  refine ⟨entry.snd, ?_, rfl⟩
  rw [ListMap.values_eq_map_snd]
  exact List.mem_map_of_mem Hin_full

/-- Store-agreement helper for `σ_R1`-style stacks (the σ_R1 layer
    overlaying `genOldIdents ↦ oldVals` on σO, plus the σO ← σAO ←
    σA ← σ chain from havoc + InitStates).

    For any identifier `v` not touched by any layer, all four stores
    agree: `updatedStates σO genOldIds oldVals v = σ v`.  Used at three
    sites in `callElimStatementCorrect` (D2c "argExpr survives" branches
    and the L6 `Hinv` derivations). -/
private theorem σR1_eq_σ_for_notTouched
    {σ σA σAO σO : CoreStore}
    {ins outs genOldIds : List Expression.Ident}
    {argVals oVals oldVals : List Expression.Expr}
    (Hinitin : InitStates σ ins argVals σA)
    (Hinitout : InitStates σA outs oVals σAO)
    (Hhav : HavocVars σAO outs σO)
    {v : Expression.Ident}
    (HvNotIns : v ∉ ins)
    (HvNotOuts : v ∉ outs)
    (HvNotGen : v ∉ genOldIds) :
    updatedStates σO genOldIds oldVals v = σ v := by
  rw [updatedStates_get_notin HvNotGen]
  rcases HavocVarsUpdateStates Hhav with ⟨ovh, Hup_havoc⟩
  have HσO_eq : σO = updatedStates σAO outs ovh := UpdateStatesUpdated Hup_havoc
  rw [HσO_eq, updatedStates_get_notin HvNotOuts,
      initStates_get_notin Hinitout HvNotOuts,
      initStates_get_notin Hinitin HvNotIns]

/-- No-throw fact for the `oldTys ← oldVars.mapM ...` step inside
    `callElimCmd`.  When every `g ∈ oldVars` already appears as a key in
    `proc.header.inputs`, the `find?`-driven lookup never hits the
    `throw` branch, so the whole `mapM` reduces to an `Except.ok` with a
    `oldTys` list whose length matches `oldVars`.

    This is one of the no-throw lemmas needed by
    `callElimCmd_call_eq` (B3) to refute the `Except.error` branches in
    the post-`outTrips` layers.  By construction the `oldVars` produced
    inside `callElimCmd` is `lhs.filter (fun g => inputNames.contains g
    && ...)`, so the `Holdvars_in_inputs` precondition is immediate at
    the call site. -/
private theorem oldVars_oldTys_mapM_ok
    {proc : Procedure}
    {oldVars : List Expression.Ident}
    {γ : CoreTransformState}
    (Holdvars_in_inputs :
      ∀ g ∈ oldVars, (ListMap.keys proc.header.inputs).contains g) :
    ∃ (oldTys : List (Lambda.LTy)) (γ' : CoreTransformState),
      (oldVars.mapM (m:=CoreTransformM) (oldTyLookupCallElim proc))
        γ
        = (Except.ok oldTys, γ') ∧
      oldTys.length = oldVars.length := by
  -- Bridge: `keys.contains g = true` gives `find? g = some _`.
  -- Use the contrapositive of `ListMap.find?_of_not_mem_values`:
  --   `find? = none → g ∉ keys`, so `g ∈ keys → find? ≠ none`.
  have Hfind_some :
      ∀ (m : ListMap Expression.Ident Lambda.LMonoTy)
        (g : Expression.Ident),
        (ListMap.keys m).contains g = true →
          ∃ v, ListMap.find? m g = some v := by
    intro m g Hcontains
    have Hmem : g ∈ ListMap.keys m := List.contains_iff_mem.mp Hcontains
    cases hf : ListMap.find? m g with
    | none =>
      have := ListMap.find?_of_not_mem_values m hf
      exact absurd Hmem this
    | some v => exact ⟨v, rfl⟩
  -- Induct on `oldVars`; threading the state explicitly.
  induction oldVars generalizing γ with
  | nil =>
    refine ⟨[], γ, ?_, rfl⟩
    simp [List.mapM_nil, pure, ExceptT.pure, StateT.pure, ExceptT.mk]
  | cons g rest ih =>
    -- Head: lookup succeeds via `Holdvars_in_inputs`.
    have Hg_in : (ListMap.keys proc.header.inputs).contains g = true := by
      exact Holdvars_in_inputs g (by simp)
    obtain ⟨ty, Hty⟩ := Hfind_some proc.header.inputs g Hg_in
    -- Tail: IH applies because `Holdvars_in_inputs` weakens.
    have Hrest : ∀ g' ∈ rest, (ListMap.keys proc.header.inputs).contains g' = true :=
      fun g' Hin => Holdvars_in_inputs g' (List.mem_cons_of_mem _ Hin)
    obtain ⟨tys', γ'', Heqtail, Hlen⟩ := ih Hrest (γ := γ)
    refine ⟨Lambda.LTy.forAll [] ty :: tys', γ'', ?_, ?_⟩
    · -- Unfold mapM_cons and chain the head match through to the tail mapM.
      -- Strategy: unfold the bind shell and `pure` in both the goal and
      -- `Heqtail` so the inner-mapM call is in a matching form, then `rw`.
      simp only [List.mapM_cons, oldTyLookupCallElim,
                 bind, ExceptT.bind, ExceptT.bindCont,
                 ExceptT.mk, StateT.bind,
                 pure, ExceptT.pure, StateT.pure, Hty]
      simp only [pure, ExceptT.pure, StateT.pure, ExceptT.mk] at Heqtail
      rw [Heqtail]
      rfl
    · simp [Hlen]

/-- No-throw fact for `Core.Transform.createAsserts`.  The body of its
    inner `mapM` only invokes `genIdent` (a pure state mutation that
    cannot throw) followed by a `return`, so the entire computation
    always reduces to `Except.ok asserts` for some asserts list whose
    length matches `conds`.

    This is the second of three "no-throw" lemmas needed by
    `callElimCmd_call_eq` (B3) to refute the `Except.error` branches
    in the post-`outTrips` layers.

    The lemma deliberately does NOT bridge to `createAsserts_list`
    (the pure-list pure analogue used in earlier lemmas).  The
    monadic version produces counter-based labels (e.g. `assert_pre0_5`)
    while `createAsserts_list` produces index-based labels
    (e.g. `assert_0_pre0`); the two strings differ.  Fortunately,
    `EvalCmd.eval_assert_pass` ignores the label entirely, so the
    label discrepancy is irrelevant to the contract derivation.  The
    length fact below is sufficient for the call-site reasoning.

    The `asserts_shape` conjunct exposes the list as a `conds.map`-shape
    over an existential `labelOf`, which is what the label-agnostic
    `H_asserts_anylist` consumes downstream. -/
private theorem createAsserts_ok
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String)
    (γ : CoreTransformState) :
    ∃ (asserts : List Statement) (γ' : CoreTransformState),
      Core.Transform.createAsserts conds subst md labelPrefix γ
        = (Except.ok asserts, γ') ∧
      asserts.length = conds.length ∧
      ∃ (labels : List String), labels.length = conds.length ∧
        asserts = (conds.zip labels).map (fun (entry, lbl) =>
          Statement.assert lbl
            (Lambda.LExpr.substFvars entry.snd.expr subst)
            (entry.snd.md.setCallSiteFileRange md)) := by
  unfold Core.Transform.createAsserts
  -- `ListMap α β := List (α × β)`, so `conds.mapM` is `List.mapM` over
  -- the underlying list.  Induct on that list, threading the state.
  induction conds generalizing γ with
  | nil =>
    refine ⟨[], γ, ?_, rfl, [], rfl, ?_⟩
    · simp [List.mapM_nil, pure, ExceptT.pure, StateT.pure, ExceptT.mk]
    · simp
  | cons head rest ih =>
    obtain ⟨l, check⟩ := head
    -- Head: genIdent always succeeds, producing a label and updated state.
    cases hgi : Core.Transform.genIdent l (fun s => s!"{labelPrefix}{s}") γ.genState with
    | mk newLabel γgen' =>
      -- The post-genIdent CoreTransformState (genState updated, rest preserved).
      let γhead : CoreTransformState :=
        { genState := γgen',
          currentProgram := γ.currentProgram,
          currentProcedureName := γ.currentProcedureName,
          cachedAnalyses := γ.cachedAnalyses,
          factory := γ.factory,
          statistics := γ.statistics }
      obtain ⟨asserts', γ'', Heqtail, Hlen, labelsTail, HlblsLen, Hshape⟩ := ih (γ := γhead)
      refine ⟨Statement.assert newLabel.toPretty
                (Lambda.LExpr.substFvars check.expr subst)
                (check.md.setCallSiteFileRange md) :: asserts', γ'', ?_, ?_, ?_⟩
      · -- Reduce both sides to the same `List.mapM` core, then chain via Heqtail.
        -- Apply the same simp set on both the goal and Heqtail so the inner-mapM
        -- shape matches.
        simp only [List.mapM_cons, bind, ExceptT.bind, ExceptT.bindCont,
                   ExceptT.mk, ExceptT.lift, ExceptT.pure,
                   StateT.bind, StateT.pure, pure,
                   monadLift, MonadLift.monadLift, liftM,
                   Functor.map, StateT.map, liftCoreGenM, hgi]
        simp only [bind, ExceptT.bind,
                   ExceptT.mk, ExceptT.lift, ExceptT.pure,
                   pure,
                   monadLift, MonadLift.monadLift, liftM,
                   Functor.map] at Heqtail
        rw [Heqtail]
        rfl
      · simp [Hlen]
      · refine ⟨newLabel.toPretty :: labelsTail, ?_, ?_⟩
        · simp [HlblsLen]
        · simp only [List.zip_cons_cons, List.map_cons]
          rw [Hshape]

/-- No-throw fact for `Core.Transform.createAssumes`.  Mirror of
    `createAsserts_ok` for the assume case.  Same `genIdent`-only
    structure, same conclusion, same caveats about labels. -/
private theorem createAssumes_ok
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String)
    (γ : CoreTransformState) :
    ∃ (assumes : List Statement) (γ' : CoreTransformState),
      Core.Transform.createAssumes conds subst md labelPrefix γ
        = (Except.ok assumes, γ') ∧
      assumes.length = conds.length ∧
      ∃ (labels : List String), labels.length = conds.length ∧
        assumes = (conds.zip labels).map (fun (entry, lbl) =>
          Statement.assume lbl
            (Lambda.LExpr.substFvars entry.snd.expr subst)
            (entry.snd.md.setCallSiteFileRange md)) := by
  unfold Core.Transform.createAssumes
  induction conds generalizing γ with
  | nil =>
    refine ⟨[], γ, ?_, rfl, [], rfl, ?_⟩
    · simp [List.mapM_nil, pure, ExceptT.pure, StateT.pure, ExceptT.mk]
    · simp
  | cons head rest ih =>
    obtain ⟨l, check⟩ := head
    cases hgi : Core.Transform.genIdent l (fun s => s!"{labelPrefix}{s}") γ.genState with
    | mk newLabel γgen' =>
      let γhead : CoreTransformState :=
        { genState := γgen',
          currentProgram := γ.currentProgram,
          currentProcedureName := γ.currentProcedureName,
          cachedAnalyses := γ.cachedAnalyses,
          factory := γ.factory,
          statistics := γ.statistics }
      obtain ⟨assumes', γ'', Heqtail, Hlen, labelsTail, HlblsLen, Hshape⟩ := ih (γ := γhead)
      refine ⟨Statement.assume newLabel.toPretty
                (Lambda.LExpr.substFvars check.expr subst)
                (check.md.setCallSiteFileRange md) :: assumes', γ'', ?_, ?_, ?_⟩
      · -- Reduce both sides to the same `List.mapM` core, then chain via Heqtail.
        simp only [List.mapM_cons, bind, ExceptT.bind, ExceptT.bindCont,
                   ExceptT.mk, ExceptT.lift, ExceptT.pure,
                   StateT.bind, StateT.pure, pure,
                   monadLift, MonadLift.monadLift, liftM,
                   Functor.map, StateT.map, liftCoreGenM, hgi]
        simp only [bind, ExceptT.bind,
                   ExceptT.mk, ExceptT.lift, ExceptT.pure,
                   pure,
                   monadLift, MonadLift.monadLift, liftM,
                   Functor.map] at Heqtail
        rw [Heqtail]
        rfl
      · simp [Hlen]
      · refine ⟨newLabel.toPretty :: labelsTail, ?_, ?_⟩
        · simp [HlblsLen]
        · simp only [List.zip_cons_cons, List.map_cons]
          rw [Hshape]

/-- Internal-shape destructuring of a successful `callElimCmd` call.

    The B1 phase of `callElimStatementCorrect` needs to bind the
    `argTrips`, `outTrips`, `genOldIdents`, `oldTys`, `asserts`,
    `assumes` and intermediate gen states produced inside
    `callElimCmd`'s `do` block, plus a procedure-lookup result and
    the structural equation `sts' = argInit ++ outInit ++ oldInit ++
    asserts ++ havocs ++ assumes`.  Because the inner
    `bind`/`ExceptT.bindCont` envelope does not normalize
    syntactically to a bare `match`, the destructuring is factored
    through this helper so the call site stays clean.

    The input state is constrained to have `currentProgram := some p`
    (which is the post-`modify` shape produced by `callElimStmt`'s
    outer `runWith`).

    The helper exposes everything the call site needs to subst the
    structural equation and continue with L1-L6 reasoning.  Internal
    state names `s_arg/s_out/s_old/s_postold/s_assert/s_assume` are
    threaded through; only state-shape relevant downstream are retained.
-/
private theorem callElimCmd_call_eq
    {procName : String} {args : List (CallArg Expression)}
    {md : Imperative.MetaData Expression}
    {γ : CoreTransformState}
    {γ_out : CoreTransformState}
    {p : Program}
    {sts' : List Statement}
    (Heq : (callElimCmd (CmdExt.call procName args md))
              { γ with currentProgram := some p }
            = (Except.ok (some sts'), γ_out)) :
    ∃ proc argTrips outTrips genOldIdents oldTys asserts assumes
       s_arg s_out s_old,
      Program.Procedure.find? p ⟨procName, ()⟩ = some proc ∧
      genArgExprIdentsTrip
          (Lambda.LMonoTySignature.toTrivialLTy proc.header.inputs)
          (CallArg.getInputExprs args)
          { γ with currentProgram := some p,
                   statistics := γ.statistics.increment
                     (toString CallElim.Stats.visitedCalls) 1 }
        = (Except.ok argTrips, s_arg) ∧
      genOutExprIdentsTrip
          (Lambda.LMonoTySignature.toTrivialLTy proc.header.outputs)
          (CallArg.getLhs args) s_arg
        = (Except.ok outTrips, s_out) ∧
      genOldExprIdents
        (List.filter
          (fun g =>
            (ListMap.keys proc.header.inputs).contains g &&
                (ListMap.keys proc.header.outputs).contains g &&
              (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
          (CallArg.getLhs args))
        s_out.genState
        = (genOldIdents, s_old) ∧
      oldTys.length =
        (List.filter
          (fun g =>
            (ListMap.keys proc.header.inputs).contains g &&
                (ListMap.keys proc.header.outputs).contains g &&
              (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
          (CallArg.getLhs args)).length ∧
      sts' =
        Core.Transform.createInits argTrips md ++
        Core.Transform.createInitVars outTrips md ++
        Core.Transform.createInitVars
          ((genOldIdents.zip oldTys).zip
            (List.filter
              (fun g =>
                (ListMap.keys proc.header.inputs).contains g &&
                    (ListMap.keys proc.header.outputs).contains g &&
                  (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                    List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
              (CallArg.getLhs args)))
          md ++
        asserts ++
        Core.Transform.createHavocs (CallArg.getLhs args) md ++
        assumes ∧
      -- Structural shape of `asserts`:  abstract `pres.zip labels` map.
      (∃ (assertLabels : List String),
        let pres := (proc.spec.preconditions.filter
                       (fun (_, check) => check.attr != .Free))
        let assertSubst :=
              ((ListMap.keys proc.header.inputs).zip
                (Core.Transform.createFvars argTrips.unzip.fst.unzip.fst) ++
              (ListMap.keys proc.header.outputs).zip
                (Core.Transform.createFvars (CallArg.getLhs args)))
        assertLabels.length = pres.length ∧
        asserts = (pres.zip assertLabels).map (fun (entry, lbl) =>
          Statement.assert lbl
            (Lambda.LExpr.substFvars entry.snd.expr assertSubst)
            (entry.snd.md.setCallSiteFileRange md))) ∧
      -- Structural shape of `assumes`:  abstract `posts.zip labels` map.
      (∃ (assumeLabels : List String),
        let inputOnlyOldSubst : Map Expression.Ident Expression.Expr :=
              (proc.header.inputs.keys.zip (CallArg.getInputExprs args)).filterMap
                fun (paramId, argExpr) =>
                  let oldVar := CoreIdent.mkOld paramId.name
                  if !(ListMap.keys proc.header.outputs).contains paramId &&
                     (proc.spec.postconditions.values.map Procedure.Check.expr).any
                       (fun e => Lambda.LExpr.freeVars e |>.any
                         (fun (id, _) => id == oldVar))
                  then some (oldVar, argExpr)
                  else none
        let oldTripsCanonical :=
              (((genOldIdents.zip oldTys).zip
                (List.filter
                  (fun g =>
                    (ListMap.keys proc.header.inputs).contains g &&
                        (ListMap.keys proc.header.outputs).contains g &&
                      (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                        List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
                  (CallArg.getLhs args))).zip
              ((List.filter
                (fun g =>
                  (ListMap.keys proc.header.inputs).contains g &&
                      (ListMap.keys proc.header.outputs).contains g &&
                    (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                      List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
                (CallArg.getLhs args)).map (fun g => CoreIdent.mkOld g.name))).map
              fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)
        let oldSubst : Map Expression.Ident Expression.Expr :=
              Core.Transform.createOldVarsSubst oldTripsCanonical ++ inputOnlyOldSubst
        let posts := Procedure.Spec.updateCheckExprs
                       (proc.spec.postconditions.values.map
                         (fun c => Lambda.LExpr.substFvars c.expr oldSubst))
                       proc.spec.postconditions
        let assumeSubst :=
              ((ListMap.keys proc.header.outputs).zip
                (Core.Transform.createFvars (CallArg.getLhs args)) ++
              ((ListMap.keys proc.header.inputs).zip
                (Core.Transform.createFvars argTrips.unzip.fst.unzip.fst)).filter
                  (fun (id, _) => !(ListMap.keys proc.header.outputs).contains id))
        assumeLabels.length = posts.length ∧
        assumes = (posts.zip assumeLabels).map (fun (entry, lbl) =>
          Statement.assume lbl
            (Lambda.LExpr.substFvars entry.snd.expr assumeSubst)
            (entry.snd.md.setCallSiteFileRange md))) := by
  -- Unfold `callElimCmd`'s `do` block step-by-step.  The first action
  -- is `incrementStat` (a `modify`), then `(← get).currentProgram` is
  -- matched.  Because we passed `{γ with currentProgram := some p}`,
  -- we can compute the post-increment state explicitly.
  unfold callElimCmd at Heq
  simp only [incrementStat, modify, modifyGet, MonadStateOf.modifyGet,
             MonadState.modifyGet, StateT.modifyGet,
             bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
             pure, ExceptT.pure, StateT.pure,
             get, getThe, MonadStateOf.get, MonadState.get, StateT.get,
             monadLift, MonadLift.monadLift, liftM, ExceptT.lift,
             Functor.map, StateT.map] at Heq
  cases hfind : Program.Procedure.find? p ⟨procName, ()⟩ with
  | none =>
      rw [hfind] at Heq
      exact absurd Heq (by intro h; cases h)
  | some proc =>
      rw [hfind] at Heq
      simp only [bind, StateT.bind, ExceptT.bind, ExceptT.bindCont,
                 ExceptT.mk, pure, StateT.pure] at Heq
      generalize Heqarg :
        (genArgExprIdentsTrip
          (Lambda.LMonoTySignature.toTrivialLTy proc.header.inputs)
          (CallArg.getInputExprs args)
          { γ with currentProgram := some p,
                   statistics := γ.statistics.increment
                     (toString CallElim.Stats.visitedCalls) 1 }) =
            pair_arg at Heq
      cases pair_arg with
      | mk res_arg s_arg =>
        cases res_arg with
        | error e =>
            exact absurd Heq (by intro h; cases h)
        | ok argTrips =>
            simp only [bind, StateT.bind, ExceptT.bind, ExceptT.bindCont,
                       ExceptT.mk, pure, StateT.pure] at Heq
            generalize Heqout :
              (genOutExprIdentsTrip
                (Lambda.LMonoTySignature.toTrivialLTy proc.header.outputs)
                (CallArg.getLhs args) s_arg) = pair_out at Heq
            cases pair_out with
            | mk res_out s_out =>
              cases res_out with
              | error e =>
                  exact absurd Heq (by intro h; cases h)
              | ok outTrips =>
                  -- Now extract `genOldIdents` from the next layer.
                  -- The next layer is `(StateT.map Except.ok
                  --   (liftCoreGenM (genOldExprIdents oldVars))).bind ...`.
                  simp only [liftCoreGenM, bind, StateT.bind,
                             ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
                             pure, ExceptT.pure, StateT.pure,
                             Functor.map, StateT.map] at Heq
                  generalize Heqold :
                    (genOldExprIdents
                      (List.filter
                        (fun g =>
                          (ListMap.keys proc.header.inputs).contains g &&
                              (ListMap.keys proc.header.outputs).contains g &&
                            (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                              List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
                        (CallArg.getLhs args))
                      s_out.genState) = pair_old at Heq
                  cases pair_old with
                  | mk genOldIdents s_old =>
                    -- B1: oldTys ← oldVars.mapM (oldVars ⊆ inputs.keys).
                    have Holdvars_in_inputs :
                        ∀ g ∈ (List.filter
                              (fun g =>
                                (ListMap.keys proc.header.inputs).contains g &&
                                    (ListMap.keys proc.header.outputs).contains g &&
                                  (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                                    List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
                              (CallArg.getLhs args)),
                          (ListMap.keys proc.header.inputs).contains g := by
                      intro g Hg
                      have Hfilt : _ ∧ _ := List.mem_filter.mp Hg
                      have Hcond : _ = true := Hfilt.2
                      simp only [Bool.and_eq_true] at Hcond
                      exact Hcond.1.1
                    obtain ⟨oldTys, s_postold, Heqty, _Hlenty⟩ :=
                      oldVars_oldTys_mapM_ok (γ := { s_out with genState := s_old })
                        Holdvars_in_inputs
                    -- Reduce `pure`/`throw` to match Heq.
                    simp only [bind, StateT.bind, ExceptT.bind,
                               ExceptT.bindCont, ExceptT.mk] at Heq
                    have HeqtyR : _ := Heqty
                    simp only [pure, ExceptT.pure, StateT.pure,
                               ExceptT.mk] at HeqtyR
                    rw [HeqtyR] at Heq
                    simp only [bind, StateT.bind, ExceptT.bind,
                               ExceptT.bindCont, ExceptT.mk,
                               pure, ExceptT.pure, StateT.pure] at Heq
                    -- ── B2 layer: asserts ← createAsserts ... ──
                    obtain ⟨asserts, s_assert, Heqas, _Hlenas,
                            assertLabels, HassertLabelsLen, HassertShape⟩ :=
                      createAsserts_ok
                        (proc.spec.preconditions.filter (fun (_, check) => check.attr != .Free))
                        ((ListMap.keys proc.header.inputs).zip
                          (Core.Transform.createFvars argTrips.unzip.fst.unzip.fst) ++
                         (ListMap.keys proc.header.outputs).zip
                          (Core.Transform.createFvars (CallArg.getLhs args)))
                        md
                        callElimAssertPrefix
                        s_postold
                    rw [Heqas] at Heq
                    simp only [bind, StateT.bind, ExceptT.bind,
                               ExceptT.bindCont, ExceptT.mk,
                               pure, ExceptT.pure, StateT.pure] at Heq
                    -- B2: assumes ← createAssumes (oldSubst helper).
                    let inputOnlyOldSubst : Map Expression.Ident Expression.Expr :=
                      (proc.header.inputs.keys.zip (CallArg.getInputExprs args)).filterMap
                        fun (paramId, argExpr) =>
                          let oldVar := CoreIdent.mkOld paramId.name
                          if !(ListMap.keys proc.header.outputs).contains paramId &&
                             (proc.spec.postconditions.values.map Procedure.Check.expr).any
                               (fun e => Lambda.LExpr.freeVars e |>.any
                                 (fun (id, _) => id == oldVar))
                          then some (oldVar, argExpr)
                          else none
                    let oldTrips :=
                      (((genOldIdents.zip oldTys).zip
                        (List.filter
                          (fun g =>
                            (ListMap.keys proc.header.inputs).contains g &&
                                (ListMap.keys proc.header.outputs).contains g &&
                              (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                                List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
                          (CallArg.getLhs args))).zip
                      ((List.filter
                        (fun g =>
                          (ListMap.keys proc.header.inputs).contains g &&
                              (ListMap.keys proc.header.outputs).contains g &&
                            (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
                              List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
                        (CallArg.getLhs args)).map (fun g => CoreIdent.mkOld g.name))).map
                      fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)
                    let oldSubst : Map Expression.Ident Expression.Expr :=
                      Core.Transform.createOldVarsSubst oldTrips ++ inputOnlyOldSubst
                    obtain ⟨assumes, s_assume, Heqasm, _Hlenasm,
                            assumeLabels, HassumeLabelsLen, HassumeShape⟩ :=
                      createAssumes_ok
                        (Procedure.Spec.updateCheckExprs
                          (proc.spec.postconditions.values.map
                            (fun c => Lambda.LExpr.substFvars c.expr oldSubst))
                          proc.spec.postconditions)
                        ((ListMap.keys proc.header.outputs).zip
                          (Core.Transform.createFvars (CallArg.getLhs args)) ++
                         ((ListMap.keys proc.header.inputs).zip
                            (Core.Transform.createFvars argTrips.unzip.fst.unzip.fst)).filter
                              (fun (id, _) => !(ListMap.keys proc.header.outputs).contains id))
                        md
                        callElimAssumePrefix
                        s_assert
                    rw [Heqasm] at Heq
                    simp only [bind, StateT.bind, ExceptT.bind,
                               ExceptT.bindCont, ExceptT.mk,
                               pure, ExceptT.pure, StateT.pure,
                               get, getThe, MonadStateOf.get,
                               MonadState.get, StateT.get,
                               set, MonadStateOf.set, StateT.set,
                               monadLift, MonadLift.monadLift, liftM,
                               ExceptT.lift, Functor.map,
                               StateT.map] at Heq
                    -- ── Callgraph update ──
                    -- `match σ.cachedAnalyses.callGraph, σ.currentProcedureName`.
                    -- We split on both branches.  The first branch may
                    -- throw via decrementEdge; refute that case.
                    refine ⟨proc, argTrips, outTrips, genOldIdents, oldTys,
                            asserts, assumes,
                            s_arg, s_out, s_old,
                            rfl, Heqarg, Heqout, Heqold, _Hlenty, ?_,
                            ⟨assertLabels, HassertLabelsLen, HassertShape⟩,
                            ⟨assumeLabels, HassumeLabelsLen, HassumeShape⟩⟩
                    · -- Structural equation: split on callgraph match,
                      -- then read off `sts' = ...`.  Use a single simp
                      -- set that unfolds `set`/`StateT.set`/`StateT.map`
                      -- so the post-callgraph pure-return reduces to a
                      -- raw `(Except.ok (List ...), state)` pair.
                      cases hcg : s_assume.cachedAnalyses.callGraph with
                      | none =>
                        cases hcpn : s_assume.currentProcedureName with
                        | none =>
                          rw [hcg, hcpn] at Heq
                          simp only [pure, ExceptT.pure, StateT.pure,
                                     bind, StateT.bind, ExceptT.bind,
                                     ExceptT.bindCont, ExceptT.mk,
                                     set, MonadStateOf.set, StateT.set,
                                     Functor.map, StateT.map] at Heq
                          have Hpair := Prod.mk.injEq _ _ _ _ |>.mp Heq
                          have Hexc := Except.ok.injEq _ _ |>.mp Hpair.1
                          have Hopt := Option.some.injEq _ _ |>.mp Hexc
                          exact Hopt.symm
                        | some _ =>
                          rw [hcg, hcpn] at Heq
                          simp only [pure, ExceptT.pure, StateT.pure,
                                     bind, StateT.bind, ExceptT.bind,
                                     ExceptT.bindCont, ExceptT.mk,
                                     set, MonadStateOf.set, StateT.set,
                                     Functor.map, StateT.map] at Heq
                          have Hpair := Prod.mk.injEq _ _ _ _ |>.mp Heq
                          have Hexc := Except.ok.injEq _ _ |>.mp Hpair.1
                          have Hopt := Option.some.injEq _ _ |>.mp Hexc
                          exact Hopt.symm
                      | some cg =>
                        cases hcpn : s_assume.currentProcedureName with
                        | none =>
                          rw [hcg, hcpn] at Heq
                          simp only [pure, ExceptT.pure, StateT.pure,
                                     bind, StateT.bind, ExceptT.bind,
                                     ExceptT.bindCont, ExceptT.mk,
                                     set, MonadStateOf.set, StateT.set,
                                     Functor.map, StateT.map] at Heq
                          have Hpair := Prod.mk.injEq _ _ _ _ |>.mp Heq
                          have Hexc := Except.ok.injEq _ _ |>.mp Hpair.1
                          have Hopt := Option.some.injEq _ _ |>.mp Hexc
                          exact Hopt.symm
                        | some callerName =>
                          rw [hcg, hcpn] at Heq
                          -- decrementEdge result inspected.
                          simp only [bind, StateT.bind, ExceptT.bind,
                                     ExceptT.bindCont, ExceptT.mk,
                                     pure, ExceptT.pure, StateT.pure,
                                     Functor.map, StateT.map,
                                     Except.mapError] at Heq
                          cases hde :
                            (cg.decrementEdge callerName procName) with
                          | error e =>
                            rw [hde] at Heq
                            simp only [Except.mapError, pure, ExceptT.pure,
                                       StateT.pure] at Heq
                            -- Heq is `(Except.error _, s_assume)
                            --        = (Except.ok (some sts'), γ_out)`
                            -- which is contradictory.
                            exact absurd Heq (by intro h; cases h)
                          | ok cg' =>
                            rw [hde] at Heq
                            simp only [Except.mapError, pure, ExceptT.pure,
                                       StateT.pure, bind, StateT.bind,
                                       ExceptT.bind, ExceptT.bindCont,
                                       ExceptT.mk, set, MonadStateOf.set,
                                       StateT.set,
                                       Functor.map, StateT.map] at Heq
                            have Hpair := Prod.mk.injEq _ _ _ _ |>.mp Heq
                            have Hexc := Except.ok.injEq _ _ |>.mp Hpair.1
                            have Hopt := Option.some.injEq _ _ |>.mp Hexc
                            exact Hopt.symm

/-- For every non-call statement `s`, the call-elimination transformer
    `callElimStmt s p` returns `[s]` unchanged.  This collapses what was
    eight identical simp blocks (one per `Statement` constructor that is
    not a `Cmd.call`) into a single uniform reduction.  Used by
    `callElimStatementCorrect` to dispatch the non-call branches. -/
private theorem callElimStmt_non_call_eq
    {p : Program} {γ γ' : CoreTransformState} {sts : List Statement}
    {s : Statement}
    (hne : ∀ procName args md, s ≠ .cmd (CmdExt.call procName args md))
    (hH : (Except.ok sts, γ') = (runWith s (callElimStmt · p) γ)) :
    sts = [s] := by
  -- All 7 non-call top-level cases (cmd.cmd, block, ite, loop, exit,
  -- funcDecl, typeDecl) reduce uniformly via the same simp set; the
  -- inner `cmd.call` case is discharged by `hne`.
  match s, hne, hH with
  | .cmd (.call procName args md), hne, _ =>
      exact absurd rfl (hne procName args md)
  | .cmd (.cmd _), _, hH
  | .block _ _ _, _, hH
  | .ite _ _ _ _, _, hH
  | .loop _ _ _ _ _, _, hH
  | .exit _ _, _, hH
  | .funcDecl _ _, _, hH
  | .typeDecl _ _, _, hH =>
      simp only [runWith, StateT.run, callElimStmt, bind, pure,
                 StateT.bind, ExceptT.bind, ExceptT.bindCont,
                 ExceptT.mk, ExceptT.pure, modify, modifyGet,
                 MonadStateOf.modifyGet, MonadState.modifyGet,
                 StateT.modifyGet, MonadStateOf.set,
                 monadLift, MonadLift.monadLift, liftM, ExceptT.lift,
                 StateT.pure, Functor.map, ExceptT.map, StateT.map,
                 Prod.mk.injEq, Except.ok.injEq] at hH
      exact hH.1

/-- Call-site WF/disjointness invariants required by `callElimStatementCorrect`.

    Bundles the six call-site WF clauses that were previously expressed as a
    single nested conjunction (`Hpre_post_lhs_disj`).  Each field is a
    universally-quantified property that fires only when `st` is a call;
    for non-call statements every field is vacuously true. -/
structure WFCallSiteProp (p : Program)
                         (π : String → Option Procedure)
                         (st : Statement) : Prop where
  /-- Pre-condition free vars are not `tmp_`/`old_`-prefixed and not in the
      call's `lhs`. -/
  preVarsFresh :
    ∀ procName args md, st = .cmd (CmdExt.call procName args md) →
    ∀ proc, π procName = some proc →
    ∀ pre ∈ Procedure.Spec.getCheckExprs proc.spec.preconditions,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) pre,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
      v ∉ CallArg.getLhs args
  /-- Post-condition free vars are not `tmp_`/`old_`-prefixed and not in the
      call's `lhs`. -/
  postVarsFresh :
    ∀ procName args md, st = .cmd (CmdExt.call procName args md) →
    ∀ proc, π procName = some proc →
    ∀ post ∈ Procedure.Spec.getCheckExprs proc.spec.postconditions,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) post,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
      v ∉ CallArg.getLhs args
  /-- Argument-expression free vars are disjoint from the call's `lhs`. -/
  argVarsNotInLhs :
    ∀ procName args md, st = .cmd (CmdExt.call procName args md) →
    ∀ _proc, π procName = some _proc →
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ CallArg.getLhs args
  /-- Procedure input/output parameter names are not `tmp_`/`old_`-prefixed. -/
  inoutFresh :
    ∀ procName args md, st = .cmd (CmdExt.call procName args md) →
    ∀ proc, π procName = some proc →
    ∀ v ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v
  /-- Argument-expression free vars are disjoint from the procedure's
      `outputs.keys` (the global modset). -/
  argVarsNotInOutKeys :
    ∀ procName args md, st = .cmd (CmdExt.call procName args md) →
    ∀ proc, π procName = some proc →
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ ListMap.keys proc.header.outputs
  /-- Argument-expression free vars are disjoint from the procedure's
      `inputs.keys` (procedure parameter names). -/
  argVarsNotInInKeys :
    ∀ procName args md, st = .cmd (CmdExt.call procName args md) →
    ∀ proc, π procName = some proc →
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ ListMap.keys proc.header.inputs
  /-- Positional-alignment WF for inout outputs: for each output parameter
      `v ∈ outputs.keys` that is also an `lhs` entry (i.e., an inout pass),
      the call's lhs index for `v` agrees with the procedure's outputs-keys
      index.  Backs the L6 `HoldEval_bridge` derivation. -/
  outAlignment :
    ∀ procName args md, st = .cmd (CmdExt.call procName args md) →
    ∀ proc, π procName = some proc →
    ∀ v ∈ ListMap.keys proc.header.outputs,
      v ∈ CallArg.getLhs args →
      (CallArg.getLhs args).idxOf v =
        (ListMap.keys proc.header.outputs).idxOf v

/-- Call-site WF clauses already specialized at a fixed call form
    `(procName, args, md)` and a fixed procedure `proc`.

    Bundles the seven `WFCallSiteProp` fields with the per-call
    `(procName, args, md, rfl, proc, lkup)` instantiation already
    applied, so call-site code can `obtain ⟨...⟩ := ... .specialize ...`
    in one step instead of repeating the instantiation per field. -/
structure WFCallSiteSpec (proc : Procedure) (args : List (CallArg Expression)) : Prop where
  preVarsFresh :
    ∀ pre ∈ Procedure.Spec.getCheckExprs proc.spec.preconditions,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) pre,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
      v ∉ CallArg.getLhs args
  postVarsFresh :
    ∀ post ∈ Procedure.Spec.getCheckExprs proc.spec.postconditions,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) post,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
      v ∉ CallArg.getLhs args
  argVarsNotInLhs :
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ CallArg.getLhs args
  inoutFresh :
    ∀ v ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v
  argVarsNotInOutKeys :
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ ListMap.keys proc.header.outputs
  argVarsNotInInKeys :
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ ListMap.keys proc.header.inputs
  outAlignment :
    ∀ v ∈ ListMap.keys proc.header.outputs,
      v ∈ CallArg.getLhs args →
      (CallArg.getLhs args).idxOf v =
        (ListMap.keys proc.header.outputs).idxOf v

/-- Specialize all seven `WFCallSiteProp` fields at a fixed call form
    `st = .cmd (CmdExt.call procName args md)` and procedure lookup
    `π procName = some proc`.

    Lets the call-site case discharge the `(procName, args, md, rfl,
    proc, lkup)` instantiation once and reuse the seven specialized
    facts via `obtain ⟨...⟩ := Hwfcs.specialize Hst Hlkup`. -/
theorem WFCallSiteProp.specialize {p : Program}
    {π : String → Option Procedure} {st : Statement}
    {procName : String} {args : List (CallArg Expression)} {md}
    {proc : Procedure}
    (Hwfcs : WFCallSiteProp p π st)
    (Hst : st = .cmd (CmdExt.call procName args md))
    (Hlkup : π procName = some proc) : WFCallSiteSpec proc args :=
  ⟨ Hwfcs.preVarsFresh procName args md Hst proc Hlkup
  , Hwfcs.postVarsFresh procName args md Hst proc Hlkup
  , Hwfcs.argVarsNotInLhs procName args md Hst proc Hlkup
  , Hwfcs.inoutFresh procName args md Hst proc Hlkup
  , Hwfcs.argVarsNotInOutKeys procName args md Hst proc Hlkup
  , Hwfcs.argVarsNotInInKeys procName args md Hst proc Hlkup
  , Hwfcs.outAlignment procName args md Hst proc Hlkup ⟩

/-- Relation between the source store `σ` and the call-elim transform
    state `γ`'s tracked fresh-name set.

    Bundles the two halves of the legacy `Hwfgenst` hypothesis: the
    `tmp_*` alignment between `γ.genState.generated` and `σ`'s defined
    keys, and the `old_*` freshness against `σ`. -/
structure CoreGenStateRel (σ : CoreStore) (γ : CoreTransformState) : Prop where
  /-- `tmp_*`-prefixed names in `γ.genState.generated` are exactly the
      `tmp_*`-defined names in `σ`. -/
  tmpAlign : ∀ v, v ∈ γ.genState.generated ∧ isTempIdent v ↔
                  (σ v).isSome ∧ isTempIdent v
  /-- `old_*`-prefixed names are never defined in `σ`. -/
  oldFresh : ∀ v, isOldTempIdent v → (σ v).isNone
  /-- The fresh-name generator state is well-formed.  Folded in here so
      `CoreGenStateRel` is the complete γ-vs-σ relation needed by the
      call-elim proof. -/
  wfgen : CoreGenState.WF γ.genState

/-- Call-elimination correctness for a single statement.

    Given a small-step `EvalStatementsContract` derivation of `[st]`
    from σ to σ', the transformed statement list `sts` produced by
    `callElimStmt` admits an `EvalStatementsContract` derivation from
    σ to some σ'' that extends σ' on the freshly-introduced temp
    variables.

    For non-call statements `callElimStmt` returns `[st]` unchanged
    and the conclusion is immediate.  For a call statement the proof
    chains L1–L6 via `EvalCallElim_glue`; that integration is the
    open obligation, recorded as a single `sorry` below.

    The WF/disjointness hypotheses (`Hp`, `Hwfc`, `Hwf`, `Hwfp`,
    `Hgenrel`) are needed by the call-case proof
    (when the open `sorry` is discharged); for non-call cases they
    are not used. They are reinstated here so the next implementer
    has them available.

    The legacy big-step signature also carried `Hgv`
    (`∀ gk, (p.find? .var gk).isSome → (σ gk).isSome`); this is
    omitted because the current `Core.DeclKind` has no `.var` kind
    and there is no live notion of "global variable declaration"
    in `Program` to relate to a store.

    -/
theorem callElimStatementCorrect [LawfulBEq Expression.Expr]
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval}
    {σ σ' : CoreStore}
    {p : Program}
    {γ γ' : CoreTransformState}
    {st : Statement}
    {sts : List Statement}
    (Hp : ∀ pname, π pname = Program.Procedure.find? p ⟨pname, ()⟩)
    (Heval : EvalStatementsContract π φ ⟨σ, δ, false⟩ [st] ⟨σ', δ, false⟩)
    (Hwfc : WellFormedCoreEvalCong δ)
    (Hwf : WF.WFStatementsProp p [st])
    (Hgenrel : CoreGenStateRel σ γ)
    -- Call-site WF: pre/post vars are non-temp/non-old and disjoint
    -- from `lhs`/inputs.keys/outputs.keys (six clauses; see WFCallSiteProp
    -- in Strata/Languages/Core/WF.lean).
    (Hwfcallsite : WFCallSiteProp p π st)
    (Helim : (Except.ok sts, γ') = (runWith st (callElimStmt · p) γ)) :
    ∃ σ'',
      Inits σ' σ'' ∧
      EvalStatementsContract π φ ⟨σ, δ, false⟩ sts ⟨σ'', δ, false⟩ := by
  -- Non-call cases close with σ'' = σ' (callElimStmt returns [st]);
  -- call case extends σ' with fresh temp/old vars.  Non-call branches
  -- unified via `callElimStmt_non_call_eq`, dispatched through `nc_close`.
  have nc_close : ∀ {b : Statement} (_ : st = b)
      (_ : ∀ pn ar mt, b ≠ .cmd (CmdExt.call pn ar mt)),
      ∃ σ'', Inits σ' σ'' ∧
        EvalStatementsContract π φ ⟨σ, δ, false⟩ sts ⟨σ'', δ, false⟩ := by
    intro b heq hne
    refine ⟨σ', Inits.init InitVars.init_none, ?_⟩
    have hsts := callElimStmt_non_call_eq hne (heq ▸ Helim)
    rw [hsts]; rw [← heq]; exact Heval
  cases hst : st with
  | block lbl b md => exact nc_close hst (by intro _ _ _ h; cases h)
  | ite cd tb eb md => exact nc_close hst (by intro _ _ _ h; cases h)
  | loop g m i b md => exact nc_close hst (by intro _ _ _ h; cases h)
  | exit lbl md => exact nc_close hst (by intro _ _ _ h; cases h)
  | funcDecl f md => exact nc_close hst (by intro _ _ _ h; cases h)
  | typeDecl tc md => exact nc_close hst (by intro _ _ _ h; cases h)
  | cmd c =>
      cases c with
      | cmd c' => exact nc_close hst (by intro _ _ _ h; cases h)
      | call procName args md =>
          -- B1: Destructure Helim to expose triplet plumbing.
          subst hst
          simp only [runWith, StateT.run, callElimStmt,
                     bind, pure,
                     StateT.bind, ExceptT.bind, ExceptT.bindCont,
                     ExceptT.mk, ExceptT.pure, modify, modifyGet,
                     MonadStateOf.modifyGet, MonadState.modifyGet,
                     StateT.modifyGet, MonadStateOf.set,
                     monadLift, MonadLift.monadLift, liftM, ExceptT.lift,
                     StateT.pure, Functor.map, StateT.map] at Helim
          -- Helim is now `(Except.ok sts, γ') = (match callElimCmd … γ_ext …)`.
          -- Successive splits peel the outer pair-binder, the inner Except,
          -- and the `Option (List Statement)`.
          split at Helim
          rename_i x_pair a_ce s_ce heq_ce
          split at Helim
          · -- inner `Except.ok` branch
            rename_i a_opt heq_ok
            -- a_opt : Option (List Statement)
            -- Now Helim has a `match a_opt with | none => ... | some s' => ...`.
            split at Helim
            · -- `a_opt = none`: heq_ce says `callElimCmd ... = (Except.ok none, s_ce)`.
              -- But `callElimCmd (CmdExt.call ...)` never returns `.none` —
              -- only the `_ => return .none` catch-all does, which is
              -- unreachable here.  We discharge this via the equation.
              refine ⟨σ', Inits.init InitVars.init_none, ?_⟩
              simp only [pure, StateT.pure, Prod.mk.injEq, Except.ok.injEq] at Helim
              -- Helim.1 : sts = [Imperative.Stmt.cmd (CmdExt.call procName args md)]
              rw [Helim.1]; exact Heval
            · -- `a_opt = some s'`: this is the genuine call-elim case.
              rename_i s' heq_some
              simp only [pure, StateT.pure, Prod.mk.injEq, Except.ok.injEq] at Helim
              obtain ⟨Hsts, Hγ⟩ := Helim
              -- B1/B2: callElimCmd_call_eq + Heval inversion to call_sem.
              rw [Hsts]
              have ⟨ρ_inner, hstep_call, htail⟩ : ∃ ρ_inner,
                  Imperative.StepStmtStar Expression (EvalCommandContract π)
                      (EvalPureFunc φ)
                      (.stmt (Imperative.Stmt.cmd
                        (CmdExt.call procName args md))
                          ⟨σ, δ, false⟩)
                      (.terminal ρ_inner) ∧
                  Imperative.StepStmtStar Expression (EvalCommandContract π)
                      (EvalPureFunc φ)
                      (.stmts [] ρ_inner)
                      (.terminal ⟨σ', δ, false⟩) := by
                unfold EvalStatementsContract Imperative.EvalStmtsSmall at Heval
                match Heval with
                | .step _ _ _ .step_stmts_cons hrest =>
                  exact Imperative.seq_reaches_terminal Expression
                    (EvalCommandContract π) (EvalPureFunc φ) hrest
              -- htail forces ρ_inner = ⟨σ',δ,false⟩.
              have hρ_inner_eq : ρ_inner = ⟨σ', δ, false⟩ := by
                match htail with
                | .step _ _ _ .step_stmts_nil hrest' =>
                  cases hrest' with
                  | refl => rfl
                  | step _ _ _ h _ => exact absurd h (by intro h; cases h)
              subst hρ_inner_eq
              -- Now `hstep_call : StepStmtStar (.stmt (.cmd (.call ...)) ⟨σ,δ,false⟩) (.terminal ⟨σ',δ,false⟩)`.
              -- A single `step_cmd` of `EvalCommandContract` lifts to
              -- this multi-step trace; invert to extract `Hcc`.
              have Hcc : EvalCommandContract π δ σ
                  (CmdExt.call procName args md) σ' false := by
                match hstep_call with
                | .step _ _ _ (.step_cmd hcc) hrest =>
                  cases hrest with
                  | refl =>
                    -- call_sem hardwires the failure flag to false.
                    exact hcc
                  | step _ _ _ h _ => exact absurd h (by intro h; cases h)
              cases Hcc with
              | call_sem lkup hCallArgsIn hCallArgsLhs Hevalargs Hevalouts
                          Hwfval Hwfvars Hwfb Hwf2 HdefOver
                          Hinitin Hinitout Hpre Hhav1 Hpost Hrd Hupdate =>
                -- call_sem implicits: lhs σ₀ inArgs oVals argVals σA σAO σO proc modvals.
                rename_i lhs σ₀ inArgs oVals argVals σA σAO σO proc modvals
                -- B1-tail: destructure heq_ce via callElimCmd_call_eq.
                obtain ⟨proc', argTrips, outTrips, genOldIdents, oldTys,
                        asserts, assumes,
                        s_arg, s_out, s_old,
                        Hfind, Heqarg, Heqout, Heqold, Holdtylen,
                        Hsts_struct, HassertsShape, HassumesShape⟩ :=
                  callElimCmd_call_eq heq_ce
                have Heqargs : argTrips.unzip.snd =
                    CallArg.getInputExprs args :=
                  genArgExprIdentsTrip_snd Heqarg
                have Heqouts : outTrips.unzip.snd =
                    CallArg.getLhs args :=
                  genOutExprIdentsTrip_snd Heqout
                -- Hoisted abbreviations for argument/output temp idents.
                let argTemps : List Expression.Ident :=
                  argTrips.unzip.fst.unzip.fst
                let outTemps : List Expression.Ident :=
                  outTrips.unzip.fst.unzip.fst
                -- C1: aux facts derived from the destructured binders.
                have Hwfgenargs : CoreGenState.WF s_arg.genState := by
                  apply genArgExprIdentsTripWFMono ?_ Heqarg
                  exact Hgenrel.wfgen
                have Hwfgenouts : CoreGenState.WF s_out.genState :=
                  genOutExprIdentsTripWFMono Hwfgenargs Heqout
                have Hgenargs :
                    s_arg.genState.generated =
                      argTemps.reverse ++
                        γ.genState.generated := by
                  have HH := genArgExprIdentsTripGeneratedWF Heqarg
                  -- {γ with ...}.genState = γ.genState; reduce.
                  exact HH
                have Hgenouts :
                    s_out.genState.generated =
                      outTemps.reverse ++
                        s_arg.genState.generated :=
                  genOutExprIdentsTripGeneratedWF Heqout
                have HargTemp :
                    Forall (fun x => isTempIdent x)
                      argTemps :=
                  genArgExprIdentsTrip_isTempIdent Heqarg
                have HoutTemp :
                    Forall (fun x => isTempIdent x)
                      outTemps :=
                  genOutExprIdentsTrip_isTempIdent Heqout
                -- Old-related aux facts.  `oldVars` is the filter
                -- expression in the live `callElimCmd`.
                have Hwfgenolds : CoreGenState.WF s_old :=
                  genOldExprIdentsTripWFMono Hwfgenouts Heqold
                have Hgenolds :
                    s_old.generated =
                      genOldIdents.reverse ++ s_out.genState.generated :=
                  genOldExprIdents_GeneratedWF Heqold
                have HoldIdentsTemp :
                    Forall (fun x => isOldTempIdent x) genOldIdents :=
                  genOldExprIdents_isOldTempIdent Heqold
                -- Combined-extension equation: the post-old gen list is
                -- the concatenation of all three reverse-segments and γ's gen.
                have HgenApp :
                    s_old.generated =
                      genOldIdents.reverse ++
                        outTemps.reverse ++
                          argTemps.reverse ++
                            γ.genState.generated := by
                  rw [Hgenolds, Hgenouts, Hgenargs]
                  simp [List.append_assoc]
                -- Nodup of the combined list, in reversed-segment shape.
                have Hgennd' :
                    (γ.genState.generated.reverse ++
                      argTemps ++
                        outTemps ++
                          genOldIdents).Nodup := by
                  -- `Hwfgenolds : CoreGenState.WF s_old`, which is a 3-conj
                  -- `StringGenState.WF s_old.cs ∧ ... ∧ s_old.generated.Nodup`.
                  -- Project the third component via `.right.right`.
                  have HndOld : s_old.generated.Nodup := Hwfgenolds.right.right
                  rw [HgenApp] at HndOld
                  have Hnd := nodup_reverse HndOld
                  simp only [List.reverse_append, List.reverse_reverse,
                             ← List.append_assoc] at Hnd
                  exact Hnd
                -- Nodup of just (argT ++ outT ++ genOldIdents).
                have Hgennd :
                    (argTemps ++
                      outTemps ++
                        genOldIdents).Nodup := by
                  simp only [List.append_assoc] at Hgennd' ⊢
                  exact (List.nodup_append.mp Hgennd').2.1
                -- Hgennd' nodup → arg/out/old segments σ-fresh.
                have Hnotgen_arg :
                    ∀ x ∈ argTemps,
                      x ∉ γ.genState.generated := by
                  intro x Hxin
                  -- Hgennd' : (γ.gen.rev ++ argT ++ outT ++ olds).Nodup.
                  -- Re-associate to (γ.gen.rev ++ (argT ++ outT ++ olds))
                  -- so that nodup_append gives a disjointness over the
                  -- full second segment.
                  have Hnd1 : List.Nodup (γ.genState.generated.reverse ++
                      (argTemps ++
                        outTemps ++ genOldIdents)) := by
                    simp only [List.append_assoc] at Hgennd' ⊢
                    exact Hgennd'
                  have Hdisj := (List.nodup_append.mp Hnd1).2.2
                  intro Hxgen
                  have Hin_rev : x ∈ γ.genState.generated.reverse :=
                    List.mem_reverse.mpr Hxgen
                  have Hin_combined :
                      x ∈ argTemps ++
                            outTemps ++ genOldIdents := by
                    simp only [List.mem_append]
                    exact Or.inl (Or.inl Hxin)
                  exact Hdisj x Hin_rev x Hin_combined rfl
                have Hnotgen_out :
                    ∀ x ∈ outTemps,
                      x ∉ γ.genState.generated := by
                  intro x Hxin
                  have Hnd1 : List.Nodup (γ.genState.generated.reverse ++
                      (argTemps ++
                        outTemps ++ genOldIdents)) := by
                    simp only [List.append_assoc] at Hgennd' ⊢
                    exact Hgennd'
                  have Hdisj := (List.nodup_append.mp Hnd1).2.2
                  intro Hxgen
                  have Hin_rev : x ∈ γ.genState.generated.reverse :=
                    List.mem_reverse.mpr Hxgen
                  have Hin_combined :
                      x ∈ argTemps ++
                            outTemps ++ genOldIdents := by
                    simp only [List.mem_append]
                    exact Or.inl (Or.inr Hxin)
                  exact Hdisj x Hin_rev x Hin_combined rfl
                -- σ-level freshness facts.
                have HndefArg_σ :
                    Imperative.isNotDefined σ argTemps :=
                  fresh_temps_not_defined Hgenrel.tmpAlign Hnotgen_arg HargTemp
                have HndefOut_σ :
                    Imperative.isNotDefined σ outTemps :=
                  fresh_temps_not_defined Hgenrel.tmpAlign Hnotgen_out HoutTemp
                have HndefOld_σ :
                    Imperative.isNotDefined σ genOldIdents :=
                  fresh_olds_not_defined Hgenrel.oldFresh HoldIdentsTemp
                -- Combined freshness against σ.
                have Hndefσ :
                    Imperative.isNotDefined σ
                      (argTemps ++
                        outTemps ++
                          genOldIdents) := by
                  intro v Hin
                  simp only [List.mem_append] at Hin
                  rcases Hin with (Hin | Hin)
                  · rcases Hin with (Hin | Hin)
                    · exact HndefArg_σ v Hin
                    · exact HndefOut_σ v Hin
                  · exact HndefOld_σ v Hin
                -- Lift to σ' via Hupdate.
                have Hndefgen :
                    Imperative.isNotDefined σ'
                      (argTemps ++
                        outTemps ++
                          genOldIdents) :=
                  UpdateStatesNotDefMonotone Hndefσ Hupdate
                -- ── Length facts ──
                -- argTrips.length = argVals.length
                have Hargtriplen : argTrips.length = argVals.length := by
                  rw [← List.unzip_snd_length argTrips, Heqargs, hCallArgsIn]
                  exact EvalExpressionsLength Hevalargs
                -- outTrips.length = oVals.length
                have Houttriplen : outTrips.length = oVals.length := by
                  rw [← List.unzip_snd_length outTrips, Heqouts, hCallArgsLhs]
                  exact ReadValuesLength Hevalouts
                -- C1: Derive Hinoutnd from the call_sem InitStates binders.
                have Hinnd_io : (proc.header.inputs.keys).Nodup :=
                  InitStatesNodup Hinitin
                have Houtnd_io : (proc.header.outputs.keys).Nodup :=
                  InitStatesNodup Hinitout
                have Hindef_io :
                    Imperative.isDefined σA (proc.header.inputs.keys) :=
                  InitStatesDefined Hinitin
                have Houtndef_io :
                    Imperative.isNotDefined σA (proc.header.outputs.keys) :=
                  InitStatesNotDefined Hinitout
                have Hiodisj :
                    (proc.header.inputs.keys).Disjoint
                      (proc.header.outputs.keys) := by
                  intro x Hin1 Hin2
                  have h1 : (σA x).isSome = true := Hindef_io x Hin1
                  have h2 : σA x = none := Houtndef_io x Hin2
                  rw [h2] at h1
                  simp at h1
                have Hinoutnd :
                    (proc.header.inputs.keys ++
                      proc.header.outputs.keys).Nodup := by
                  rw [List.nodup_append]
                  refine ⟨Hinnd_io, Houtnd_io, ?_⟩
                  intro a Ha b Hb Heq
                  subst Heq
                  exact Hiodisj Ha Hb
                -- C2: bind `oldVars` (filter from Hsts_struct) for HoldVals/Holdtriplen.
                let oldVars : List Expression.Ident :=
                  List.filter
                    (fun g =>
                      (ListMap.keys proc'.header.inputs).contains g &&
                          (ListMap.keys proc'.header.outputs).contains g &&
                        (List.map Procedure.Check.expr
                            proc'.spec.postconditions.values).any fun e =>
                          List.any e.freeVars
                            fun x => x.fst == CoreIdent.mkOld g.name)
                    (CallArg.getLhs args)
                -- `oldVars ⊆ lhs` because the filter narrows `lhs` ↪ `oldVars`.
                -- `Hevalouts : ReadValues σ lhs oVals` then forces every
                -- element of `lhs` (and hence `oldVars`) defined in σ.
                have HrdOldDef : Imperative.isDefined σ oldVars := by
                  intro g Hg
                  have Hg_in_getLhs : g ∈ CallArg.getLhs args :=
                    (List.mem_filter.mp Hg).1
                  -- `hCallArgsLhs : CallArg.getLhs args = lhs` (forward).
                  have Hg_in_lhs : g ∈ lhs := hCallArgsLhs ▸ Hg_in_getLhs
                  have Hlhs_def : Imperative.isDefined σ lhs :=
                    ReadValuesIsDefined Hevalouts
                  exact Hlhs_def g Hg_in_lhs
                -- Existential reading of `oldVars` against σ.
                obtain ⟨oldVals, HoldVals⟩ :=
                  isDefinedReadValues HrdOldDef
                -- Length facts.
                have HoldValsLen : oldVals.length = oldVars.length := by
                  have := ReadValuesLength HoldVals
                  exact this.symm
                -- genOld = oldTys = oldVars length facts for trip-shape.
                have HgenOldLen : genOldIdents.length = oldVars.length :=
                  genOldExprIdents_length Heqold
                have HoldTysLen : oldTys.length = oldVars.length := Holdtylen
                have Holdtriplen :
                    oldVals.length =
                      ((genOldIdents.zip oldTys).zip oldVars).length := by
                  rw [HoldValsLen]
                  simp [List.length_zip, HgenOldLen, HoldTysLen]
                -- C3: σ'' = updatedStates σ' (argTemps++outTemps++genOldIdents) (...).
                have Hinit :=
                  updatedStatesInit (P := Expression) ?_ ?_ ?_ (σ := σ')
                    (hs := argTemps
                            ++ outTemps
                            ++ genOldIdents)
                    (vs := argVals ++ oVals ++ oldVals)
                rotate_left
                · -- length of `hs` = length of `vs`
                  -- Reduce both sides via List.length_append, then close
                  -- segment-wise via Hargtriplen / Houttriplen / (HgenOldLen ; HoldValsLen).
                  have HgenOldValsLen :
                      genOldIdents.length = oldVals.length := by
                    rw [HgenOldLen, ← HoldValsLen]
                  simp [argTemps, outTemps, List.length_append, List.unzip_eq_map,
                        Hargtriplen, Houttriplen, HgenOldValsLen]
                · exact Hndefgen
                · exact Hgennd
                -- σ'' is the updatedStates σ' … form; D2 may use InitsUpdatesComm.
                refine ⟨updatedStates σ'
                          (argTemps
                            ++ outTemps
                            ++ genOldIdents)
                          (argVals ++ oVals ++ oldVals), ?_, ?_⟩
                · -- First conjunct: Inits σ' σ''.
                  exact InitStatesInits Hinit
                · -- L1-L6 chain via EvalCallElim_glue.
                  have HargNd : argTemps.Nodup := by
                    have Hsplit := List.nodup_append.mp Hgennd
                    -- Hgennd : (argT ++ outT ++ olds).Nodup;
                    -- Hsplit.1 : (argT ++ outT).Nodup
                    exact (List.nodup_append.mp Hsplit.1).1
                  have HoutNd : outTemps.Nodup := by
                    have Hsplit := List.nodup_append.mp Hgennd
                    exact (List.nodup_append.mp Hsplit.1).2.1
                  have HoldNd : genOldIdents.Nodup := by
                    have Hsplit := List.nodup_append.mp Hgennd
                    exact Hsplit.2.1
                  have HargOutDisj :
                      argTemps.Disjoint
                        outTemps := by
                    have Hsplit := List.nodup_append.mp Hgennd
                    have Hsplit2 := List.nodup_append.mp Hsplit.1
                    intro x Hin1 Hin2
                    exact Hsplit2.2.2 x Hin1 x Hin2 rfl
                  have HargOldDisj :
                      argTemps.Disjoint genOldIdents := by
                    have Hnd' : (argTemps ++
                                  (outTemps ++
                                    genOldIdents)).Nodup := by
                      simp only [List.append_assoc] at Hgennd
                      exact Hgennd
                    have Hsplit := List.nodup_append.mp Hnd'
                    intro x Hin1 Hin2
                    exact Hsplit.2.2 x Hin1 x
                      (List.mem_append.mpr (Or.inr Hin2)) rfl
                  have HoutOldDisj :
                      outTemps.Disjoint genOldIdents := by
                    have Hsplit := List.nodup_append.mp Hgennd
                    have Hsplit2 := List.nodup_append.mp Hsplit.1
                    -- Hsplit.2.1 : (outT ++ olds).Nodup is wrong shape;
                    -- Hgennd is ((argT ++ outT) ++ olds).Nodup.
                    -- Use Hsplit.2.2 : (argT ++ outT) Disjoint olds.
                    intro x Hin1 Hin2
                    exact Hsplit.2.2 x
                      (List.mem_append.mpr (Or.inr Hin1)) x Hin2 rfl
                  -- Disjointness of σ-defined argument expression vars
                  -- from the freshly generated argTemps: HdefOver puts
                  -- them in σ, HndefArg_σ keeps temps out of σ, so they
                  -- can't intersect.
                  have HdefVars : Imperative.isDefined σ
                      (List.flatMap
                        (Imperative.HasVarsPure.getVars (P:=Expression))
                        (CallArg.getInputExprs args)) := by
                    -- Use Hevalargs directly via evalExpressions_isDefined_flatMap.
                    have Heval' :
                        Imperative.isDefined σ
                          (List.flatMap
                            (Imperative.HasVarsPure.getVars (P:=Expression))
                            inArgs) :=
                      evalExpressions_isDefined_flatMap Hevalargs
                    -- hCallArgsIn : CallArg.getInputExprs args = inArgs.
                    rw [← hCallArgsIn] at Heval'
                    exact Heval'
                  have HargExprDisj :
                      argTemps.Disjoint
                        (List.flatMap
                          (Imperative.HasVarsPure.getVars (P:=Expression))
                          argTrips.unzip.snd) := by
                    intro x Hin1 Hin2
                    -- Rewrite Hin2 via Heqargs so we can use HdefVars.
                    rw [Heqargs] at Hin2
                    -- HndefArg_σ says σ x = none; HdefVars says (σ x).isSome.
                    have Hnone : σ x = none := HndefArg_σ x Hin1
                    have Hsome : (σ x).isSome = true := HdefVars x Hin2
                    rw [Hnone] at Hsome
                    simp at Hsome
                  -- ── L1: argInit ──
                  -- `H_inits` evaluates `createInits argTrips md` from
                  -- σ to `updatedStates σ argTemps argVals`.
                  have HevalArgs' :
                      EvalExpressions (P:=Core.Expression) δ σ
                        argTrips.unzip.snd argVals := by
                    rw [Heqargs, hCallArgsIn]
                    exact Hevalargs
                  have HL1 :
                      EvalStatementsContract π φ ⟨σ, δ, false⟩
                        (Core.Transform.createInits argTrips md)
                        ⟨updatedStates σ argTemps
                          argVals, δ, false⟩ :=
                    H_inits Hwfvars Hwfval Hwfc HargExprDisj HargNd
                      HevalArgs' HndefArg_σ
                  -- L2: outInit (lift Hevalouts to σ_arg via readValues_updatedStates).
                  have Hlhs_isLocl :
                      Imperative.isDefined σ lhs :=
                    ReadValuesIsDefined Hevalouts
                  have HlhsDisjArg :
                      lhs.Disjoint argTemps := by
                    intro x Hin1 Hin2
                    have Hnone : σ x = none := HndefArg_σ x Hin2
                    have Hsome : (σ x).isSome = true := Hlhs_isLocl x Hin1
                    rw [Hnone] at Hsome
                    simp at Hsome
                  have HlhsDisjOut :
                      lhs.Disjoint outTemps := by
                    intro x Hin1 Hin2
                    have Hnone : σ x = none := HndefOut_σ x Hin2
                    have Hsome : (σ x).isSome = true := Hlhs_isLocl x Hin1
                    rw [Hnone] at Hsome
                    simp at Hsome
                  have HlhsDisjOld :
                      lhs.Disjoint genOldIdents := by
                    intro x Hin1 Hin2
                    have Hnone : σ x = none := HndefOld_σ x Hin2
                    have Hsome : (σ x).isSome = true := Hlhs_isLocl x Hin1
                    rw [Hnone] at Hsome
                    simp at Hsome
                  -- Out-temp Nodup append form for `H_initVars`.
                  have HoutSnd_eq_lhs : outTrips.unzip.snd = lhs := by
                    rw [Heqouts, hCallArgsLhs]
                  have HlhsNd : lhs.Nodup := by
                    -- WFcallProp.lhsWF says (CallArg.getLhs args).Nodup.
                    -- Hwf is now Forall (WFStatementProp p)
                    --   [Stmt.cmd (CmdExt.call procName args md)].
                    have Hwfst_head := (List.Forall_cons _ _ _).mp Hwf
                    -- Hwfst_head.1 : WFStatementProp p (Statement.call ...)
                    have Hwfcall : WF.WFcallProp p procName args := Hwfst_head.1
                    have Hlhs_args_nd :
                        (CallArg.getLhs args).Nodup := Hwfcall.lhsWF
                    rw [hCallArgsLhs] at Hlhs_args_nd
                    exact Hlhs_args_nd
                  have Hout_nd_app :
                      List.Nodup (outTemps
                                  ++ outTrips.unzip.snd) := by
                    rw [HoutSnd_eq_lhs]
                    rw [List.nodup_append]
                    refine ⟨HoutNd, HlhsNd, ?_⟩
                    intro a Ha b Hb Heq
                    subst Heq
                    exact HlhsDisjOut Hb Ha
                  -- ReadValues over the σ_arg store.
                  have HrdOuts_argLayer :
                      ReadValues
                        (updatedStates σ argTemps
                          argVals)
                        outTrips.unzip.snd oVals := by
                    rw [HoutSnd_eq_lhs]
                    apply readValues_updatedStates
                    · -- length: argTemps.length = argVals.length via Hargtriplen
                      rw [show argTemps.length =
                            argTrips.length from by
                            simp [argTemps, List.unzip_eq_map]]
                      exact Hargtriplen
                    · exact HlhsDisjArg
                    · exact Hevalouts
                  -- outTemps undefined in σ_arg (argTemps disjoint from outTemps).
                  have HndefOut_argLayer :
                      Imperative.isNotDefined
                        (updatedStates σ argTemps
                          argVals)
                        outTemps := by
                    intro v Hv
                    have Hv_notin : ¬ v ∈ argTemps := by
                      intro Hin
                      exact HargOutDisj Hin Hv
                    have Hfall := updatedStates_get_notin
                      (σ:=σ)
                      (ks:=argTemps)
                      (vs:=argVals) Hv_notin
                    rw [Hfall]
                    exact HndefOut_σ v Hv
                  have HL2 :
                      EvalStatementsContract π φ
                        ⟨updatedStates σ argTemps
                          argVals, δ, false⟩
                        (Core.Transform.createInitVars outTrips md)
                        ⟨updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals, δ, false⟩ :=
                    H_initVars Hwfvars Hout_nd_app HrdOuts_argLayer
                      HndefOut_argLayer
                  -- L3: oldInit; oldTrips := (genOldIdents.zip oldTys).zip oldVars.
                  let oldTrips :
                      List ((Expression.Ident × Expression.Ty) ×
                             Expression.Ident) :=
                    (genOldIdents.zip oldTys).zip oldVars
                  have HoldTripsFst :
                      oldTrips.unzip.fst.unzip.fst = genOldIdents := by
                    -- (genOldIdents.zip oldTys).zip oldVars
                    -- unzip.fst = genOldIdents.zip oldTys (when lengths match)
                    -- unzip.fst.unzip.fst = genOldIdents (when lengths match)
                    have HzipLen :
                        (genOldIdents.zip oldTys).length = oldVars.length := by
                      simp [List.length_zip, HgenOldLen, HoldTysLen]
                    have HzipUnzip1 :
                        ((genOldIdents.zip oldTys).zip oldVars).unzip.fst =
                          genOldIdents.zip oldTys := by
                      simp [List.unzip_eq_map, List.map_fst_zip,
                            HzipLen]
                    have HzipUnzip2 :
                        (genOldIdents.zip oldTys).unzip.fst = genOldIdents := by
                      simp [List.unzip_eq_map, List.map_fst_zip,
                            HgenOldLen, HoldTysLen]
                    rw [show oldTrips = (genOldIdents.zip oldTys).zip oldVars
                        from rfl]
                    rw [HzipUnzip1]
                    exact HzipUnzip2
                  have HoldTripsSnd :
                      oldTrips.unzip.snd = oldVars := by
                    have HzipLen :
                        (genOldIdents.zip oldTys).length = oldVars.length := by
                      simp [List.length_zip, HgenOldLen, HoldTysLen]
                    rw [show oldTrips = (genOldIdents.zip oldTys).zip oldVars
                        from rfl]
                    simp [List.unzip_eq_map, List.map_snd_zip, HzipLen]
                  -- Disjointness of oldVars from argTemps/outTemps and
                  -- oldVars Nodup follow from `oldVars ⊆ lhs`.
                  have HoldVars_sub_lhs : ∀ g ∈ oldVars, g ∈ lhs := by
                    intro g Hg
                    have Hg_in_getLhs : g ∈ CallArg.getLhs args :=
                      (List.mem_filter.mp Hg).1
                    exact hCallArgsLhs ▸ Hg_in_getLhs
                  have HoldVarsDisjArg :
                      oldVars.Disjoint argTemps := by
                    intro x Hin1 Hin2
                    exact HlhsDisjArg (HoldVars_sub_lhs x Hin1) Hin2
                  have HoldVarsDisjOut :
                      oldVars.Disjoint outTemps := by
                    intro x Hin1 Hin2
                    exact HlhsDisjOut (HoldVars_sub_lhs x Hin1) Hin2
                  have HoldVarsDisjOldT :
                      oldVars.Disjoint genOldIdents := by
                    intro x Hin1 Hin2
                    exact HlhsDisjOld (HoldVars_sub_lhs x Hin1) Hin2
                  have HoldVarsNd : oldVars.Nodup := by
                    -- oldVars = filter ... (CallArg.getLhs args), and
                    -- (CallArg.getLhs args) = lhs (via hCallArgsLhs) so
                    -- has the same Nodup as `lhs`.
                    have HlhsArgs_nd : (CallArg.getLhs args).Nodup := by
                      rw [hCallArgsLhs]
                      exact HlhsNd
                    exact List.Sublist.nodup List.filter_sublist HlhsArgs_nd
                  -- σ_out := updatedStates (updatedStates σ argT argVals)
                  --                       outT oVals.
                  -- ReadValues σ oldVars oldVals (from C2's HoldVals).
                  -- Lift to σ_out via two readValues_updatedStates layers.
                  have HrdOlds_outLayer :
                      ReadValues
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        oldVars oldVals := by
                    -- First lift through argTemp layer.
                    have Hstep1 :
                        ReadValues
                          (updatedStates σ
                            argTemps argVals)
                          oldVars oldVals := by
                      apply readValues_updatedStates
                      · rw [show argTemps.length =
                              argTrips.length from by
                              simp [argTemps, List.unzip_eq_map]]
                        exact Hargtriplen
                      · exact HoldVarsDisjArg
                      · exact HoldVals
                    -- Then lift through outTemp layer.
                    apply readValues_updatedStates
                    · rw [show outTemps.length =
                            outTrips.length from by
                            simp [outTemps, List.unzip_eq_map]]
                      exact Houttriplen
                    · exact HoldVarsDisjOut
                    · exact Hstep1
                  -- ReadValues precondition for H_initVars uses
                  -- oldTrips.unzip.snd; rewrite via HoldTripsSnd.
                  have HrdOldTrips :
                      ReadValues
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        oldTrips.unzip.snd oldVals := by
                    rw [HoldTripsSnd]
                    exact HrdOlds_outLayer
                  -- isNotDefined of genOldIdents in σ_out: genOldIdents
                  -- disjoint from argTemps and outTemps.
                  have HndefOld_outLayer :
                      Imperative.isNotDefined
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        genOldIdents := by
                    intro v Hv
                    have Hv_notin_out :
                        ¬ v ∈ outTemps := by
                      intro Hin
                      exact HoutOldDisj Hin Hv
                    have Hv_notin_arg :
                        ¬ v ∈ argTemps := by
                      intro Hin
                      exact HargOldDisj Hin Hv
                    rw [updatedStates_2layer_get_notin
                          Hv_notin_arg Hv_notin_out]
                    exact HndefOld_σ v Hv
                  -- isNotDefined precondition for H_initVars on
                  -- oldTrips.unzip.fst.unzip.fst.
                  have HndefOldTrips :
                      Imperative.isNotDefined
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        oldTrips.unzip.fst.unzip.fst := by
                    rw [HoldTripsFst]
                    exact HndefOld_outLayer
                  -- Nodup precondition: (genOldIdents ++ oldVars).Nodup.
                  have HoldTrips_nd_app :
                      List.Nodup
                        (oldTrips.unzip.fst.unzip.fst ++ oldTrips.unzip.snd) := by
                    rw [HoldTripsFst, HoldTripsSnd]
                    rw [List.nodup_append]
                    refine ⟨HoldNd, HoldVarsNd, ?_⟩
                    intro a Ha b Hb Heq
                    subst Heq
                    exact HoldVarsDisjOldT Hb Ha
                  have HL3 :
                      EvalStatementsContract π φ
                        ⟨updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals, δ, false⟩
                        (Core.Transform.createInitVars oldTrips md)
                        ⟨updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩ :=
                    H_initVars Hwfvars HoldTrips_nd_app HrdOldTrips
                      HndefOldTrips
                  -- D2: L4 (asserts), L5 (havocs), L6 (assumes) chain.
                  rw [Hsts_struct]
                  -- L5: build post-havoc store σ_havoc by applying HavocVars
                  -- segment-by-segment to σ' = σ.update lhs modvals.  Derive
                  -- HL5 directly:
                  have HlhsDef : Imperative.isDefined σ lhs :=
                    ReadValuesIsDefined Hevalouts
                  have Hhav_σ : HavocVars σ lhs σ' :=
                    UpdateStatesHavocVars Hupdate
                  have Hhav_arg :
                      HavocVars (updatedStates σ
                                  argTemps argVals)
                                lhs
                                (updatedStates σ'
                                  argTemps argVals) :=
                    havocVars_updatedStates_lift HlhsDisjArg Hhav_σ
                  have Hhav_out :
                      HavocVars
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        lhs
                        (updatedStates
                          (updatedStates σ'
                            argTemps argVals)
                          outTemps oVals) :=
                    havocVars_updatedStates_lift HlhsDisjOut Hhav_arg
                  have Hhav_old :
                      HavocVars
                        (updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals)
                        lhs
                        (updatedStates
                          (updatedStates
                            (updatedStates σ'
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals) := by
                    rw [HoldTripsFst]
                    apply havocVars_updatedStates_lift HlhsDisjOld Hhav_out
                  -- isDefined σ_old lhs (via 3-layer extension monotone).
                  have HlhsDef_arg :
                      Imperative.isDefined
                        (updatedStates σ
                          argTemps argVals) lhs := by
                    intro v Hv
                    have Hnotin :
                        ¬ v ∈ argTemps := by
                      intro Hin
                      exact HlhsDisjArg Hv Hin
                    rw [updatedStates_get_notin Hnotin]
                    exact HlhsDef v Hv
                  have HlhsDef_out :
                      Imperative.isDefined
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals) lhs := by
                    intro v Hv
                    have Hnotin :
                        ¬ v ∈ outTemps := by
                      intro Hin
                      exact HlhsDisjOut Hv Hin
                    rw [updatedStates_get_notin Hnotin]
                    exact HlhsDef_arg v Hv
                  have HlhsDef_old :
                      Imperative.isDefined
                        (updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals) lhs := by
                    intro v Hv
                    have Hnotin :
                        ¬ v ∈ oldTrips.unzip.fst.unzip.fst := by
                      rw [HoldTripsFst]
                      intro Hin
                      exact HlhsDisjOld Hv Hin
                    rw [updatedStates_get_notin Hnotin]
                    exact HlhsDef_out v Hv
                  -- HL5: havocs over `lhs` from σ_old to σ_havoc (same
                  -- 3-layer init applied to σ' instead of σ).  Use
                  -- `hCallArgsLhs.symm` to align with `CallArg.getLhs args`.
                  have HL5_pre :
                      EvalStatementsContract π φ
                        ⟨updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩
                        (Core.Transform.createHavocs lhs md)
                        ⟨updatedStates
                          (updatedStates
                            (updatedStates σ'
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩ :=
                    H_havocs Hwfvars HlhsDef_old Hhav_old
                  -- Equality: σ_havoc (3-layer applied to σ') = σ'' (flat).
                  -- Both yield the same store via updatedStates'App and
                  -- list-zip-append commutation.
                  have HoldFstLen :
                      oldTrips.unzip.fst.unzip.fst.length = oldVals.length := by
                    rw [HoldTripsFst, HgenOldLen, HoldValsLen]
                  have HoutFstLen :
                      outTemps.length = oVals.length := by
                    rw [show outTemps.length =
                            outTrips.length from by
                            simp [outTemps, List.unzip_eq_map]]
                    exact Houttriplen
                  have HargFstLen :
                      argTemps.length = argVals.length := by
                    rw [show argTemps.length =
                            argTrips.length from by
                            simp [argTemps, List.unzip_eq_map]]
                    exact Hargtriplen
                  have Hflatten_eq :
                      updatedStates σ'
                        (argTemps ++
                          outTemps ++ genOldIdents)
                        (argVals ++ oVals ++ oldVals) =
                      updatedStates
                        (updatedStates
                          (updatedStates σ'
                            argTemps argVals)
                          outTemps oVals)
                        oldTrips.unzip.fst.unzip.fst oldVals := by
                    rw [HoldTripsFst]
                    simp only [updatedStates]
                    -- (a ++ b ++ c).zip (av ++ bv ++ cv) = a.zip av ++ b.zip bv ++ c.zip cv.
                    have Hzip1 :
                        ((argTemps ++
                          outTemps) ++ genOldIdents).zip
                          ((argVals ++ oVals) ++ oldVals) =
                        (argTemps ++
                          outTemps).zip
                          (argVals ++ oVals) ++
                          genOldIdents.zip oldVals :=
                      List.zip_append (by
                        rw [List.length_append, List.length_append,
                            HargFstLen, HoutFstLen])
                    have Hzip2 :
                        (argTemps ++
                          outTemps).zip
                          (argVals ++ oVals) =
                        argTemps.zip argVals ++
                          outTemps.zip oVals :=
                      List.zip_append HargFstLen
                    rw [Hzip1, Hzip2]
                    rw [updatedStates'App, updatedStates'App]
                  have HL5 :
                      EvalStatementsContract π φ
                        ⟨updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩
                        (Core.Transform.createHavocs (CallArg.getLhs args) md)
                        ⟨updatedStates σ'
                          (argTemps ++
                            outTemps ++ genOldIdents)
                          (argVals ++ oVals ++ oldVals), δ, false⟩ := by
                    rw [Hflatten_eq, hCallArgsLhs]
                    exact HL5_pre
                  -- D2a: per-precondition payload for L4 (asserts).
                  have HprocEq : proc' = proc := by
                    have Hπ := Hp procName
                    -- Hπ : π procName = Program.Procedure.find? p ⟨procName, ()⟩
                    -- lkup : π procName = some proc
                    -- Hfind : Program.Procedure.find? p ⟨procName, ()⟩ = some proc'
                    rw [Hπ] at lkup
                    rw [Hfind] at lkup
                    -- lkup : some proc' = some proc
                    exact (Option.some_inj.mp lkup.symm).symm
                  -- Specialize the call-site hypothesis to the call form.
                  -- `Hwfcallsite` is over the call_sem `proc`;
                  -- the spike interface uses `proc'`, but `HprocEq`
                  -- bridges them where needed.
                  obtain ⟨HpreVarsFresh, HpostVarsFresh, HargVarsNotInLhs,
                          HinoutFresh, HargVarsNotInOutKeys,
                          HargVarsNotInInKeys, HoutAlign⟩ :=
                    Hwfcallsite.specialize (procName := procName)
                      (args := args) (md := md) rfl lkup
                  -- Lift HpostVarsFresh to take c ∈ proc'.spec.postconditions.values.
                  -- Bridges proc' = proc and unfolds getCheckExprs.
                  have HpostVarsFresh_via_c :
                      ∀ c ∈ proc'.spec.postconditions.values,
                      ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) c.expr,
                        ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
                        v ∉ CallArg.getLhs args := by
                    intro c Hc_in v Hv
                    have Hin_full :
                        c.expr ∈ Procedure.Spec.getCheckExprs
                                    proc.spec.postconditions := by
                      simp only [Procedure.Spec.getCheckExprs, List.mem_map]
                      refine ⟨c, ?_, rfl⟩
                      have Hc_in' := Hc_in
                      rw [HprocEq] at Hc_in'
                      rw [ListMap.values_eq_map_snd]
                      rw [ListMap.values_eq_map_snd] at Hc_in'
                      exact Hc_in'
                    exact HpostVarsFresh c.expr Hin_full v Hv
                  -- C-aux: hoisted disjointness facts (used by L4 + L6).
                  have HinputsFresh :
                      ∀ v ∈ proc.header.inputs.keys,
                        ¬ isTempIdent v ∧ ¬ isOldTempIdent v := by
                    intro v Hv
                    exact HinoutFresh v (List.mem_append.mpr (Or.inl Hv))
                  have HoutputsFresh :
                      ∀ v ∈ proc.header.outputs.keys,
                        ¬ isTempIdent v ∧ ¬ isOldTempIdent v := by
                    intro v Hv
                    exact HinoutFresh v (List.mem_append.mpr (Or.inr Hv))
                  -- inputs.keys ∩ argTemps = ∅ (inputs not tmp_).
                  have HinKeys_disj_argTemps :
                      proc.header.inputs.keys.Disjoint argTemps := by
                    intro v Hv1 Hv2
                    have HvNotTemp : ¬ isTempIdent v := (HinputsFresh v Hv1).1
                    have HvTemp : isTempIdent v :=
                      (List.Forall_mem_iff.mp HargTemp) v Hv2
                    exact HvNotTemp HvTemp
                  have HinKeys_disj_outTemps :
                      proc.header.inputs.keys.Disjoint outTemps := by
                    intro v Hv1 Hv2
                    have HvNotTemp : ¬ isTempIdent v := (HinputsFresh v Hv1).1
                    have HvTemp : isTempIdent v :=
                      (List.Forall_mem_iff.mp HoutTemp) v Hv2
                    exact HvNotTemp HvTemp
                  have HinKeys_disj_olds :
                      proc.header.inputs.keys.Disjoint genOldIdents := by
                    intro v Hv1 Hv2
                    have HvNotOld : ¬ isOldTempIdent v :=
                      (HinputsFresh v Hv1).2
                    have HvOld : isOldTempIdent v :=
                      (List.Forall_mem_iff.mp HoldIdentsTemp) v Hv2
                    exact HvNotOld HvOld
                  have HoutKeys_disj_argTemps :
                      proc.header.outputs.keys.Disjoint argTemps := by
                    intro v Hv1 Hv2
                    have HvNotTemp : ¬ isTempIdent v := (HoutputsFresh v Hv1).1
                    have HvTemp : isTempIdent v :=
                      (List.Forall_mem_iff.mp HargTemp) v Hv2
                    exact HvNotTemp HvTemp
                  have HoutKeys_disj_outTemps :
                      proc.header.outputs.keys.Disjoint outTemps := by
                    intro v Hv1 Hv2
                    have HvNotTemp : ¬ isTempIdent v := (HoutputsFresh v Hv1).1
                    have HvTemp : isTempIdent v :=
                      (List.Forall_mem_iff.mp HoutTemp) v Hv2
                    exact HvNotTemp HvTemp
                  have HoutKeys_disj_olds :
                      proc.header.outputs.keys.Disjoint genOldIdents := by
                    intro v Hv1 Hv2
                    have HvNotOld : ¬ isOldTempIdent v :=
                      (HoutputsFresh v Hv1).2
                    have HvOld : isOldTempIdent v :=
                      (List.Forall_mem_iff.mp HoldIdentsTemp) v Hv2
                    exact HvNotOld HvOld
                  -- inputs.keys ∩ lhs = ∅: σ-undefined inputs vs σ-defined lhs.
                  have HinKeys_disj_lhs :
                      proc.header.inputs.keys.Disjoint lhs := by
                    intro v Hv1 Hv2
                    have Hvσ_none : σ v = none :=
                      InitStatesNotDefined Hinitin v Hv1
                    have Hvσ_some : (σ v).isSome = true :=
                      HlhsDef v Hv2
                    rw [Hvσ_none] at Hvσ_some
                    simp at Hvσ_some
                  -- outputs.keys ∩ lhs = ∅: σA-undefined outputs vs σ-defined lhs.
                  have HoutKeys_disj_lhs :
                      proc.header.outputs.keys.Disjoint lhs := by
                    intro v Hv1 Hv2
                    have HvσA_none : σA v = none := Houtndef_io v Hv1
                    have HvNotInInputs : v ∉ proc.header.inputs.keys :=
                      fun h => Hiodisj h Hv1
                    have HvσA_eq_σ : σA v = σ v :=
                      initStates_get_notin Hinitin HvNotInInputs
                    have Hvσ_none : σ v = none := by
                      rw [← HvσA_eq_σ]; exact HvσA_none
                    have Hvσ_some : (σ v).isSome = true :=
                      HlhsDef v Hv2
                    rw [Hvσ_none] at Hvσ_some
                    simp at Hvσ_some
                  -- Restrict to the filtered preconditions.
                  let presFiltered : List (CoreLabel × Procedure.Check) :=
                    proc.spec.preconditions.filter
                      (fun (_, c) => c.attr ≠ .Free)
                  -- Filtered entry's expr ∈ getCheckExprs proc.spec.preconditions.
                  have HfilteredContains :
                      ∀ entry ∈ presFiltered,
                        (Procedure.Spec.getCheckExprs
                          proc.spec.preconditions).contains entry.snd.expr :=
                    fun entry Hentry => filterCheck_in_getCheckExprs Hentry
                  -- Bind σAO definedness/eval-tt for each filtered entry.
                  have HpreFiltered :
                      ∀ entry ∈ presFiltered,
                        Imperative.isDefinedOver
                          (Imperative.HasVarsPure.getVars (P:=Expression))
                          σAO entry.snd.expr ∧
                        δ σAO entry.snd.expr = some Imperative.HasBool.tt := by
                    intro entry Hentry
                    exact Hpre entry.snd.expr (HfilteredContains entry Hentry)
                  -- Pre-var freshness lemma against σ_old / σAO.
                  have HpresVarsFresh' :
                      ∀ entry ∈ presFiltered,
                        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr,
                          ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
                          v ∉ CallArg.getLhs args := fun entry Hentry v Hv =>
                    HpreVarsFresh entry.snd.expr
                      (filterCheck_mem_getCheckExprs Hentry) v Hv
                  -- HpresPayload (D2a output).
                  have HpresPayload :
                      ∀ entry ∈ presFiltered,
                        Imperative.invStores σAO
                          (updatedStates
                            (updatedStates
                              (updatedStates σ
                                argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals)
                          ((Imperative.HasVarsPure.getVars (P:=Expression)
                              entry.snd.expr).removeAll
                            ((proc.header.inputs.keys ++
                                proc.header.outputs.keys) ++
                              (argTemps ++ lhs))) ∧
                        (argTemps ++ lhs).Disjoint
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr) ∧
                        δ σAO entry.snd.expr = some Imperative.HasBool.tt := by
                    intro entry Hentry
                    -- Unpack per-entry facts.
                    have HpreEnt := HpreFiltered entry Hentry
                    -- preVars are not tmp_/old_ and not in lhs.
                    have HfreshEnt := HpresVarsFresh' entry Hentry
                    -- (1) Hpred_disj: (argT ++ lhs).Disjoint preVars.
                    have Hpred_disj :
                        (argTemps ++ lhs).Disjoint
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr) := by
                      intro x Hin1 Hin2
                      cases List.mem_append.mp Hin1 with
                      | inl HxArg =>
                        -- x ∈ argT (tmp_), x ∈ preVars (not tmp_).
                        have HxTemp : isTempIdent x :=
                          (List.Forall_mem_iff.mp HargTemp) x HxArg
                        have HxNotTemp : ¬ isTempIdent x :=
                          (HfreshEnt x Hin2).1
                        exact HxNotTemp HxTemp
                      | inr HxLhs =>
                        -- x ∈ lhs, x ∉ lhs (via Hpre_post_lhs_disj).
                        -- hCallArgsLhs : CallArg.getLhs args = lhs
                        have HxNotInLhs : x ∉ CallArg.getLhs args :=
                          (HfreshEnt x Hin2).2.2
                        -- HxLhs : x ∈ lhs, want: x ∈ CallArg.getLhs args.
                        rw [hCallArgsLhs] at HxNotInLhs
                        exact HxNotInLhs HxLhs
                    -- (2) Hinv: invStores σAO σ_old (preVars.removeAll ...).
                    have Hinv :
                        Imperative.invStores σAO
                          (updatedStates
                            (updatedStates
                              (updatedStates σ
                                argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals)
                          ((Imperative.HasVarsPure.getVars (P:=Expression)
                              entry.snd.expr).removeAll
                            ((proc.header.inputs.keys ++
                                proc.header.outputs.keys) ++
                              (argTemps ++ lhs))) := by
                      simp only [Imperative.invStores, Imperative.substStores]
                      intros k1 k2 Hkin
                      have Hk_eq := zip_self_eq Hkin
                      subst Hk_eq
                      have Hk1_in : k1 ∈
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr).removeAll
                            ((proc.header.inputs.keys ++
                                proc.header.outputs.keys) ++
                              (argTemps ++ lhs)) :=
                        (List.of_mem_zip Hkin).1
                      -- Decompose the removeAll membership.
                      have Hk1_inPre :
                          k1 ∈ Imperative.HasVarsPure.getVars
                                  (P:=Expression) entry.snd.expr ∧
                          k1 ∉ (proc.header.inputs.keys ++
                                  proc.header.outputs.keys) ++
                                (argTemps ++ lhs) := by
                        simp only [List.removeAll, List.mem_filter,
                                   List.elem_eq_mem, Bool.not_eq_true',
                                   decide_eq_false_iff_not] at Hk1_in
                        exact Hk1_in
                      obtain ⟨Hk1_pre, Hk1_notin⟩ := Hk1_inPre
                      obtain ⟨Hk1_notin_inputs, Hk1_notin_outputs,
                              Hk1_notin_argT, _Hk1_notin_lhs⟩ :=
                        List.notin_append4 Hk1_notin
                      -- preVar k1 fresh facts (not tmp_, not old_, not in lhs).
                      have HfreshK := HfreshEnt k1 Hk1_pre
                      have Hk1_notTemp : ¬ isTempIdent k1 := HfreshK.1
                      have Hk1_notOld : ¬ isOldTempIdent k1 := HfreshK.2.1
                      -- k1 ∉ outT (since outT are tmp_).
                      have Hk1_notin_outT :
                          k1 ∉ outTemps := fun h =>
                        Hk1_notTemp ((List.Forall_mem_iff.mp HoutTemp) k1 h)
                      -- k1 ∉ genOldIdents (since olds are old_).
                      have Hk1_notin_olds :
                          k1 ∉ genOldIdents := fun h =>
                        Hk1_notOld
                          ((List.Forall_mem_iff.mp HoldIdentsTemp) k1 h)
                      -- σ_old k1 = σ k1 by 3-layer fall-through.
                      have Hold_eq_σ :
                          (updatedStates
                            (updatedStates
                              (updatedStates σ
                                argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals) k1 = σ k1 := by
                        have Hk1_notin_oldFst :
                            k1 ∉ oldTrips.unzip.fst.unzip.fst := by
                          rw [HoldTripsFst]; exact Hk1_notin_olds
                        exact updatedStates_3layer_get_notin
                          Hk1_notin_argT Hk1_notin_outT Hk1_notin_oldFst
                      -- σAO k1 = σ k1 by InitStates fall-through.
                      have HAO_eq_σ : σAO k1 = σ k1 := by
                        -- σAO comes from σA via Hinitout (over outputs).
                        -- σA comes from σ via Hinitin (over inputs).
                        rw [initStates_get_notin Hinitout Hk1_notin_outputs,
                            initStates_get_notin Hinitin Hk1_notin_inputs]
                      -- Conclude: σAO k1 = σ_old k1.
                      rw [HAO_eq_σ, Hold_eq_σ]
                    refine ⟨Hinv, Hpred_disj, ?_⟩
                    exact HpreEnt.2
                  -- D2b: per-postcondition payload (HpostFiltered, HpostSubFresh).
                  let postsFiltered : List (CoreLabel × Procedure.Check) :=
                    proc.spec.postconditions.filter
                      (fun (_, c) => c.attr ≠ .Free)
                  -- Bridge: each filtered entry's expr is contained in
                  -- `getCheckExprs proc.spec.postconditions` (`.contains`
                  -- form, matching `Hpost`'s expected argument).
                  have HpostFilteredContains :
                      ∀ entry ∈ postsFiltered,
                        (Procedure.Spec.getCheckExprs
                          proc.spec.postconditions).contains entry.snd.expr :=
                    fun entry Hentry => filterCheck_in_getCheckExprs Hentry
                  -- Bind σO eval-tt for each filtered post entry.  Hpost
                  -- gives `isDefinedOver σAO post ∧ δ σO post = tt` over
                  -- the full getCheckExprs list.
                  have HpostFiltered :
                      ∀ entry ∈ postsFiltered,
                        Imperative.isDefinedOver
                          (Imperative.HasVarsPure.getVars (P:=Expression))
                          σAO entry.snd.expr ∧
                        δ σO entry.snd.expr = some Imperative.HasBool.tt := by
                    intro entry Hentry
                    exact Hpost entry.snd.expr (HpostFilteredContains entry Hentry)
                  -- Post-var freshness lemma against ORIGINAL post (pre-oldSubst).
                  have HpostsVarsFresh_orig :
                      ∀ entry ∈ postsFiltered,
                        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr,
                          ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
                          v ∉ CallArg.getLhs args := fun entry Hentry v Hv =>
                    HpostVarsFresh entry.snd.expr
                      (filterCheck_mem_getCheckExprs Hentry) v Hv
                  -- D2c: σ_R1 + L6 substStores/substDefined facts.
                  let σ_R1 : CoreStore :=
                    updatedStates σO genOldIdents oldVals
                  -- σ_havoc abbreviation (matches HL5's RHS).
                  let σ_havoc : CoreStore :=
                    updatedStates σ'
                      (argTemps ++
                        outTemps ++ genOldIdents)
                      (argVals ++ oVals ++ oldVals)
                  -- Filtered argument substitution shape.  Matches
                  -- `arg_subst_filtered` in `callElimCmd` (CallElim.lean:133).
                  let filtered_argSubst :
                      List (Expression.Ident × Expression.Ident) :=
                    (proc.header.inputs.keys.zip argTemps).filter
                      (fun pr =>
                        ¬ (proc.header.outputs.keys).contains pr.1)
                  let filtered_inputs : List Expression.Ident :=
                    filtered_argSubst.unzip.fst
                  let filtered_argTemps : List Expression.Ident :=
                    filtered_argSubst.unzip.snd
                  let filtered_ks : List Expression.Ident :=
                    proc.header.outputs.keys ++ filtered_inputs
                  let filtered_ks' : List Expression.Ident :=
                    lhs ++ filtered_argTemps
                  -- Pre-filter zip lengths agree (inputs.keys.length =
                  -- argTemps.length).  Hinitin → InitStatesLength gives
                  -- inputs.keys.length = argVals.length, and Hargtriplen
                  -- gives argTemps.length = argVals.length.
                  have HinKeys_argTemps_len :
                      proc.header.inputs.keys.length = argTemps.length := by
                    have H1 : proc.header.inputs.keys.length =
                                argVals.length := InitStatesLength Hinitin
                    have H2 : argTemps.length = argVals.length := by
                      show argTemps.length = argVals.length
                      simp [argTemps, List.unzip_eq_map, Hargtriplen]
                    omega
                  -- The pre-filter zip's unzip is exactly (inputs.keys,
                  -- argTemps); the filter doesn't break the length-match.
                  have Hzip_unzip :
                      (proc.header.inputs.keys.zip argTemps).unzip =
                      (proc.header.inputs.keys, argTemps) := by
                    apply List.unzip_zip
                    exact HinKeys_argTemps_len
                  -- Filter sub-membership: each (id, t) ∈ filtered_argSubst
                  -- is in the original zip and satisfies the filter.
                  have Hfilter_in :
                      ∀ pr ∈ filtered_argSubst,
                        pr ∈ proc.header.inputs.keys.zip argTemps ∧
                        pr.1 ∉ proc.header.outputs.keys := by
                    intro pr Hpr
                    have := List.mem_filter.mp Hpr
                    refine ⟨this.1, ?_⟩
                    have Hbool := this.2
                    simp [List.contains_iff_mem] at Hbool
                    exact Hbool
                  -- Length symmetry of filtered halves.
                  have Hfilt_len_sym :
                      filtered_inputs.length = filtered_argTemps.length := by
                    show filtered_argSubst.unzip.fst.length =
                          filtered_argSubst.unzip.snd.length
                    simp [List.unzip_eq_map]
                  -- Outputs ↔ lhs length: from Hinitout (outputs.length =
                  -- oVals.length) plus Hevalouts (lhs.length = oVals.length).
                  have HoutKeys_lhs_len :
                      proc.header.outputs.keys.length = lhs.length := by
                    have H1 : proc.header.outputs.keys.length = oVals.length :=
                      InitStatesLength Hinitout
                    have H2 : lhs.length = oVals.length :=
                      ReadValuesLength Hevalouts
                    omega
                  -- Hkslen (Goal #4):
                  --   filtered_ks.length = filtered_ks'.length.
                  have Hkslen :
                      filtered_ks.length = filtered_ks'.length := by
                    show (proc.header.outputs.keys ++
                          filtered_inputs).length =
                         (lhs ++ filtered_argTemps).length
                    rw [List.length_append, List.length_append,
                        HoutKeys_lhs_len, Hfilt_len_sym]
                  -- (HinputsFresh/HoutputsFresh and inputs/outputs vs
                  --  argTemps/outTemps/olds disjointness hoisted to C-aux.)
                  -- filtered_inputs ⊆ inputs.keys (via the filter zip path).
                  have Hfilt_in_eq_map :
                      filtered_inputs = filtered_argSubst.map Prod.fst := by
                    show filtered_argSubst.unzip.fst = _
                    simp [List.unzip_eq_map]
                  have Hfilt_argT_eq_map :
                      filtered_argTemps = filtered_argSubst.map Prod.snd := by
                    show filtered_argSubst.unzip.snd = _
                    simp [List.unzip_eq_map]
                  have Hfilt_in_sub_inputs :
                      ∀ v ∈ filtered_inputs, v ∈ proc.header.inputs.keys := by
                    intro v Hv
                    have Hv' : v ∈ filtered_argSubst.map Prod.fst :=
                      Hfilt_in_eq_map ▸ Hv
                    rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
                    have HinZip := (Hfilter_in pr Hpr_in).1
                    have Hofzip := List.of_mem_zip HinZip
                    rw [← Hpr_eq]
                    exact Hofzip.1
                  have Hfilt_argT_sub_argTemps :
                      ∀ v ∈ filtered_argTemps, v ∈ argTemps := by
                    intro v Hv
                    have Hv' : v ∈ filtered_argSubst.map Prod.snd :=
                      Hfilt_argT_eq_map ▸ Hv
                    rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
                    have HinZip := (Hfilter_in pr Hpr_in).1
                    have Hofzip := List.of_mem_zip HinZip
                    rw [← Hpr_eq]
                    exact Hofzip.2
                  have Hfilt_in_disj_outs :
                      filtered_inputs.Disjoint proc.header.outputs.keys := by
                    intro v Hv1 Hv2
                    have Hv' : v ∈ filtered_argSubst.map Prod.fst :=
                      Hfilt_in_eq_map ▸ Hv1
                    rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
                    have HnotIn := (Hfilter_in pr Hpr_in).2
                    rw [Hpr_eq] at HnotIn
                    exact HnotIn Hv2
                  -- Hnd: substNodup of filtered_ks.zip filtered_ks'.
                  have Hnd : Imperative.substNodup
                      (filtered_ks.zip filtered_ks') := by
                    -- Unfold substNodup; rewrite via unzip_zip.
                    have HzipUnzip :
                        (filtered_ks.zip filtered_ks').unzip =
                          (filtered_ks, filtered_ks') :=
                      List.unzip_zip Hkslen
                    show ((filtered_ks.zip filtered_ks').unzip.fst ++
                          (filtered_ks.zip filtered_ks').unzip.snd).Nodup
                    rw [HzipUnzip]
                    -- Now goal: (filtered_ks ++ filtered_ks').Nodup.
                    show ((proc.header.outputs.keys ++ filtered_inputs) ++
                          (lhs ++ filtered_argTemps)).Nodup
                    -- ((outs ++ filt_in) ++ (lhs ++ filt_argT)).Nodup: each
                    -- Nodup + pairwise disjoints (C-aux supplies most).
                    have Hfilt_in_disj_lhs :
                        filtered_inputs.Disjoint lhs := by
                      intro v Hv1 Hv2
                      exact HinKeys_disj_lhs (Hfilt_in_sub_inputs v Hv1) Hv2
                    -- outs ∩ filt_argT: filt_argT ⊆ argTemps.
                    -- outputs ∩ argTemps = ∅ (HoutKeys_disj_argTemps).
                    have HoutKeys_disj_filt_argT :
                        proc.header.outputs.keys.Disjoint
                          filtered_argTemps := by
                      intro v Hv1 Hv2
                      exact HoutKeys_disj_argTemps Hv1
                        (Hfilt_argT_sub_argTemps v Hv2)
                    -- filt_in ∩ filt_argT: subsets of inputs / argTemps.
                    have Hfilt_in_disj_filt_argT :
                        filtered_inputs.Disjoint filtered_argTemps := by
                      intro v Hv1 Hv2
                      exact HinKeys_disj_argTemps
                        (Hfilt_in_sub_inputs v Hv1)
                        (Hfilt_argT_sub_argTemps v Hv2)
                    -- lhs ∩ filt_argT: lhs ∩ argTemps = ∅ (HlhsDisjArg).
                    have Hlhs_disj_filt_argT :
                        lhs.Disjoint filtered_argTemps := by
                      intro v Hv1 Hv2
                      exact HlhsDisjArg Hv1
                        (Hfilt_argT_sub_argTemps v Hv2)
                    -- Underlying full-zip has Pairwise distinct fst
                    -- (via inputs.keys.Nodup), so its filter has the
                    -- same Pairwise property, hence (filter).map fst
                    -- has Pairwise (· ≠ ·) i.e. Nodup.
                    have Hin_nd_pw :
                        List.Pairwise
                          (· ≠ ·) proc.header.inputs.keys :=
                      List.nodup_iff_pairwise_ne.mp Hinnd_io
                    have HargT_nd_pw :
                        List.Pairwise (· ≠ ·) argTemps :=
                      List.nodup_iff_pairwise_ne.mp HargNd
                    -- Pairwise-distinct on the full zip.
                    have Hzip_pw_fst :
                        List.Pairwise
                          (fun (p q :
                              Expression.Ident × Expression.Ident) =>
                            p.1 ≠ q.1)
                          (proc.header.inputs.keys.zip argTemps) := by
                      -- Lift via pairwise_map + map_fst_zip from inputs.keys Pairwise.
                      rw [show (fun (p q : Expression.Ident × Expression.Ident) =>
                                  p.1 ≠ q.1) =
                            (fun p q => Prod.fst p ≠ Prod.fst q) from rfl]
                      rw [← List.pairwise_map]
                      rw [List.map_fst_zip
                            (Nat.le_of_eq HinKeys_argTemps_len)]
                      exact Hin_nd_pw
                    have Hzip_pw_snd :
                        List.Pairwise
                          (fun (p q :
                              Expression.Ident × Expression.Ident) =>
                            p.2 ≠ q.2)
                          (proc.header.inputs.keys.zip argTemps) := by
                      rw [show (fun (p q : Expression.Ident × Expression.Ident) =>
                                  p.2 ≠ q.2) =
                            (fun p q => Prod.snd p ≠ Prod.snd q) from rfl]
                      rw [← List.pairwise_map]
                      rw [List.map_snd_zip
                            (Nat.le_of_eq HinKeys_argTemps_len.symm)]
                      exact HargT_nd_pw
                    -- Filter preserves Pairwise (sublist).
                    have Hfilt_pw_fst :
                        List.Pairwise
                          (fun (p q :
                              Expression.Ident × Expression.Ident) =>
                            p.1 ≠ q.1)
                          filtered_argSubst :=
                      List.Pairwise.sublist List.filter_sublist Hzip_pw_fst
                    have Hfilt_pw_snd :
                        List.Pairwise
                          (fun (p q :
                              Expression.Ident × Expression.Ident) =>
                            p.2 ≠ q.2)
                          filtered_argSubst :=
                      List.Pairwise.sublist List.filter_sublist Hzip_pw_snd
                    have Hfilt_in_nodup : filtered_inputs.Nodup := by
                      show filtered_argSubst.unzip.fst.Nodup
                      simp [List.unzip_eq_map]
                      rw [List.nodup_iff_pairwise_ne]
                      rw [List.pairwise_map]
                      exact Hfilt_pw_fst
                    have Hfilt_argT_nodup : filtered_argTemps.Nodup := by
                      show filtered_argSubst.unzip.snd.Nodup
                      simp [List.unzip_eq_map]
                      rw [List.nodup_iff_pairwise_ne]
                      rw [List.pairwise_map]
                      exact Hfilt_pw_snd
                    -- Step: assemble (filtered_ks ++ filtered_ks').Nodup.
                    -- = (outputs ++ filtered_inputs ++ lhs ++ filtered_argTemps).Nodup.
                    rw [List.nodup_append]
                    refine ⟨?_, ?_, ?_⟩
                    · -- (outputs ++ filtered_inputs).Nodup.
                      rw [List.nodup_append]
                      refine ⟨Houtnd_io, Hfilt_in_nodup, ?_⟩
                      intro a Ha b Hb Heq
                      subst Heq
                      exact Hfilt_in_disj_outs Hb Ha
                    · -- (lhs ++ filtered_argTemps).Nodup.
                      rw [List.nodup_append]
                      refine ⟨HlhsNd, Hfilt_argT_nodup, ?_⟩
                      intro a Ha b Hb Heq
                      subst Heq
                      exact Hlhs_disj_filt_argT Ha Hb
                    · -- (outputs ++ filtered_inputs).Disjoint
                      --   (lhs ++ filtered_argTemps).
                      intro a Ha b Hb Heq
                      subst Heq
                      cases List.mem_append.mp Ha with
                      | inl HaOuts =>
                        cases List.mem_append.mp Hb with
                        | inl HbLhs =>
                          exact HoutKeys_disj_lhs HaOuts HbLhs
                        | inr HbArgT =>
                          exact HoutKeys_disj_filt_argT HaOuts HbArgT
                      | inr HaIn =>
                        cases List.mem_append.mp Hb with
                        | inl HbLhs =>
                          exact Hfilt_in_disj_lhs HaIn HbLhs
                        | inr HbArgT =>
                          exact Hfilt_in_disj_filt_argT HaIn HbArgT
                  -- Hdef: substDefined σ_R1 σ_havoc.
                  have HσO_def_outs :
                      Imperative.isDefined σO proc.header.outputs.keys := by
                    apply HavocVarsDefMonotone ?_ Hhav1
                    exact InitStatesDefined Hinitout
                  have HσO_def_inputs :
                      Imperative.isDefined σO proc.header.inputs.keys := by
                    apply HavocVarsDefMonotone ?_ Hhav1
                    apply InitStatesDefMonotone ?_ Hinitout
                    exact InitStatesDefined Hinitin
                  have Hσ_R1_def_outs :
                      Imperative.isDefined σ_R1 proc.header.outputs.keys := by
                    intro v Hv
                    show (updatedStates σO genOldIdents oldVals v).isSome = true
                    rw [updatedStates_get_notin
                      (HoutKeys_disj_olds Hv : v ∉ genOldIdents)]
                    exact HσO_def_outs v Hv
                  have Hσ_R1_def_filt_in :
                      Imperative.isDefined σ_R1 filtered_inputs := by
                    intro v Hv
                    show (updatedStates σO genOldIdents oldVals v).isSome = true
                    have Hv_in : v ∈ proc.header.inputs.keys :=
                      Hfilt_in_sub_inputs v Hv
                    rw [updatedStates_get_notin
                      (HinKeys_disj_olds Hv_in : v ∉ genOldIdents)]
                    exact HσO_def_inputs v Hv_in
                  -- σ_havoc definedness on lhs.
                  have Hσ_havoc_def_lhs :
                      Imperative.isDefined σ_havoc lhs := by
                    intro v Hv
                    show (updatedStates σ'
                      (argTemps ++
                        outTemps ++ genOldIdents)
                      (argVals ++ oVals ++ oldVals) v).isSome = true
                    have Hv_notin :
                        v ∉ argTemps ++
                              outTemps ++ genOldIdents := by
                      intro h
                      cases List.mem_append.mp h with
                      | inl h2 =>
                        cases List.mem_append.mp h2 with
                        | inl hArg =>
                          exact HlhsDisjArg Hv hArg
                        | inr hOut =>
                          exact HlhsDisjOut Hv hOut
                      | inr hOld =>
                        exact HlhsDisjOld Hv hOld
                    rw [updatedStates_get_notin Hv_notin]
                    -- σ' v isSome via UpdateStates' definedness on lhs.
                    have Hσ'def : Imperative.isDefined σ' lhs := by
                      have Hh := UpdateStatesHavocVars Hupdate
                      exact HavocVarsDefined Hh
                    exact Hσ'def v Hv
                  -- σ_havoc definedness on filtered_argTemps.
                  have Hσ_havoc_def_filt_argT :
                      Imperative.isDefined σ_havoc filtered_argTemps := by
                    intro v Hv
                    have Hv_argT : v ∈ argTemps :=
                      Hfilt_argT_sub_argTemps v Hv
                    -- σ_havoc[v]: v ∈ argTemps, layer 1 of σ_havoc writes
                    -- argTemps to argVals.  Use updatedStatesDefined on
                    -- (argTemps ++ outTemps ++ olds) over argVals++oVals++oldVals.
                    show (updatedStates σ'
                      (argTemps ++
                        outTemps ++ genOldIdents)
                      (argVals ++ oVals ++ oldVals) v).isSome = true
                    apply updatedStatesDefined
                    · -- length of (argT++outT++olds) = length of vals.
                      have HgenOldValsLen :
                          genOldIdents.length = oldVals.length := by
                        rw [HgenOldLen, ← HoldValsLen]
                      simp [argTemps, outTemps, List.length_append, List.unzip_eq_map,
                            Hargtriplen, Houttriplen, HgenOldValsLen]
                    · simp only [List.mem_append]
                      exact Or.inl (Or.inl Hv_argT)
                  -- Now assemble Hdef.
                  have Hdef : Imperative.substDefined σ_R1 σ_havoc
                      (filtered_ks.zip filtered_ks') := by
                    intro k1 k2 Hkin
                    have Hpair_in_fst : k1 ∈ filtered_ks :=
                      (List.of_mem_zip Hkin).1
                    have Hpair_in_snd : k2 ∈ filtered_ks' :=
                      (List.of_mem_zip Hkin).2
                    refine ⟨?_, ?_⟩
                    · -- (σ_R1 k1).isSome.
                      cases List.mem_append.mp Hpair_in_fst with
                      | inl Hk1_outs => exact Hσ_R1_def_outs k1 Hk1_outs
                      | inr Hk1_in => exact Hσ_R1_def_filt_in k1 Hk1_in
                    · -- (σ_havoc k2).isSome.
                      cases List.mem_append.mp Hpair_in_snd with
                      | inl Hk2_lhs => exact Hσ_havoc_def_lhs k2 Hk2_lhs
                      | inr Hk2_aT => exact Hσ_havoc_def_filt_argT k2 Hk2_aT
                  -- Hsubst: substStores σ_R1 σ_havoc.
                  have Hσ'_eq : σ' = updatedStates σ lhs modvals :=
                    UpdateStatesUpdated Hupdate
                  -- modvals length = lhs length.
                  have HmodvalsLen : modvals.length = lhs.length := by
                    have := UpdateStatesLength Hupdate
                    omega
                  -- σO outputs = modvals (via Hrd).
                  -- σO inputs = σA inputs (via the σAO/σA fall-through chain).
                  -- σ_havoc on lhs = σ' lhs.
                  have Hσ_havoc_lhs_eq :
                      ∀ v ∈ lhs, σ_havoc v = σ' v := by
                    intro v Hv
                    have Hv_notin :
                        v ∉ argTemps ++
                              outTemps ++ genOldIdents := by
                      intro h
                      cases List.mem_append.mp h with
                      | inl h2 =>
                        cases List.mem_append.mp h2 with
                        | inl hArg => exact HlhsDisjArg Hv hArg
                        | inr hOut => exact HlhsDisjOut Hv hOut
                      | inr hOld => exact HlhsDisjOld Hv hOld
                    show updatedStates σ'
                      (argTemps ++
                        outTemps ++ genOldIdents)
                      (argVals ++ oVals ++ oldVals) v = σ' v
                    exact updatedStates_get_notin Hv_notin
                  -- σ_R1 on outputs = σO on outputs.
                  have Hσ_R1_outs_eq :
                      ∀ v ∈ proc.header.outputs.keys, σ_R1 v = σO v := by
                    intro v Hv
                    show updatedStates σO genOldIdents oldVals v = σO v
                    exact updatedStates_get_notin (HoutKeys_disj_olds Hv)
                  -- σ_R1 on inputs = σO on inputs.
                  have Hσ_R1_ins_eq :
                      ∀ v ∈ proc.header.inputs.keys, σ_R1 v = σO v := by
                    intro v Hv
                    show updatedStates σO genOldIdents oldVals v = σO v
                    exact updatedStates_get_notin (HinKeys_disj_olds Hv)
                  -- σO on inputs = σA on inputs (Hhav1 preserves on non-outputs;
                  -- Hinitout preserves on non-outputs).
                  have HσO_ins_eq_σA :
                      ∀ v ∈ proc.header.inputs.keys, σO v = σA v := by
                    intro v Hv
                    -- σO = updatedStates σAO outputs.keys outVals_havoc
                    --   (via HavocVarsUpdateStates Hhav1 + UpdateStatesUpdated).
                    have Hhav_up := HavocVarsUpdateStates Hhav1
                    rcases Hhav_up with ⟨ovh, Hup_havoc⟩
                    have HσO_eq : σO = updatedStates σAO
                                    proc.header.outputs.keys ovh :=
                      UpdateStatesUpdated Hup_havoc
                    have Hv_notin_outs : v ∉ proc.header.outputs.keys :=
                      fun h => Hiodisj Hv h
                    rw [HσO_eq, updatedStates_get_notin Hv_notin_outs]
                    -- σAO v = σA v via initStates_get_notin Hinitout.
                    exact initStates_get_notin Hinitout Hv_notin_outs
                  -- σA on inputs = positional argVals (via Hinitin).
                  -- Use ReadValues σA inputs.keys argVals from
                  -- InitStatesReadValues Hinitin.
                  have HrdA : ReadValues σA proc.header.inputs.keys argVals :=
                    InitStatesReadValues Hinitin
                  -- ── Build Hsubst via per-pair direct argument ──
                  -- (k1, k2) ∈ filtered_ks.zip filtered_ks' is either an
                  -- output-pair (outputs.keys[i], lhs[i]) or input-pair
                  -- (filtered_inputs[j], filtered_argTemps[j]).
                  have HinKeys_argVals_len :
                      proc.header.inputs.keys.length = argVals.length :=
                    InitStatesLength Hinitin
                  -- Length: zip (inputs ↔ argTemps) ↔ argVals lengths align.
                  have Hzip_argV_len :
                      (proc.header.inputs.keys.zip argTemps).length =
                        argVals.length := by
                    rw [List.length_zip, HinKeys_argTemps_len, Nat.min_self]
                    omega
                  -- Build Hsubst via parallel ReadValues.
                  have HinKVlen :
                      proc.header.inputs.keys.length = argVals.length :=
                    InitStatesLength Hinitin
                  have HargT_len_argV :
                      argTemps.length = argVals.length := by
                    rw [← HinKeys_argTemps_len]; exact HinKVlen
                  -- σ_R1 reads inputs.keys → argVals (full).
                  have Hrd_R1_in_full :
                      ReadValues σ_R1 proc.header.inputs.keys argVals := by
                    apply readValues_updatedStates
                    · rw [HgenOldLen, HoldValsLen]
                    · exact HinKeys_disj_olds
                    · -- ReadValues σO inputs.keys argVals.
                      have HrdAO :
                          ReadValues σAO proc.header.inputs.keys argVals := by
                        apply InitStatesReadValuesMonotone (σ:=σA) ?_ Hinitout
                        exact InitStatesReadValues Hinitin
                      have Hh1 := HavocVarsUpdateStates Hhav1
                      rcases Hh1 with ⟨ovh, Hup_havoc⟩
                      apply UpdateStatesReadValuesMonotone (σ:=σAO) _
                              ?_ Hup_havoc
                      · exact Hinoutnd
                      · exact HrdAO
                  -- σ_R1 reads outputs.keys → modvals (full).
                  have Hrd_R1_outs :
                      ReadValues σ_R1 proc.header.outputs.keys modvals := by
                    apply readValues_updatedStates
                    · rw [HgenOldLen, HoldValsLen]
                    · exact HoutKeys_disj_olds
                    · exact Hrd
                  -- σ_havoc reads argTemps → argVals (layer-1).
                  have Hrd_havoc_argT :
                      ReadValues σ_havoc argTemps argVals := by
                    show ReadValues
                      (updatedStates σ'
                        (argTemps ++
                          outTemps ++ genOldIdents)
                        (argVals ++ oVals ++ oldVals))
                      argTemps argVals
                    rw [Hflatten_eq]
                    have HargF_σ' :
                        ReadValues
                          (updatedStates σ' argTemps argVals)
                          argTemps argVals := by
                      apply readValues_updatedStatesSame
                      · exact HargFstLen
                      · exact HargNd
                    have HargF_step1 :
                        ReadValues
                          (updatedStates
                            (updatedStates σ' argTemps argVals)
                            outTemps oVals) argTemps argVals := by
                      apply readValues_updatedStates
                      · exact HoutFstLen
                      · exact HargOutDisj
                      · exact HargF_σ'
                    have HargF_step2 :
                        ReadValues
                          (updatedStates
                            (updatedStates
                              (updatedStates σ' argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals)
                          argTemps argVals := by
                      rw [HoldTripsFst]
                      apply readValues_updatedStates
                      · -- length: genOldIdents.length = oldVals.length.
                        rw [HgenOldLen, ← HoldValsLen]
                      · exact HargOldDisj
                      · exact HargF_step1
                    exact HargF_step2
                  -- σ_havoc reads lhs → modvals (fall-through to σ').
                  have HmodvalsLen' : lhs.length = modvals.length := by
                    have := UpdateStatesLength Hupdate; omega
                  have Hrd_havoc_lhs :
                      ReadValues σ_havoc lhs modvals := by
                    apply readValues_updatedStates
                    · have HgenOldValsLen :
                          genOldIdents.length = oldVals.length := by
                        rw [HgenOldLen, ← HoldValsLen]
                      simp [argTemps, outTemps, List.length_append, List.unzip_eq_map,
                            Hargtriplen, Houttriplen, HgenOldValsLen]
                    · intro v Hv1 Hv2
                      cases List.mem_append.mp Hv2 with
                      | inl h => cases List.mem_append.mp h with
                        | inl ha => exact HlhsDisjArg Hv1 ha
                        | inr ho => exact HlhsDisjOut Hv1 ho
                      | inr ho => exact HlhsDisjOld Hv1 ho
                    · rw [Hσ'_eq]
                      exact readValues_updatedStatesSame HmodvalsLen' HlhsNd
                  -- Filtered halves via the triple zip.
                  have Hsubst : Imperative.substStores σ_R1 σ_havoc
                      (filtered_ks.zip filtered_ks') := by
                    intro k1 k2 Hkin
                    show σ_R1 k1 = σ_havoc k2
                    -- (k1, k2) ∈ filtered_ks.zip filtered_ks'.
                    -- Get the underlying pair shape: either output-pair
                    -- or filtered-input-pair.
                    rcases List.mem_iff_get.mp Hkin with ⟨n, Hn⟩
                    have Hn_lt_zip : n.val < (filtered_ks.zip filtered_ks').length :=
                      n.isLt
                    have Hzip_len :
                        (filtered_ks.zip filtered_ks').length =
                          filtered_ks.length := by
                      simp [List.length_zip, Hkslen]
                    have Hn_lt_ks : n.val < filtered_ks.length := by omega
                    have Hn_lt_ks' : n.val < filtered_ks'.length := by
                      rw [← Hkslen]; exact Hn_lt_ks
                    -- Project (k1, k2) via getElem_zip.
                    have Hzip_get :
                        (filtered_ks.zip filtered_ks')[n.val]'Hn_lt_zip =
                          (filtered_ks[n.val]'Hn_lt_ks,
                           filtered_ks'[n.val]'Hn_lt_ks') :=
                      List.getElem_zip
                    have HnGE :
                        (filtered_ks.zip filtered_ks')[n.val]'Hn_lt_zip =
                          (k1, k2) := by
                      have HhE := Hn
                      have : (filtered_ks.zip filtered_ks').get n =
                              (filtered_ks.zip filtered_ks')[n.val]'Hn_lt_zip :=
                        rfl
                      rw [this] at HhE
                      exact HhE
                    have Hk1_eq : k1 = filtered_ks[n.val]'Hn_lt_ks := by
                      have := HnGE
                      rw [Hzip_get] at this
                      exact ((Prod.mk.injEq _ _ _ _).mp this.symm).1
                    have Hk2_eq : k2 = filtered_ks'[n.val]'Hn_lt_ks' := by
                      have := HnGE
                      rw [Hzip_get] at this
                      exact ((Prod.mk.injEq _ _ _ _).mp this.symm).2
                    by_cases Hsplit : n.val < proc.header.outputs.keys.length
                    · -- Output-half.
                      have Hks_app_lt :
                          n.val < (proc.header.outputs.keys ++
                                    filtered_inputs).length := by
                        rw [List.length_append]; omega
                      have HoutLhsLen : n.val < lhs.length := by
                        rw [← HoutKeys_lhs_len]; exact Hsplit
                      have Hks'_app_lt :
                          n.val < (lhs ++ filtered_argTemps).length := by
                        rw [List.length_append]; omega
                      have Hk1_app :
                          k1 = proc.header.outputs.keys[n.val]'Hsplit := by
                        rw [Hk1_eq]
                        show (proc.header.outputs.keys ++
                              filtered_inputs)[n.val]'_ = _
                        rw [List.getElem_append_left (h := Hsplit)]
                      have Hk2_app : k2 = lhs[n.val]'HoutLhsLen := by
                        rw [Hk2_eq]
                        show (lhs ++ filtered_argTemps)[n.val]'_ = _
                        rw [List.getElem_append_left (h := HoutLhsLen)]
                      -- σ_R1 k1 = some modvals[n.val] (via Hrd_R1_outs).
                      have HmodLen_outs :
                          n.val < modvals.length := by
                        have := ReadValuesLength Hrd_R1_outs; omega
                      have HrdR1_get :
                          σ_R1 (proc.header.outputs.keys[n.val]'Hsplit) =
                            some (modvals[n.val]'HmodLen_outs) := by
                        have HG := readValues_get
                          (σ:=σ_R1) (ks:=proc.header.outputs.keys)
                          (vs:=modvals) Hrd_R1_outs
                          (i:=n.val) (hi:=Hsplit) (hi':=HmodLen_outs)
                        exact HG
                      have HrdHavoc_get :
                          σ_havoc (lhs[n.val]'HoutLhsLen) =
                            some (modvals[n.val]'HmodLen_outs) := by
                        have HG := readValues_get
                          (σ:=σ_havoc) (ks:=lhs) (vs:=modvals)
                          Hrd_havoc_lhs
                          (i:=n.val) (hi:=HoutLhsLen) (hi':=HmodLen_outs)
                        exact HG
                      rw [Hk1_app, HrdR1_get, Hk2_app, HrdHavoc_get]
                    · -- Input-half.
                      have Hsplit_le : proc.header.outputs.keys.length ≤ n.val :=
                        Nat.le_of_not_lt Hsplit
                      have Hlhs_le : lhs.length ≤ n.val := by
                        rw [← HoutKeys_lhs_len]; exact Hsplit_le
                      have Hk1_app :
                          k1 = filtered_inputs[n.val -
                              proc.header.outputs.keys.length]'(by
                            have Hl : filtered_ks.length =
                                proc.header.outputs.keys.length +
                                  filtered_inputs.length :=
                              List.length_append
                            omega) := by
                        rw [Hk1_eq]
                        show (proc.header.outputs.keys ++
                              filtered_inputs)[n.val]'_ = _
                        rw [List.getElem_append_right (h₁ := Hsplit_le)]
                      have Hk2_app :
                          k2 = filtered_argTemps[n.val - lhs.length]'(by
                            have Hl : filtered_ks'.length =
                                lhs.length + filtered_argTemps.length :=
                              List.length_append
                            omega) := by
                        rw [Hk2_eq]
                        show (lhs ++ filtered_argTemps)[n.val]'_ = _
                        rw [List.getElem_append_right (h₁ := Hlhs_le)]
                      -- The two filtered halves' indices line up:
                      --   n - outputs.length = n - lhs.length (by HoutKeys_lhs_len).
                      have Hidx_eq :
                          n.val - proc.header.outputs.keys.length =
                          n.val - lhs.length := by
                        rw [HoutKeys_lhs_len]
                      let j : Nat :=
                        n.val - proc.header.outputs.keys.length
                      have Hj_lt_filt :
                          j < filtered_inputs.length := by
                        have Hl : filtered_ks.length =
                            proc.header.outputs.keys.length +
                              filtered_inputs.length :=
                          List.length_append
                        omega
                      have Hj_lt_argT :
                          j < filtered_argTemps.length := by
                        rw [← Hfilt_len_sym]; exact Hj_lt_filt
                      have Hj_lt_subst :
                          j < filtered_argSubst.length := by
                        show j < filtered_argSubst.length
                        rw [show filtered_argSubst.length =
                            filtered_argSubst.unzip.fst.length from by
                            simp [List.unzip_eq_map]]
                        exact Hj_lt_filt
                      -- Pair at index j in filtered_argSubst is (k1, k2).
                      have HpairAtJ :
                          filtered_argSubst[j]'Hj_lt_subst = (k1, k2) := by
                        -- filtered_inputs[j] = (filtered_argSubst[j]).fst.
                        have HfilGetFst :
                            filtered_inputs[j]'Hj_lt_filt =
                            (filtered_argSubst[j]'Hj_lt_subst).fst := by
                          show filtered_argSubst.unzip.fst[j]'_ = _
                          simp [List.unzip_eq_map]
                        have HfilGetSnd :
                            filtered_argTemps[j]'Hj_lt_argT =
                            (filtered_argSubst[j]'Hj_lt_subst).snd := by
                          show filtered_argSubst.unzip.snd[j]'_ = _
                          simp [List.unzip_eq_map]
                        ext
                        · -- fst component.
                          rw [← HfilGetFst, ← Hk1_app]
                        · -- snd component.
                          rw [← HfilGetSnd]
                          have : filtered_argTemps[n.val - lhs.length]'(by
                              have Hl : filtered_ks'.length =
                                  lhs.length + filtered_argTemps.length :=
                                List.length_append
                              omega) = filtered_argTemps[j]'Hj_lt_argT := by
                            congr 1
                            exact Hidx_eq.symm
                          rw [Hk2_app, this]
                      -- Pair (k1, k2) ∈ filtered_argSubst.
                      have HpairIn : (k1, k2) ∈ filtered_argSubst := by
                        rw [← HpairAtJ]
                        exact List.getElem_mem _
                      -- (k1, k2) ∈ inputs.keys.zip argTemps via Hfilter_in.
                      have HpairZip := (Hfilter_in (k1, k2) HpairIn).1
                      -- Get index m in inputs.keys.zip argTemps.
                      rcases List.mem_iff_get.mp HpairZip with ⟨m, Hm⟩
                      have Hzip_inkA_len :
                          (proc.header.inputs.keys.zip argTemps).length =
                            argVals.length := by
                        rw [List.length_zip, HinKeys_argTemps_len, Nat.min_self]
                        omega
                      have Hm_lt_in : m.val < proc.header.inputs.keys.length := by
                        have Hmlt := m.isLt
                        have Hl1 : (proc.header.inputs.keys.zip argTemps).length =
                                    argVals.length := Hzip_inkA_len
                        have Hl2 : argVals.length =
                                    proc.header.inputs.keys.length :=
                          HinKVlen.symm
                        omega
                      have Hm_lt_argT : m.val < argTemps.length := by
                        rw [← HinKeys_argTemps_len]; exact Hm_lt_in
                      have Hm_lt_argV : m.val < argVals.length := by
                        rw [← HinKVlen]; exact Hm_lt_in
                      have HmGet :
                          (proc.header.inputs.keys.zip argTemps)[m.val]'(by
                              have := m.isLt; exact this) =
                          (proc.header.inputs.keys[m.val]'Hm_lt_in,
                           argTemps[m.val]'Hm_lt_argT) :=
                        List.getElem_zip
                      have HmEq :
                          (k1, k2) = (proc.header.inputs.keys[m.val]'Hm_lt_in,
                                       argTemps[m.val]'Hm_lt_argT) := by
                        have := Hm.symm
                        rw [show (proc.header.inputs.keys.zip argTemps).get m =
                              (proc.header.inputs.keys.zip argTemps)[m.val]'_
                            from rfl] at this
                        rw [HmGet] at this
                        exact this
                      have Hk1_inGet :
                          k1 = proc.header.inputs.keys[m.val]'Hm_lt_in :=
                        ((Prod.mk.injEq _ _ _ _).mp HmEq).1
                      have Hk2_argTGet :
                          k2 = argTemps[m.val]'Hm_lt_argT :=
                        ((Prod.mk.injEq _ _ _ _).mp HmEq).2
                      -- σ_R1 k1 = some argVals[m.val] (via Hrd_R1_in_full).
                      have HrdR1_get :
                          σ_R1 (proc.header.inputs.keys[m.val]'Hm_lt_in) =
                            some (argVals[m.val]'Hm_lt_argV) := by
                        have HG := readValues_get
                          (σ:=σ_R1) (ks:=proc.header.inputs.keys)
                          (vs:=argVals) Hrd_R1_in_full
                          (i:=m.val) (hi:=Hm_lt_in) (hi':=Hm_lt_argV)
                        exact HG
                      have HrdHavoc_get :
                          σ_havoc (argTemps[m.val]'Hm_lt_argT) =
                            some (argVals[m.val]'Hm_lt_argV) := by
                        have HG := readValues_get
                          (σ:=σ_havoc) (ks:=argTemps) (vs:=argVals)
                          Hrd_havoc_argT
                          (i:=m.val) (hi:=Hm_lt_argT) (hi':=Hm_lt_argV)
                        exact HG
                      rw [Hk1_inGet, HrdR1_get, Hk2_argTGet, HrdHavoc_get]
                  -- ── D2e: Apply H_asserts_zip to derive HL4 ──
                  -- HL4 is L4 of EvalCallElim_glue.  σ_old = post-L3 store
                  -- (3-layer over argTemps/outTemps/oldTrips.fst.fst);
                  -- `asserts` has the `pres.zip labels` shape from HassertsShape.
                  let σ_old : CoreStore :=
                    updatedStates
                      (updatedStates
                        (updatedStates σ
                          argTemps argVals)
                        outTemps oVals)
                      oldTrips.unzip.fst.unzip.fst oldVals
                  -- L4 ks/ks' bindings with explicit type annotation
                  -- so `substNodup` can unify the identifier type.
                  let ks_L4 : List Expression.Ident :=
                    proc.header.inputs.keys ++ proc.header.outputs.keys
                  let ks'_L4 : List Expression.Ident :=
                    argTemps ++ lhs
                  -- ── L4 length facts ──
                  have Hks_len_L4 :
                      ks_L4.length = ks'_L4.length := by
                    show (proc.header.inputs.keys ++
                          proc.header.outputs.keys).length =
                         (argTemps ++ lhs).length
                    rw [List.length_append, List.length_append,
                        HinKeys_argTemps_len, HoutKeys_lhs_len]
                  -- ── L4 substNodup: ((inputs ++ outputs) ++ (argTemps ++ lhs)).Nodup ──
                  -- Disjointness facts (HinKeys/HoutKeys vs argTemps/lhs)
                  -- hoisted to C-aux phase; consumed below by name.
                  have HargT_lhs_nd :
                      (argTemps ++ lhs).Nodup := by
                    rw [List.nodup_append]
                    refine ⟨HargNd, HlhsNd, ?_⟩
                    intro a Ha b Hb Heq
                    subst Heq
                    exact HlhsDisjArg Hb Ha
                  have Hbignd_L4 :
                      (ks_L4 ++ ks'_L4).Nodup := by
                    show ((proc.header.inputs.keys ++
                            proc.header.outputs.keys) ++
                          (argTemps ++ lhs)).Nodup
                    rw [List.nodup_append]
                    refine ⟨Hinoutnd, HargT_lhs_nd, ?_⟩
                    intro a Ha b Hb Heq
                    subst Heq
                    cases List.mem_append.mp Ha with
                    | inl HaIn =>
                      cases List.mem_append.mp Hb with
                      | inl HbArg =>
                        exact HinKeys_disj_argTemps HaIn HbArg
                      | inr HbLhs =>
                        exact HinKeys_disj_lhs HaIn HbLhs
                    | inr HaOut =>
                      cases List.mem_append.mp Hb with
                      | inl HbArg =>
                        exact HoutKeys_disj_argTemps HaOut HbArg
                      | inr HbLhs =>
                        exact HoutKeys_disj_lhs HaOut HbLhs
                  have Hnd_L4 : Imperative.substNodup
                      (ks_L4.zip ks'_L4) := by
                    unfold Imperative.substNodup
                    rw [List.unzip_zip Hks_len_L4]
                    exact Hbignd_L4
                  -- ── L4 substDefined ──
                  have HσAO_def_in_L4 :
                      Imperative.isDefined σAO proc.header.inputs.keys := by
                    apply InitStatesDefMonotone ?_ Hinitout
                    exact InitStatesDefined Hinitin
                  have HσAO_def_out_L4 :
                      Imperative.isDefined σAO proc.header.outputs.keys :=
                    InitStatesDefined Hinitout
                  -- σ_old definedness on argTemps (layer 1 fall-through).
                  have Hσ_old_def_argT :
                      Imperative.isDefined σ_old
                        argTemps := by
                    intro v Hv
                    show ((updatedStates
                            (updatedStates
                              (updatedStates σ
                                argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals) v).isSome =
                          true
                    -- v not in oldTrips.fst.fst (= genOldIdents), since v ∈ argT
                    -- and argT ∩ olds = ∅ (Hgennd).
                    have Hv_notin_old :
                        v ∉ oldTrips.unzip.fst.unzip.fst := by
                      rw [HoldTripsFst]
                      intro Hin
                      have Hnd' :=
                        (List.nodup_append.mp Hgennd).2.2
                      exact Hnd' v
                        (List.mem_append.mpr (Or.inl Hv))
                        v Hin rfl
                    -- v not in outTrips.fst.fst, by Nodup of (argT ++ outT).
                    have Hv_notin_outT :
                        v ∉ outTemps := by
                      have Hnd_argT_outT :=
                        (List.nodup_append.mp Hgennd).1
                      have Hnd' :=
                        (List.nodup_append.mp Hnd_argT_outT).2.2
                      intro Hin
                      exact Hnd' v Hv v Hin rfl
                    rw [updatedStates_get_notin Hv_notin_old,
                        updatedStates_get_notin Hv_notin_outT]
                    -- updatedStates σ argTemps argVals v: v ∈ argTemps, so layer
                    -- 1 maps it to argVals[idx].
                    apply updatedStatesDefined
                    · exact HargFstLen
                    · exact Hv
                  -- σ_old definedness on lhs (reuses C-aux HlhsDef_old).
                  have Hσ_old_def_lhs :
                      Imperative.isDefined σ_old lhs := HlhsDef_old
                  have Hdef_L4 : Imperative.substDefined σAO σ_old
                      (ks_L4.zip ks'_L4) := by
                    intro k1 k2 Hkin
                    have Hmem := List.of_mem_zip Hkin
                    refine ⟨?_, ?_⟩
                    · cases List.mem_append.mp Hmem.1 with
                      | inl Hin1 => exact HσAO_def_in_L4 k1 Hin1
                      | inr Hin1 => exact HσAO_def_out_L4 k1 Hin1
                    · cases List.mem_append.mp Hmem.2 with
                      | inl Hin2 => exact Hσ_old_def_argT k2 Hin2
                      | inr Hin2 => exact Hσ_old_def_lhs k2 Hin2
                  -- ── L4 substStores: substStores σ_old σAO ((argTemps ++ lhs).zip (inputs ++ outputs)) ──
                  -- Strategy: build matching ReadValues on both σ_old and σAO,
                  -- then close via ReadValuesSubstStores.
                  -- σAO reads inputs ↦ argVals (via Hinitin lifted by Hinitout).
                  have HrdAO_in_L4 :
                      ReadValues σAO proc.header.inputs.keys argVals := by
                    have HrdA_in : ReadValues σA proc.header.inputs.keys argVals :=
                      InitStatesReadValues Hinitin
                    apply InitStatesReadValuesMonotone HrdA_in Hinitout
                  have HrdAO_out_L4 :
                      ReadValues σAO proc.header.outputs.keys oVals :=
                    InitStatesReadValues Hinitout
                  have HrdAO_inout_L4 :
                      ReadValues σAO
                        (proc.header.inputs.keys ++
                          proc.header.outputs.keys)
                        (argVals ++ oVals) :=
                    ReadValuesApp HrdAO_in_L4 HrdAO_out_L4
                  -- σ_old reads argTemps ↦ argVals.
                  -- argTemps were initialized at layer 1 (positional).
                  -- Lift through layers 2/3 via readValues_updatedStates
                  -- (using disjointness from outTemps/olds).
                  have HrdLayer1_argT :
                      ReadValues
                        (updatedStates σ
                          argTemps argVals)
                        argTemps argVals := by
                    apply readValues_updatedStatesSame
                    · exact HargFstLen
                    · -- argTemps.Nodup
                      exact (List.nodup_append.mp
                        (List.nodup_append.mp Hgennd).1).1
                  have HrdLayer2_argT :
                      ReadValues
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        argTemps argVals := by
                    apply readValues_updatedStates HoutFstLen
                            HargOutDisj HrdLayer1_argT
                  have HargT_disj_oldFst :
                      argTemps.Disjoint
                        oldTrips.unzip.fst.unzip.fst := by
                    rw [HoldTripsFst]
                    exact HargOldDisj
                  have HrdLayer3_argT :
                      ReadValues σ_old
                        argTemps argVals :=
                    readValues_updatedStates HoldFstLen HargT_disj_oldFst
                      HrdLayer2_argT
                  -- σ_old reads lhs ↦ oVals.  Path: σ_old(lhs) lifts σ(lhs)
                  -- via readValues_updatedStates × 3 (lhs disjoint from
                  -- argT/outT/old).  σ(lhs) = oVals via Hevalouts.
                  have HrdLayer1_lhs :
                      ReadValues
                        (updatedStates σ
                          argTemps argVals)
                        lhs oVals :=
                    readValues_updatedStates HargFstLen HlhsDisjArg Hevalouts
                  have HrdLayer2_lhs :
                      ReadValues
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        lhs oVals :=
                    readValues_updatedStates HoutFstLen HlhsDisjOut HrdLayer1_lhs
                  have Hlhs_disj_oldFst :
                      lhs.Disjoint oldTrips.unzip.fst.unzip.fst := by
                    rw [HoldTripsFst]
                    exact HlhsDisjOld
                  have HrdLayer3_lhs :
                      ReadValues σ_old lhs oVals :=
                    readValues_updatedStates HoldFstLen Hlhs_disj_oldFst
                      HrdLayer2_lhs
                  have HrdOld_inout_L4 :
                      ReadValues σ_old
                        (argTemps ++ lhs)
                        (argVals ++ oVals) :=
                    ReadValuesApp HrdLayer3_argT HrdLayer3_lhs
                  have Hsubst_L4 : Imperative.substStores σ_old σAO
                      (ks'_L4.zip ks_L4) :=
                    ReadValuesSubstStores HrdOld_inout_L4 HrdAO_inout_L4
                  -- ── Apply H_asserts_zip ──
                  -- Destructure HassertsShape to bind the labels list.
                  obtain ⟨assertLabels, HassertLabelsLen, HassertShape⟩ :=
                    HassertsShape
                  -- Bridge: the assertSubst from HassertsShape equals
                  -- ks_L4.zip (createFvars ks'_L4),
                  -- via List.zip_append and createFvarsApp.
                  have HassertSubst_eq :
                      ((proc.header.inputs.keys.zip
                          (Core.Transform.createFvars
                            argTemps)) ++
                        (proc.header.outputs.keys.zip
                          (Core.Transform.createFvars
                            (CallArg.getLhs args)))) =
                      ks_L4.zip
                        (Core.Transform.createFvars ks'_L4) := by
                    show _ =
                      (proc.header.inputs.keys ++
                        proc.header.outputs.keys).zip
                      (Core.Transform.createFvars
                        (argTemps ++ lhs))
                    rw [hCallArgsLhs, createFvarsApp]
                    rw [List.zip_append]
                    rw [createFvarsLength]
                    exact HinKeys_argTemps_len
                  -- Apply H_asserts_zip; bne_iff_ne bridges the != / ≠ filter forms.
                  have HL4_pre :
                      EvalStatementsContract π φ ⟨σ_old, δ, false⟩
                        (((proc.spec.preconditions.filter
                              (fun (_, check) => check.attr != .Free)).zip
                            assertLabels).map (fun (entry, lbl) =>
                          Statement.assert lbl
                            (Lambda.LExpr.substFvars entry.snd.expr
                              (ks_L4.zip
                                (Core.Transform.createFvars ks'_L4)))
                            (entry.snd.md.setCallSiteFileRange md)))
                        ⟨σ_old, δ, false⟩ := by
                    apply H_asserts_zip
                      (σA := σAO) (σ' := σ_old)
                      (ks := ks_L4)
                      (ks' := ks'_L4)
                      (pres := proc.spec.preconditions.filter
                                (fun (_, check) => check.attr != .Free))
                      (labels := assertLabels)
                      Hwfb Hwfvars Hwfval Hwfc
                      Hks_len_L4 Hnd_L4 Hdef_L4 Hsubst_L4
                    -- HpresPayload over presFiltered.  The two filter forms
                    -- (`c.attr != .Free` boolean and `c.attr ≠ .Free` Prop)
                    -- agree definitionally via decide reduction.
                    intros entry Hentry
                    -- Bridge: filter-form `c.attr != .Free` ↔ `c.attr ≠ .Free`.
                    have Hentry' : entry ∈ presFiltered := by
                      show entry ∈ proc.spec.preconditions.filter
                                    (fun (_, c) => c.attr ≠ .Free)
                      have Hin :
                          entry ∈
                            (List.filter
                              (fun x => match x with
                                | (_, check) => check.attr != Procedure.CheckAttr.Free)
                              proc.spec.preconditions) := Hentry
                      rw [List.mem_filter] at Hin ⊢
                      refine ⟨Hin.1, ?_⟩
                      simp only [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
                                 decide_eq_false_iff_not, ne_eq]
                      have := Hin.2
                      simp only [bne_iff_ne, ne_eq] at this
                      exact this
                    exact HpresPayload entry Hentry'
                  -- Bridge to the actual `asserts` list via HassertsShape.
                  have HL4 :
                      EvalStatementsContract π φ ⟨σ_old, δ, false⟩
                        asserts ⟨σ_old, δ, false⟩ := by
                    -- Rewrite asserts using HassertShape; the resulting list
                    -- is over `proc'`-keys, which equal `proc`-keys via HprocEq.
                    rw [HassertShape]
                    -- Push proc' = proc through to reach the L4-derived form.
                    rw [HprocEq]
                    -- Rewrite the inner substitution map via HassertSubst_eq.
                    rw [HassertSubst_eq]
                    exact HL4_pre
                  -- D2d-bridge: σO ↔ σAO old-binding bridge.
                  -- (a) Trivial empty-init witness.
                  have HInitVars_empty : InitVars σO [] σO := InitVars.init_none
                  -- (b) Per-output bridge via Hwf2's universal clause.
                  have Hwf2_univ :
                      ∀ v ∈ proc.header.outputs.keys,
                        δ σO (Lambda.LExpr.fvar () (CoreIdent.mkOld v.name)
                                                         none) =
                          σAO v := by
                    intro v Hv
                    -- Unfold Hwf2 to expose the `∧` structure.
                    simp only [WellFormedCoreEvalTwoState] at Hwf2
                    -- Hwf2.2 : universal clause; instantiate at
                    -- (vs := outputs.keys, vs' := [], σ₀ := σAO, σ₁ := σO,
                    --  σ_arg := σO) using `Hhav1 ∧ HInitVars_empty`.
                    have HH := Hwf2.2 proc.header.outputs.keys [] σAO σO σO
                                ⟨Hhav1, HInitVars_empty⟩ v
                    -- HH : (v ∈ outputs.keys → δ σO (mkOld v.name) = σAO v) ∧
                    --      (¬ v ∈ outputs.keys → δ σO (mkOld v.name) = σO v)
                    exact HH.1 Hv
                  -- (c) σAO[v] = σ[v] for v ∉ outputs ∪ inputs.
                  have HσAO_notin_eq_σ :
                      ∀ v, v ∉ proc.header.outputs.keys →
                           v ∉ proc.header.inputs.keys →
                           σAO v = σ v := by
                    intro v Hv_notout Hv_notin
                    rw [initStates_get_notin Hinitout Hv_notout,
                        initStates_get_notin Hinitin Hv_notin]
                  -- (d) σAO reads outputs ↦ oVals (positional).
                  have HσAO_reads_outs :
                      ReadValues σAO proc.header.outputs.keys oVals :=
                    InitStatesReadValues Hinitout
                  -- (e) Positional alignment via HoutAlign (Hwfcallsite.specialize).
                  -- (f) Per-index δ-eval bridge: δ σO (mkOld oldVars[i].name) = some oldVals[i].
                  have HoldVals_len : oldVals.length = oldVars.length :=
                    HoldValsLen
                  -- For v ∈ oldVars, v is in CallArg.getLhs args (filter).
                  have HoldVars_sub_callLhs : ∀ v ∈ oldVars, v ∈ CallArg.getLhs args := by
                    intro v Hv
                    exact (List.mem_filter.mp Hv).1
                  -- For v ∈ oldVars, v is in proc'.header.outputs.keys (filter).
                  -- Bridge proc' = proc via HprocEq.
                  have HoldVars_sub_outs : ∀ v ∈ oldVars,
                      v ∈ ListMap.keys proc.header.outputs := by
                    intro v Hv
                    have Hv_filt := List.mem_filter.mp Hv
                    have Hbool := Hv_filt.2
                    -- Hbool : (proc'.inputs.contains v && proc'.outputs.contains v &&
                    --         ...) = true
                    -- Project the outputs.contains conjunct.
                    simp only [Bool.and_eq_true] at Hbool
                    have HinOuts' : (ListMap.keys proc'.header.outputs).contains v := by
                      exact Hbool.1.2
                    rw [HprocEq] at HinOuts'
                    exact List.contains_iff_mem.mp HinOuts'
                  -- For v ∈ oldVars, v ∈ lhs (oldVars ⊆ getLhs args = lhs).
                  have HoldVars_sub_lhs_L6 : ∀ v ∈ oldVars, v ∈ lhs := by
                    intro v Hv
                    exact hCallArgsLhs ▸ HoldVars_sub_callLhs v Hv
                  -- The per-index bridge.  We name it `HoldEval_bridge`
                  -- and frame it positionally for downstream consumers.
                  have HoldEval_bridge :
                      ∀ (i : Nat) (Hi : i < oldVars.length),
                        δ σO
                            (Lambda.LExpr.fvar ()
                              (CoreIdent.mkOld (oldVars[i]'Hi).name) none) =
                          some (oldVals[i]'(HoldVals_len.symm ▸ Hi)) := by
                    intro i Hi
                    -- Name the i-th oldVars element via let-binding.
                    let v : Expression.Ident := oldVars[i]'Hi
                    have Hv_def : v = oldVars[i]'Hi := rfl
                    -- v ∈ oldVars (List.getElem_mem).
                    have Hv_mem : v ∈ oldVars := List.getElem_mem _
                    -- v ∈ outputs.keys.
                    have Hv_out : v ∈ ListMap.keys proc.header.outputs :=
                      HoldVars_sub_outs v Hv_mem
                    -- v ∈ lhs.
                    have Hv_lhs : v ∈ lhs := HoldVars_sub_lhs_L6 v Hv_mem
                    -- v ∈ CallArg.getLhs args.
                    have Hv_callLhs : v ∈ CallArg.getLhs args :=
                      HoldVars_sub_callLhs v Hv_mem
                    -- Step 1: δ σO (mkOld v.name) = σAO v.
                    have HStep1 :
                        δ σO (Lambda.LExpr.fvar () (CoreIdent.mkOld v.name)
                                                         none) =
                          σAO v :=
                      Hwf2_univ v Hv_out
                    -- Step 2: σAO v = oVals[outputs.keys.idxOf v].
                    -- HσAO_reads_outs : ReadValues σAO outputs.keys oVals.
                    -- Use idxOf to index into outputs.keys.
                    let j_out := (ListMap.keys proc.header.outputs).idxOf v
                    have Hj_out_def : j_out =
                        (ListMap.keys proc.header.outputs).idxOf v := rfl
                    have Hj_out_lt :
                        j_out < (ListMap.keys proc.header.outputs).length :=
                      List.idxOf_lt_length_of_mem Hv_out
                    have HouterKeys_oVals_len :
                        (ListMap.keys proc.header.outputs).length =
                          oVals.length :=
                      InitStatesLength Hinitout
                    have Hj_out_lt_oVals : j_out < oVals.length := by
                      rw [← HouterKeys_oVals_len]
                      exact Hj_out_lt
                    have Houts_get_v :
                        (ListMap.keys proc.header.outputs)[j_out]'Hj_out_lt = v := by
                      show (ListMap.keys proc.header.outputs)[
                              (ListMap.keys proc.header.outputs).idxOf v]'_ = v
                      unfold List.idxOf
                      have HH := @List.findIdx_getElem _ (· == v)
                                  (ListMap.keys proc.header.outputs)
                                  (List.idxOf_lt_length_of_mem Hv_out)
                      simpa using HH
                    have HStep2 :
                        σAO v = some (oVals[j_out]'Hj_out_lt_oVals) := by
                      have Hget := readValues_get
                        (σ:=σAO)
                        (ks:=ListMap.keys proc.header.outputs)
                        (vs:=oVals)
                        HσAO_reads_outs
                        (i:=j_out) (hi:=Hj_out_lt) (hi':=Hj_out_lt_oVals)
                      -- Hget : σAO outputs.keys[j_out] = some oVals[j_out].
                      -- Houts_get_v : outputs.keys[j_out] = v.
                      rw [Houts_get_v] at Hget
                      exact Hget
                    -- Step 3: lhs.idxOf v = outputs.keys.idxOf v (alignment).
                    have HAlign :
                        (CallArg.getLhs args).idxOf v =
                          (ListMap.keys proc.header.outputs).idxOf v :=
                      HoutAlign v Hv_out Hv_callLhs
                    -- Translate to lhs (since hCallArgsLhs : getLhs args = lhs).
                    have HAlign_lhs : lhs.idxOf v = j_out := by
                      show lhs.idxOf v = (ListMap.keys proc.header.outputs).idxOf v
                      rw [← HAlign, hCallArgsLhs]
                    -- Step 4: σ v = oVals[lhs.idxOf v]'_.
                    -- Use Hevalouts : ReadValues σ lhs oVals positional.
                    let j_lhs := lhs.idxOf v
                    have Hj_lhs_def : j_lhs = lhs.idxOf v := rfl
                    have Hj_lhs_eq_j_out : j_lhs = j_out := HAlign_lhs
                    have Hj_lhs_lt : j_lhs < lhs.length :=
                      List.idxOf_lt_length_of_mem Hv_lhs
                    have Hlhs_oVals_len : lhs.length = oVals.length :=
                      ReadValuesLength Hevalouts
                    have Hj_lhs_lt_oVals : j_lhs < oVals.length := by
                      rw [Hlhs_oVals_len] at Hj_lhs_lt
                      exact Hj_lhs_lt
                    have Hlhs_get_v : lhs[j_lhs]'Hj_lhs_lt = v := by
                      show lhs[lhs.idxOf v]'_ = v
                      unfold List.idxOf
                      have HH := @List.findIdx_getElem _ (· == v) lhs
                                  (List.idxOf_lt_length_of_mem Hv_lhs)
                      simpa using HH
                    have HStep4 :
                        σ v = some (oVals[j_lhs]'Hj_lhs_lt_oVals) := by
                      have Hget := readValues_get
                        (σ:=σ) (ks:=lhs) (vs:=oVals) Hevalouts
                        (i:=j_lhs) (hi:=Hj_lhs_lt) (hi':=Hj_lhs_lt_oVals)
                      rw [Hlhs_get_v] at Hget
                      exact Hget
                    -- Step 5: σ v = some oldVals[i]'_ (HoldVals positional).
                    have Hi_oldVals : i < oldVals.length := HoldVals_len.symm ▸ Hi
                    have HStep5 : σ v = some (oldVals[i]'Hi_oldVals) := by
                      have Hget := readValues_get
                        (σ:=σ) (ks:=oldVars) (vs:=oldVals) HoldVals
                        (i:=i) (hi:=Hi) (hi':=Hi_oldVals)
                      -- Hget : σ oldVars[i] = some oldVals[i].
                      -- v = oldVars[i] by Hv_def.
                      exact Hget
                    -- Combine: δ σO (mkOld v.name) = some oldVals[i].
                    show δ σO (Lambda.LExpr.fvar () (CoreIdent.mkOld v.name) none)
                          = some (oldVals[i]'Hi_oldVals)
                    rw [HStep1, HStep2]
                    -- Goal: some oVals[j_out] = some oldVals[i].
                    have Hj_eq : oVals[j_out]'Hj_out_lt_oVals =
                                 oVals[j_lhs]'Hj_lhs_lt_oVals := by
                      congr 1
                      exact Hj_lhs_eq_j_out.symm
                    rw [Hj_eq]
                    -- Goal: some oVals[j_lhs] = some oldVals[i].
                    rw [← HStep4, HStep5]
                  -- D2d: Structural pieces of HpostPayload (Hinv,
                  -- Hpred_disj, Heval_bridge per entry; survive/codom
                  -- split via getVars_substFvars_mem).
                  let oldVars_L6 : List Expression.Ident :=
                    List.filter
                      (fun g =>
                        (ListMap.keys proc'.header.inputs).contains g &&
                            (ListMap.keys proc'.header.outputs).contains g &&
                          (List.map Procedure.Check.expr
                              proc'.spec.postconditions.values).any fun e =>
                            List.any e.freeVars
                              fun x => x.fst == CoreIdent.mkOld g.name)
                      (CallArg.getLhs args)
                  let oldGVars_L6 : List Expression.Ident :=
                    oldVars_L6.map (fun g => CoreIdent.mkOld g.name)
                  let oldTripsCanonical_L6 :
                      List ((Expression.Ident × Expression.Ty) ×
                            Expression.Ident) :=
                    (((genOldIdents.zip oldTys).zip oldVars_L6).zip
                      oldGVars_L6).map
                      fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)
                  let inputOnlyOldSubst_L6 :
                      Map Expression.Ident Expression.Expr :=
                    (proc'.header.inputs.keys.zip
                        (CallArg.getInputExprs args)).filterMap
                      fun (paramId, argExpr) =>
                        let oldVar := CoreIdent.mkOld paramId.name
                        if !(ListMap.keys proc'.header.outputs).contains paramId &&
                           (proc'.spec.postconditions.values.map
                             Procedure.Check.expr).any
                             (fun e => Lambda.LExpr.freeVars e |>.any
                               (fun (id, _) => id == oldVar))
                        then some (oldVar, argExpr)
                        else none
                  let oldSubst_L6 : Map Expression.Ident Expression.Expr :=
                    Core.Transform.createOldVarsSubst oldTripsCanonical_L6 ++
                      inputOnlyOldSubst_L6
                  let posts_filtered_L6 :
                      ListMap CoreLabel Procedure.Check :=
                    Procedure.Spec.updateCheckExprs
                      (proc'.spec.postconditions.values.map
                        (fun c =>
                          Lambda.LExpr.substFvars c.expr oldSubst_L6))
                      proc'.spec.postconditions
                  -- Per-entry posts_filtered_L6 ↔ original correspondence
                  -- via updateCheckExprs_substFvars_mem.
                  have HpostFiltered_corresp :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈
                          (proc'.spec.postconditions.keys.zip
                            (updateCheckExprs_walk
                              (proc'.spec.postconditions.values.map
                                (fun c =>
                                  Lambda.LExpr.substFvars c.expr oldSubst_L6))
                              proc'.spec.postconditions.values)) →
                        ∃ c ∈ proc'.spec.postconditions.values,
                          entry.snd.expr =
                            Lambda.LExpr.substFvars c.expr oldSubst_L6 := by
                    intro entry Hentry
                    exact updateCheckExprs_substFvars_mem Hentry
                  -- Per-entry decomposition helper.
                  have forall_post_filtered_decompose :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        ∃ c ∈ proc'.spec.postconditions.values,
                          entry.snd.expr =
                            Lambda.LExpr.substFvars c.expr oldSubst_L6 := by
                    intro entry Hentry
                    have Hentry_zip :
                        entry ∈
                          (proc'.spec.postconditions.keys.zip
                            (updateCheckExprs_walk
                              (proc'.spec.postconditions.values.map
                                (fun c =>
                                  Lambda.LExpr.substFvars c.expr oldSubst_L6))
                              proc'.spec.postconditions.values)) := by
                      rw [updateCheckExprs_walk_eq_go]
                      show entry ∈
                          (proc'.spec.postconditions.keys.zip
                            (Procedure.Spec.updateCheckExprs.go _ _))
                      exact Hentry
                    exact HpostFiltered_corresp entry Hentry_zip
                  -- D2d-eval: per-fvar bridges for substFvars eval
                  -- (Hsurv/Hsub for subst_fvars_eval_bridge, split on
                  -- oldSubst_L6 = createOldVarsSubst ++ inputOnlyOldSubst).
                  have HoldSubBridge :
                      ∀ k w,
                        Map.find?
                          (Core.Transform.createOldVarsSubst
                            oldTripsCanonical_L6) k = some w →
                        δ σ_R1 w =
                          δ σO (Lambda.LExpr.fvar () k none) := by
                    intro k w Hf
                    -- Positional decomposition via createOldVarsSubst_pos_decomp.
                    obtain ⟨ni_val, Hni_lt, Hk_eqMkOld, Hw_eq⟩ :=
                      createOldVarsSubst_pos_decomp HgenOldLen HoldTysLen Hf
                    have Hni_lt_genOld : ni_val < genOldIdents.length := by
                      have := HgenOldLen
                      omega
                    -- LHS: δ σ_R1 w = σ_R1 genOldIdents[i] = some oldVals[i].
                    -- σ_R1 = updatedStates σO genOldIdents oldVals.
                    -- Use readValues_updatedStatesSame + readValues_get.
                    have HoldValsLenE :
                        genOldIdents.length = oldVals.length := by
                      have := HoldValsLen
                      have := HgenOldLen
                      omega
                    have Hni_lt_oldVals : ni_val < oldVals.length := by
                      have := HoldValsLen
                      omega
                    have HrdR1_olds :
                        ReadValues σ_R1 genOldIdents oldVals := by
                      show ReadValues
                        (updatedStates σO genOldIdents oldVals)
                        genOldIdents oldVals
                      exact readValues_updatedStatesSame
                              HoldValsLenE HoldNd
                    have HrdR1_get :
                        σ_R1 (genOldIdents[ni_val]'Hni_lt_genOld) =
                          some (oldVals[ni_val]'Hni_lt_oldVals) :=
                      readValues_get HrdR1_olds
                        (i:=ni_val) (hi:=Hni_lt_genOld) (hi':=Hni_lt_oldVals)
                    -- δ σ_R1 (createFvar gen) = σ_R1 gen.
                    have Hwfvr := Hwfvars
                    simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
                    have HwfL :
                        δ σ_R1 (Core.Transform.createFvar
                                 (genOldIdents[ni_val]'Hni_lt_genOld)) =
                          σ_R1 (genOldIdents[ni_val]'Hni_lt_genOld) := by
                      show δ σ_R1 (Lambda.LExpr.fvar () _ none) = _
                      rw [Hwfvr (Lambda.LExpr.fvar ()
                            (genOldIdents[ni_val]'Hni_lt_genOld) none)
                          (genOldIdents[ni_val]'Hni_lt_genOld)]
                      simp [Imperative.HasFvar.getFvar]
                    -- RHS: δ σO (fvar k) = δ σO (fvar (mkOld oldVars[i].name))
                    --                    = some oldVals[i] (HoldEval_bridge).
                    have HoldEv :
                        δ σO (Lambda.LExpr.fvar ()
                                (CoreIdent.mkOld
                                  (oldVars[ni_val]'Hni_lt).name)
                                none) =
                          some (oldVals[ni_val]'Hni_lt_oldVals) :=
                      HoldEval_bridge ni_val Hni_lt
                    -- Conclude.
                    rw [Hw_eq, HwfL, HrdR1_get, Hk_eqMkOld, HoldEv]
                  -- (2b) HinputSubBridge: inputOnlyOldSubst codomain.
                  have HinputSubBridge :
                      ∀ k w,
                        Map.find? inputOnlyOldSubst_L6 k = some w →
                        δ σ_R1 w =
                          δ σO (Lambda.LExpr.fvar () k none) := by
                    intro k w Hf
                    -- Positional decomposition via the shared helper:
                    -- extracts ni < inputs.length, ni < inputArgs.length,
                    -- k = mkOld inputs[ni].name, w = inputArgs[ni], and
                    -- inputs[ni] ∉ outputs.keys.
                    obtain ⟨ni_val, Hni_lt_inKeys, Hni_lt_inArgs,
                            Hk_eq_proc', Hw_eq_proc', Hin_notin_outs_proc'⟩ :=
                      inputOnlyOldSubst_pos_decomp Hf
                    -- Bridge proc' = proc.
                    have Hni_lt_inKeys' :
                        ni_val < proc.header.inputs.keys.length := by
                      have HEqLen : proc'.header.inputs.keys.length =
                          proc.header.inputs.keys.length := by rw [HprocEq]
                      omega
                    have HpinKeys :
                        proc'.header.inputs.keys[ni_val]'Hni_lt_inKeys =
                          proc.header.inputs.keys[ni_val]'Hni_lt_inKeys' := by
                      subst HprocEq; rfl
                    -- Let `inputId := inputs.keys[ni_val]`.
                    let inputId : Expression.Ident :=
                      proc.header.inputs.keys[ni_val]'Hni_lt_inKeys'
                    have HinputId_def : inputId =
                        proc.header.inputs.keys[ni_val]'Hni_lt_inKeys' := rfl
                    have HinputId_in : inputId ∈ proc.header.inputs.keys :=
                      List.getElem_mem _
                    have HinputId_notin_outs :
                        inputId ∉ proc.header.outputs.keys :=
                      fun h => Hiodisj HinputId_in h
                    -- argExpr := the snd projection.
                    let argExpr : Expression.Expr :=
                      (CallArg.getInputExprs args)[ni_val]'Hni_lt_inArgs
                    have HargExpr_def : argExpr =
                        (CallArg.getInputExprs args)[ni_val]'Hni_lt_inArgs := rfl
                    have HargExpr_in : argExpr ∈ CallArg.getInputExprs args :=
                      List.getElem_mem _
                    -- k = mkOld inputId.name.
                    have Hk_mkOld : k = CoreIdent.mkOld inputId.name := by
                      rw [Hk_eq_proc', HpinKeys]
                    -- w = argExpr.
                    have Hw_argExpr : w = argExpr := Hw_eq_proc'
                    -- Fin-packaging so existing `ni : Fin …` users still apply.
                    let ni : Fin (CallArg.getInputExprs args).length :=
                      ⟨ni_val, Hni_lt_inArgs⟩
                    have Hni_lt_inArgsCall : ni.val < inArgs.length := by
                      have : (CallArg.getInputExprs args).length =
                          inArgs.length := by rw [hCallArgsIn]
                      rw [← this]
                      exact Hni_lt_inArgs
                    have HargExpr_eq_inArgs :
                        argExpr = inArgs[ni.val]'Hni_lt_inArgsCall := by
                      show (CallArg.getInputExprs args)[ni.val]'Hni_lt_inArgs =
                            inArgs[ni.val]'Hni_lt_inArgsCall
                      congr 1 <;> exact hCallArgsIn
                    -- argVals length facts.
                    have HinKeys_argVals_len :
                        proc.header.inputs.keys.length = argVals.length :=
                      InitStatesLength Hinitin
                    have Hni_lt_argVals : ni.val < argVals.length := by
                      rw [← HinKeys_argVals_len]
                      exact Hni_lt_inKeys'
                    -- ── RHS Step A: δ σO (mkOld inputId.name) = σO inputId
                    --   via Hwf2 not-in-outputs branch. ──
                    have HRHS_StepA :
                        δ σO (Lambda.LExpr.fvar ()
                                (CoreIdent.mkOld inputId.name) none) =
                          σO inputId := by
                      simp only [WellFormedCoreEvalTwoState] at Hwf2
                      have HH := Hwf2.2 proc.header.outputs.keys [] σAO σO σO
                                  ⟨Hhav1, HInitVars_empty⟩ inputId
                      exact HH.2 HinputId_notin_outs
                    -- ── RHS Step B: σO inputId = σAO inputId
                    --   via havoc preserves on non-outputs. ──
                    have HRHS_StepB : σO inputId = σAO inputId := by
                      have Hhav_up := HavocVarsUpdateStates Hhav1
                      rcases Hhav_up with ⟨ovh, Hup_havoc⟩
                      have HσO_eq : σO = updatedStates σAO
                                      proc.header.outputs.keys ovh :=
                        UpdateStatesUpdated Hup_havoc
                      rw [HσO_eq, updatedStates_get_notin HinputId_notin_outs]
                    -- ── RHS Step C: σAO inputId = σA inputId
                    --   via Hinitout fall-through. ──
                    have HRHS_StepC : σAO inputId = σA inputId :=
                      initStates_get_notin Hinitout HinputId_notin_outs
                    -- ── RHS Step D: σA inputId = some argVals[ni.val]
                    --   via positional Hinitin. ──
                    have HRHS_StepD : σA inputId =
                        some (argVals[ni.val]'Hni_lt_argVals) := by
                      have HrdA :
                          ReadValues σA proc.header.inputs.keys argVals :=
                        InitStatesReadValues Hinitin
                      have Hget := readValues_get
                        (σ:=σA) (ks:=proc.header.inputs.keys)
                        (vs:=argVals) HrdA
                        (i:=ni.val) (hi:=Hni_lt_inKeys')
                        (hi':=Hni_lt_argVals)
                      -- Hget : σA inputs.keys[ni.val] = some argVals[ni.val].
                      exact Hget
                    -- ── RHS Step E: argVals[ni.val] = δ σ argExpr
                    --   via evalExpressions_get + hCallArgsIn. ──
                    have HRHS_StepE :
                        δ σ argExpr =
                          some (argVals[ni.val]'Hni_lt_argVals) := by
                      have Hev := evalExpressions_get Hevalargs
                                    Hni_lt_inArgsCall Hni_lt_argVals
                      -- Hev : δ σ (List.get inArgs ⟨ni.val, _⟩) =
                      --   some (List.get argVals ⟨ni.val, _⟩).
                      -- Bridge δ σ argExpr = δ σ inArgs[ni.val].
                      have HargList :
                          List.get inArgs ⟨ni.val, Hni_lt_inArgsCall⟩ =
                            inArgs[ni.val]'Hni_lt_inArgsCall := rfl
                      have HvalList :
                          List.get argVals ⟨ni.val, Hni_lt_argVals⟩ =
                            argVals[ni.val]'Hni_lt_argVals := rfl
                      rw [HargList, HvalList] at Hev
                      rw [HargExpr_eq_inArgs]
                      exact Hev
                    -- LHS Step F: δ σ_R1 argExpr = δ σ argExpr.
                    have HargIsDef : Imperative.isDefined σ
                          (List.flatMap
                            (Imperative.HasVarsPure.getVars (P:=Expression))
                            inArgs) :=
                      evalExpressions_isDefined_flatMap Hevalargs
                    -- For v ∈ getVars argExpr, σ v is some (definedness lift).
                    have HargExpr_in_argList :
                        argExpr ∈ inArgs := by
                      rw [HargExpr_eq_inArgs]
                      exact List.getElem_mem _
                    have HargExpr_in_callList :
                        argExpr ∈ CallArg.getInputExprs args := HargExpr_in
                    -- σ_R1 ↔ σ pointwise on argExpr's free vars.
                    have Hσ_R1_eq_σ_argVars :
                        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression)
                                argExpr,
                          σ_R1 v = σ v := by
                      intro v Hv
                      -- v ∈ flatMap getVars inArgs.
                      have Hv_flat : v ∈
                          List.flatMap
                            (Imperative.HasVarsPure.getVars (P:=Expression))
                            inArgs := by
                        rw [List.mem_flatMap]
                        refine ⟨argExpr, ?_, Hv⟩
                        exact HargExpr_in_argList
                      -- σ v is some.
                      have Hσv_some : (σ v).isSome := HargIsDef v Hv_flat
                      -- v not isOldTempIdent (via Hgenrel.oldFresh contrapositive).
                      have HvNotOldTemp : ¬ isOldTempIdent v := by
                        intro Hold
                        have HNone := Hgenrel.oldFresh v Hold
                        have HSome : ¬ (σ v).isNone := by
                          simp only [Option.isNone_iff_eq_none,
                                     ← Option.isSome_iff_ne_none]
                          exact Hσv_some
                        exact HSome HNone
                      -- v ∉ genOldIdents.
                      have HvNotGen : v ∉ genOldIdents := by
                        intro Hg
                        exact HvNotOldTemp
                          ((List.Forall_mem_iff.mp HoldIdentsTemp) v Hg)
                      -- v ∉ outputs.keys (clause 5).
                      have HvNotOuts : v ∉ proc.header.outputs.keys :=
                        HargVarsNotInOutKeys argExpr HargExpr_in_callList v Hv
                      -- v ∉ inputs.keys (clause 6).
                      have HvNotIns : v ∉ proc.header.inputs.keys :=
                        HargVarsNotInInKeys argExpr HargExpr_in_callList v Hv
                      -- σ_R1 v = σ v via the layered store-agreement
                      -- helper.
                      show updatedStates σO genOldIdents oldVals v = σ v
                      exact σR1_eq_σ_for_notTouched
                        Hinitin Hinitout Hhav1 HvNotIns HvNotOuts HvNotGen
                    -- Lift to δ-eval via Hwfvars (fvarcongr-like).
                    have Hwfvr := Hwfvars
                    simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
                    have Hδ_R1_eq_δ_σ :
                        δ σ_R1 argExpr = δ σ argExpr := by
                      -- Apply subst_fvars_eval_bridge with empty subst map.
                      have Hsurv :
                          ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression)
                                  argExpr,
                            Map.find? (∅ : Map Expression.Ident
                                          Expression.Expr) v = none →
                            δ σ_R1 (Lambda.LExpr.fvar () v none) =
                              δ σ (Lambda.LExpr.fvar () v none) := by
                        intro v Hv _
                        have HwfL :
                            δ σ_R1 (Lambda.LExpr.fvar () v none) = σ_R1 v := by
                          rw [Hwfvr (Lambda.LExpr.fvar () v none) v]
                          simp [Imperative.HasFvar.getFvar]
                        have HwfR :
                            δ σ (Lambda.LExpr.fvar () v none) = σ v := by
                          rw [Hwfvr (Lambda.LExpr.fvar () v none) v]
                          simp [Imperative.HasFvar.getFvar]
                        rw [HwfL, HwfR]
                        exact Hσ_R1_eq_σ_argVars v Hv
                      have Hsub :
                          ∀ k' w', k' ∈ Imperative.HasVarsPure.getVars
                                          (P:=Expression) argExpr →
                            Map.find? (∅ : Map Expression.Ident
                                          Expression.Expr) k' = some w' →
                            δ σ_R1 w' =
                              δ σ (Lambda.LExpr.fvar () k' none) := by
                        intro k' w' _ Hf
                        simp [Map.find?] at Hf
                      have Hbridge :
                          δ σ_R1 (Lambda.LExpr.substFvars argExpr
                                    (∅ : Map Expression.Ident
                                          Expression.Expr)) =
                            δ σ argExpr :=
                        subst_fvars_eval_bridge Hwfc Hwfvars Hwfval
                          (sm:=∅)
                          Hsurv Hsub
                      -- substFvars argExpr ∅ = argExpr.
                      have HsubstEmpty :
                          Lambda.LExpr.substFvars argExpr
                              (∅ : Map Expression.Ident Expression.Expr) =
                            argExpr := by
                        induction argExpr with
                        | const _ _ => simp
                        | op _ _ _ => simp
                        | bvar _ _ => simp
                        | fvar m name ty =>
                          rw [Lambda.LExpr.substFvars_fvar_none m name ty]
                          rfl
                        | abs _ _ _ _ ih =>
                          simp [Lambda.LExpr.substFvars_abs, ih]
                        | quant _ _ _ _ _ _ trih bih =>
                          simp [Lambda.LExpr.substFvars_quant, trih, bih]
                        | app _ _ _ ih1 ih2 =>
                          simp [Lambda.LExpr.substFvars_app, ih1, ih2]
                        | eq _ _ _ ih1 ih2 =>
                          simp [Lambda.LExpr.substFvars_eq, ih1, ih2]
                        | ite _ _ _ _ ih1 ih2 ih3 =>
                          simp [Lambda.LExpr.substFvars_ite,
                                ih1, ih2, ih3]
                      rw [HsubstEmpty] at Hbridge
                      exact Hbridge
                    rw [Hw_argExpr, Hδ_R1_eq_δ_σ, HRHS_StepE,
                        ← HRHS_StepD, ← HRHS_StepC, ← HRHS_StepB,
                        ← HRHS_StepA, ← Hk_mkOld]
                  -- HpostEval_bridge: per-entry σ_R1 eval bridge via
                  -- subst_fvars_eval_bridge + HpostFiltered_corresp.
                  have HpostEval_bridge :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        δ σ_R1 entry.snd.expr =
                          some Imperative.HasBool.tt := by
                    intro entry Hentry
                    obtain ⟨c, Hc_in, Hentry_eq⟩ :=
                      forall_post_filtered_decompose entry Hentry
                    -- entry.snd.expr = substFvars c.expr oldSubst_L6.
                    rw [Hentry_eq]
                    -- Build the combined Hsub for subst_fvars_eval_bridge.
                    have Hsub :
                        ∀ k w, k ∈ Imperative.HasVarsPure.getVars
                                      (P:=Expression) c.expr →
                          Map.find? oldSubst_L6 k = some w →
                          δ σ_R1 w =
                            δ σO (Lambda.LExpr.fvar () k none) := by
                      intro k w _Hk Hf
                      -- oldSubst_L6 = createOldVarsSubst ... ++ inputOnlyOldSubst_L6.
                      -- Map.find? on append: split via Map.find?_append.
                      have HfApp := Hf
                      show δ σ_R1 w =
                          δ σO (Lambda.LExpr.fvar () k none)
                      -- Case split on `Map.find? createOldVarsSubst k`.
                      cases hfind : Map.find?
                                      (Core.Transform.createOldVarsSubst
                                        oldTripsCanonical_L6) k with
                      | some v =>
                        -- find? oldSubst_L6 k = some v (via Map.find?_append
                        -- + this branch).  HfApp tells us it's `some w`,
                        -- so v = w.
                        have HH := Map.find?_append
                          (Core.Transform.createOldVarsSubst
                            oldTripsCanonical_L6) inputOnlyOldSubst_L6 k
                        rw [hfind] at HH
                        -- HH : (createOldVarsSubst ... ++ inputOnlyOldSubst_L6).find? k = some v
                        have Hvw : v = w := by
                          have HfApp_unfold :
                            Map.find?
                              (Core.Transform.createOldVarsSubst
                                oldTripsCanonical_L6 ++
                                  inputOnlyOldSubst_L6) k = some w := HfApp
                          have Hcombined := HH.symm.trans HfApp_unfold
                          exact Option.some_inj.mp Hcombined
                        rw [← Hvw]
                        exact HoldSubBridge k v hfind
                      | none =>
                        -- find? oldSubst_L6 k = find? inputOnlyOldSubst_L6 k.
                        have HH := Map.find?_append
                          (Core.Transform.createOldVarsSubst
                            oldTripsCanonical_L6) inputOnlyOldSubst_L6 k
                        rw [hfind] at HH
                        -- HH : (createOldVarsSubst ... ++ inputOnlyOldSubst_L6).find? k =
                        --       inputOnlyOldSubst_L6.find? k
                        have HfApp_unfold :
                            Map.find?
                              (Core.Transform.createOldVarsSubst
                                oldTripsCanonical_L6 ++
                                  inputOnlyOldSubst_L6) k = some w := HfApp
                        have Hin_some :
                            Map.find? inputOnlyOldSubst_L6 k = some w :=
                          HH.symm.trans HfApp_unfold
                        exact HinputSubBridge k w Hin_some
                    -- Build HsurvBridge specialized to c.
                    have Hc_filtered : c ∈ postsFiltered.map (·.snd) ∨
                                        c ∈ proc'.spec.postconditions.values := by
                      right; exact Hc_in
                    -- HsurvBridge wants entry ∈ postsFiltered, not c ∈ ...values.
                    -- We need to find entry' ∈ postsFiltered with entry'.snd = c.
                    -- For the bridge, we just need v ∈ getVars c.expr ⇒
                    -- ¬ isOldTempIdent v, which holds via HpostVarsFresh.
                    have HsurvBridgeC :
                        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression)
                                c.expr,
                          Map.find? oldSubst_L6 v = none →
                          δ σ_R1 (Lambda.LExpr.fvar () v none) =
                            δ σO (Lambda.LExpr.fvar () v none) := by
                      intro v Hv _Hnone
                      -- v ∈ getVars c.expr where c ∈ proc'.spec.postconditions.values.
                      have HvFresh := HpostVarsFresh_via_c c Hc_in v Hv
                      have HvNotOld : ¬ isOldTempIdent v := HvFresh.2.1
                      have HvNotGen : v ∉ genOldIdents := by
                        intro Hg
                        exact HvNotOld
                          ((List.Forall_mem_iff.mp HoldIdentsTemp) v Hg)
                      have Hσ_R1_v_eq_σO :
                          σ_R1 v = σO v := by
                        show (updatedStates σO genOldIdents oldVals) v = σO v
                        exact updatedStates_get_notin HvNotGen
                      have Hwfvr := Hwfvars
                      simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
                      have HwfL :
                          δ σ_R1 (Lambda.LExpr.fvar () v none) = σ_R1 v := by
                        rw [Hwfvr (Lambda.LExpr.fvar () v none) v]
                        simp [Imperative.HasFvar.getFvar]
                      have HwfR :
                          δ σO (Lambda.LExpr.fvar () v none) = σO v := by
                        rw [Hwfvr (Lambda.LExpr.fvar () v none) v]
                        simp [Imperative.HasFvar.getFvar]
                      rw [HwfL, HwfR]
                      exact Hσ_R1_v_eq_σO
                    -- Apply subst_fvars_eval_bridge.
                    have Hbridge :
                        δ σ_R1 (Lambda.LExpr.substFvars c.expr oldSubst_L6) =
                          δ σO c.expr :=
                      subst_fvars_eval_bridge Hwfc Hwfvars Hwfval
                        HsurvBridgeC Hsub
                    rw [Hbridge]
                    -- Now `δ σO c.expr = some HasBool.tt`.
                    -- Bridge proc'.spec.postconditions ↔ proc.spec.postconditions.
                    have Hin_full :
                        c.expr ∈ Procedure.Spec.getCheckExprs
                                    proc.spec.postconditions := by
                      simp only [Procedure.Spec.getCheckExprs, List.mem_map]
                      refine ⟨c, ?_, rfl⟩
                      rw [HprocEq] at Hc_in
                      rw [ListMap.values_eq_map_snd]
                      rw [ListMap.values_eq_map_snd] at Hc_in
                      exact Hc_in
                    have Hin_contains :
                        (Procedure.Spec.getCheckExprs
                            proc.spec.postconditions).contains c.expr = true :=
                      List.contains_iff_mem.mpr Hin_full
                    exact (Hpost c.expr Hin_contains).2
                  -- Hinv: residual invStores σ_R1 σ_havoc.
                  have HrdHavoc_olds_pos :
                      ∀ (i : Nat) (Hi : i < genOldIdents.length)
                        (Hi' : i < oldVals.length),
                        σ_havoc (genOldIdents[i]'Hi) =
                          some (oldVals[i]'Hi') := by
                    -- σ_havoc reads genOldIdents → oldVals (overlay positional,
                    -- via the appended-list semantics of updatedStates).
                    -- Use readValues_updatedStatesSame after a splitting bridge
                    -- (turn ++-unfold of updatedStates into a 2-layer form).
                    have HoldValsLenE :
                        genOldIdents.length = oldVals.length := by
                      have := HoldValsLen
                      have := HgenOldLen
                      omega
                    have HargLen : argTemps.length =
                        argVals.length := by
                      show argTemps.length = argVals.length
                      simp [argTemps, List.unzip_eq_map, Hargtriplen]
                    have HoutLen : outTemps.length =
                        oVals.length := by
                      have H1 : outTemps.length =
                          outTrips.length := by
                        simp [outTemps, List.unzip_eq_map]
                      have H2 : lhs.length = oVals.length :=
                        ReadValuesLength Hevalouts
                      have H3 : outTrips.length = lhs.length := by
                        have HE : outTrips.unzip.snd = lhs := by
                          rw [Heqouts, hCallArgsLhs]
                        have HEL : outTrips.unzip.snd.length = lhs.length := by
                          rw [HE]
                        have HE2 : outTrips.unzip.snd.length = outTrips.length := by
                          simp [List.unzip_eq_map]
                        omega
                      omega
                    -- Decompose σ_havoc as nested updatedStates.
                    -- updatedStates σ (a ++ b) (va ++ vb) =
                    --   updatedStates (updatedStates σ a va) b vb
                    -- via List.zip_append (when |a|=|va|).
                    have HzipAppend1 :
                        (argTemps ++
                            outTemps).zip
                          (argVals ++ oVals) =
                          (argTemps.zip argVals) ++
                          (outTemps.zip oVals) :=
                      List.zip_append HargLen
                    have HzipAppend2 :
                        ((argTemps ++
                            outTemps) ++ genOldIdents).zip
                          ((argVals ++ oVals) ++ oldVals) =
                          ((argTemps ++
                              outTemps).zip
                            (argVals ++ oVals)) ++
                          (genOldIdents.zip oldVals) := by
                      apply List.zip_append
                      simp [List.length_append]
                      omega
                    have HsplitOverlay :
                        σ_havoc =
                        updatedStates
                          (updatedStates σ'
                            (argTemps ++
                              outTemps)
                            (argVals ++ oVals))
                          genOldIdents oldVals := by
                      show updatedStates σ'
                            (argTemps ++
                              outTemps ++ genOldIdents)
                            (argVals ++ oVals ++ oldVals) = _
                      simp only [updatedStates]
                      rw [HzipAppend2, updatedStates'App]
                    have HrdHavoc :
                        ReadValues σ_havoc genOldIdents oldVals := by
                      rw [HsplitOverlay]
                      exact readValues_updatedStatesSame HoldValsLenE HoldNd
                    intro i Hi Hi'
                    exact readValues_get HrdHavoc (i:=i) (hi:=Hi) (hi':=Hi')
                  -- Shared class-(b) decompositions for Hinv/Hpred_disj
                  -- via oldSubst_L6 = createOldVarsSubst ++ inputOnlyOldSubst.
                  have b1_var_witness :
                      ∀ {var : Expression.Ident}
                        {k : Expression.Ident} {w w' : Expression.Expr}
                        (_hfind : Map.find?
                          (Core.Transform.createOldVarsSubst
                            oldTripsCanonical_L6) k = some w')
                        (_Hf : Map.find? oldSubst_L6 k = some w)
                        (_Hv_in : var ∈ Imperative.HasVarsPure.getVars
                                          (P:=Expression) w),
                      ∃ (ni : Nat) (Hni : ni < genOldIdents.length),
                        w = Core.Transform.createFvar
                              (genOldIdents[ni]'Hni) ∧
                        var = genOldIdents[ni]'Hni := by
                    intro var k w w' hfind Hf Hv_in
                    have HH := Map.find?_append
                      (Core.Transform.createOldVarsSubst
                        oldTripsCanonical_L6) inputOnlyOldSubst_L6 k
                    rw [hfind] at HH
                    have Hf_unfold :
                        Map.find?
                          (Core.Transform.createOldVarsSubst
                            oldTripsCanonical_L6 ++
                              inputOnlyOldSubst_L6) k = some w := Hf
                    have Hw'w : w' = w :=
                      Option.some_inj.mp (HH.symm.trans Hf_unfold)
                    obtain ⟨ni_val, Hni_lt, _Hk_eqMkOld, Hw'_eq⟩ :=
                      createOldVarsSubst_pos_decomp HgenOldLen HoldTysLen hfind
                    have Hni_lt_genOld : ni_val < genOldIdents.length := by
                      have := HgenOldLen; omega
                    have Hw_eq : w =
                        Core.Transform.createFvar
                          (genOldIdents[ni_val]'Hni_lt_genOld) := by
                      rw [← Hw'w]; exact Hw'_eq
                    refine ⟨ni_val, Hni_lt_genOld, Hw_eq, ?_⟩
                    rw [Hw_eq] at Hv_in
                    have Hv_in' :
                        var ∈ Imperative.HasVarsPure.getVars (P:=Expression)
                                (Core.Transform.createFvar
                                  (genOldIdents[ni_val]'Hni_lt_genOld)) := Hv_in
                    show var = _
                    simp [Core.Transform.createFvar,
                          Imperative.HasVarsPure.getVars,
                          Lambda.LExpr.LExpr.getVars] at Hv_in'
                    exact Hv_in'
                  -- (b2): miss on createOldVarsSubst, hit on inputOnlyOldSubst.
                  -- Yields `w = inArgs[ni2]`, `w ∈ inArgs`, the input-key
                  -- positional fact, and `var ∈ flatMap getVars inArgs`.
                  have b2_var_witness :
                      ∀ {var : Expression.Ident}
                        {k : Expression.Ident} {w : Expression.Expr}
                        (_hfind_none : Map.find?
                          (Core.Transform.createOldVarsSubst
                            oldTripsCanonical_L6) k = none)
                        (_Hf : Map.find? oldSubst_L6 k = some w)
                        (_Hv_in : var ∈ Imperative.HasVarsPure.getVars
                                          (P:=Expression) w),
                      ∃ (ni2 : Nat) (Hni2 : ni2 < proc'.header.inputs.keys.length)
                          (Hni2' : ni2 < inArgs.length),
                        w = inArgs[ni2]'Hni2' ∧
                        w ∈ inArgs ∧
                        w ∈ CallArg.getInputExprs args ∧
                        (proc'.header.inputs.keys[ni2]'Hni2)
                          ∉ proc'.header.outputs.keys ∧
                        var ∈ List.flatMap
                                (Imperative.HasVarsPure.getVars (P:=Expression))
                                inArgs := by
                    intro var k w hfind_none Hf Hv_in
                    have HH := Map.find?_append
                      (Core.Transform.createOldVarsSubst
                        oldTripsCanonical_L6) inputOnlyOldSubst_L6 k
                    rw [hfind_none] at HH
                    have Hf_unfold :
                        Map.find?
                          (Core.Transform.createOldVarsSubst
                            oldTripsCanonical_L6 ++
                              inputOnlyOldSubst_L6) k = some w := Hf
                    have Hin_some :
                        Map.find? inputOnlyOldSubst_L6 k = some w :=
                      HH.symm.trans Hf_unfold
                    obtain ⟨ni2_val, Hni2_lt_inKeys, Hni2_lt_inArgs,
                            _Hk_eq_proc', Hw_eq_proc', Hin_notin_outs⟩ :=
                      inputOnlyOldSubst_pos_decomp Hin_some
                    have HargExpr_def :
                        w = (CallArg.getInputExprs args)[ni2_val]'Hni2_lt_inArgs :=
                      Hw_eq_proc'
                    have Hni2_lt_inArgsCall :
                        ni2_val < inArgs.length := by
                      have : (CallArg.getInputExprs args).length =
                          inArgs.length := by rw [hCallArgsIn]
                      rw [← this]
                      exact Hni2_lt_inArgs
                    have HargExpr_eq_inArgs :
                        w = inArgs[ni2_val]'Hni2_lt_inArgsCall := by
                      rw [HargExpr_def]
                      show (CallArg.getInputExprs args)[ni2_val]'Hni2_lt_inArgs =
                            inArgs[ni2_val]'Hni2_lt_inArgsCall
                      congr 1 <;> exact hCallArgsIn
                    have Hk1_in_inArgs : w ∈ inArgs := by
                      rw [HargExpr_eq_inArgs]; exact List.getElem_mem _
                    have HargExpr_in : w ∈ CallArg.getInputExprs args := by
                      rw [HargExpr_def]; exact List.getElem_mem _
                    have Hk1_flat :
                        var ∈ List.flatMap
                              (Imperative.HasVarsPure.getVars (P:=Expression))
                              inArgs := by
                      rw [List.mem_flatMap]
                      exact ⟨w, Hk1_in_inArgs, Hv_in⟩
                    refine ⟨ni2_val, Hni2_lt_inKeys, Hni2_lt_inArgsCall,
                            HargExpr_eq_inArgs, Hk1_in_inArgs, HargExpr_in,
                            Hin_notin_outs, Hk1_flat⟩
                  have Hinv :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        Imperative.invStores σ_R1 σ_havoc
                          ((Imperative.HasVarsPure.getVars (P:=Expression)
                              entry.snd.expr).removeAll
                            (filtered_ks ++ filtered_ks')) := by
                    intro entry Hentry
                    obtain ⟨c, Hc_in, Hentry_eq⟩ :=
                      forall_post_filtered_decompose entry Hentry
                    -- Open invStores.
                    simp only [Imperative.invStores, Imperative.substStores]
                    intros k1 k2 Hkin
                    have Hk_eq := zip_self_eq Hkin
                    subst Hk_eq
                    have Hk1_in : k1 ∈
                        (Imperative.HasVarsPure.getVars (P:=Expression)
                          entry.snd.expr).removeAll
                          (filtered_ks ++ filtered_ks') :=
                      (List.of_mem_zip Hkin).1
                    -- Decompose removeAll.
                    have Hk1_inDecomp :
                        k1 ∈ Imperative.HasVarsPure.getVars
                                (P:=Expression) entry.snd.expr ∧
                        k1 ∉ filtered_ks ++ filtered_ks' := by
                      simp only [List.removeAll, List.mem_filter,
                                 List.elem_eq_mem, Bool.not_eq_true',
                                 decide_eq_false_iff_not] at Hk1_in
                      exact Hk1_in
                    obtain ⟨Hk1_pre, Hk1_notin_combined⟩ := Hk1_inDecomp
                    -- Decompose `k1 ∉ (outputs ++ filtered_inputs) ++
                    -- (lhs ++ filtered_argTemps)` into 4 leaf facts.
                    obtain ⟨Hk1_notin_outs, Hk1_notin_filtIn,
                            Hk1_notin_lhs, Hk1_notin_filtArgT⟩ :=
                      List.notin_append4 Hk1_notin_combined
                    -- entry.snd.expr = substFvars c.expr oldSubst_L6.
                    rw [Hentry_eq] at Hk1_pre
                    -- Decompose k1 ∈ getVars (substFvars c.expr oldSubst_L6).
                    rcases getVars_substFvars_mem Hk1_pre with
                      Hclass_a | ⟨k, w, Hk_in, Hf, Hv_in⟩
                    · -- ── Class (a): k1 ∈ getVars c.expr ∧ find? oldSubst_L6 k1 = none ──
                      obtain ⟨Hk1_post, _Hf_none⟩ := Hclass_a
                      -- HpostsVarsFresh_orig: ¬tmp_, ¬old_, k1 ∉ lhs.
                      have HfreshK := HpostVarsFresh_via_c c Hc_in k1 Hk1_post
                      have Hk1_notTemp : ¬ isTempIdent k1 := HfreshK.1
                      have Hk1_notOld : ¬ isOldTempIdent k1 := HfreshK.2.1
                      -- k1 ∉ argTemps (tmp_).
                      have Hk1_notin_argT :
                          k1 ∉ argTemps := fun h =>
                        Hk1_notTemp ((List.Forall_mem_iff.mp HargTemp) k1 h)
                      have Hk1_notin_outT :
                          k1 ∉ outTemps := fun h =>
                        Hk1_notTemp ((List.Forall_mem_iff.mp HoutTemp) k1 h)
                      have Hk1_notin_genOld :
                          k1 ∉ genOldIdents := fun h =>
                        Hk1_notOld
                          ((List.Forall_mem_iff.mp HoldIdentsTemp) k1 h)
                      -- k1 ∉ inputs.keys (since k1 ∉ outputs and k1 ∉ filtered_inputs).
                      have Hk1_notin_ins :
                          k1 ∉ proc.header.inputs.keys := by
                        intro h
                        -- k1 ∈ inputs.keys, k1 ∉ outputs.keys ⇒ k1 ∈ filtered_inputs.
                        rcases List.mem_iff_get.mp h with ⟨n, Hn⟩
                        have Hn_lt_in : n.val < proc.header.inputs.keys.length := n.isLt
                        have Hn_lt_argT : n.val < argTemps.length := by
                          rw [← HinKeys_argTemps_len]; exact Hn_lt_in
                        have HkE :
                            proc.header.inputs.keys[n.val]'Hn_lt_in = k1 := by
                          have HEget := Hn
                          have :
                              proc.header.inputs.keys[n.val]'Hn_lt_in =
                                proc.header.inputs.keys.get
                                  ⟨n.val, Hn_lt_in⟩ := rfl
                          rw [this]; exact HEget
                        have Hpair_in_zip :
                            (k1, argTemps[n.val]'Hn_lt_argT) ∈
                              proc.header.inputs.keys.zip argTemps := by
                          rw [← HkE]
                          apply List.mem_iff_get.mpr
                          have HzL : (proc.header.inputs.keys.zip argTemps).length =
                              min proc.header.inputs.keys.length argTemps.length :=
                            List.length_zip
                          have Hn_lt_zip :
                              n.val < (proc.header.inputs.keys.zip argTemps).length := by
                            rw [HzL]
                            have := HinKeys_argTemps_len
                            omega
                          refine ⟨⟨n.val, Hn_lt_zip⟩, ?_⟩
                          show (proc.header.inputs.keys.zip argTemps)[n.val]'_ = _
                          exact List.getElem_zip
                        have Hpair_in_filtAS :
                            (k1, argTemps[n.val]'Hn_lt_argT) ∈
                              filtered_argSubst := by
                          apply List.mem_filter.mpr
                          refine ⟨Hpair_in_zip, ?_⟩
                          simp only [decide_not, Bool.not_eq_eq_eq_not,
                                     Bool.not_true, decide_eq_false_iff_not,
                                     List.contains_iff_mem]
                          exact Hk1_notin_outs
                        have Hk1_in_unzip :
                            k1 ∈ filtered_inputs := by
                          show k1 ∈ filtered_argSubst.unzip.fst
                          simp only [List.unzip_eq_map, List.mem_map]
                          refine ⟨(k1, argTemps[n.val]'Hn_lt_argT), Hpair_in_filtAS, rfl⟩
                        exact Hk1_notin_filtIn Hk1_in_unzip
                      -- σ_R1 k1 = σ k1 via the layered store-agreement
                      -- helper, then chain through σ' and σ_havoc.
                      have HσR1_σ :
                          updatedStates σO genOldIdents oldVals k1 = σ k1 :=
                        σR1_eq_σ_for_notTouched Hinitin Hinitout Hhav1
                          Hk1_notin_ins Hk1_notin_outs Hk1_notin_genOld
                      -- σ k1 = σ' k1 (k1 ∉ lhs; Hupdate).
                      have H5 : σ k1 = σ' k1 := by
                        rw [Hσ'_eq, updatedStates_get_notin Hk1_notin_lhs]
                      -- σ' k1 = σ_havoc k1 (k1 ∉ argT/outT/genOld).
                      have Hk1_notin_layered :
                          k1 ∉ argTemps ++
                                outTemps ++ genOldIdents := by
                        intro h
                        rcases List.mem_append.mp h with h | h
                        · rcases List.mem_append.mp h with h | h
                          · exact Hk1_notin_argT h
                          · exact Hk1_notin_outT h
                        · exact Hk1_notin_genOld h
                      have H6 : σ' k1 = σ_havoc k1 := by
                        show σ' k1 =
                          updatedStates σ'
                            (argTemps ++
                              outTemps ++ genOldIdents)
                            (argVals ++ oVals ++ oldVals) k1
                        rw [updatedStates_get_notin Hk1_notin_layered]
                      show updatedStates σO genOldIdents oldVals k1 = σ_havoc k1
                      rw [HσR1_σ, H5, H6]
                    · -- ── Class (b): k1 ∈ getVars w for some (k, w) ∈ oldSubst_L6 ──
                      -- Split via Map.find?_append.
                      cases hfind : Map.find?
                                      (Core.Transform.createOldVarsSubst
                                        oldTripsCanonical_L6) k with
                      | some w' =>
                        -- (b1) createOldVarsSubst flavor — via shared helper.
                        obtain ⟨ni_val, Hni_lt_genOld, _Hw_eq, Hv_eq_gen⟩ :=
                          b1_var_witness hfind Hf Hv_in
                        -- σ_R1 k1 = oldVals[ni_val]; σ_havoc k1 = oldVals[ni_val].
                        have Hni_lt_oldVals :
                            ni_val < oldVals.length := by
                          have := HoldValsLen; omega
                        have HoldValsLenE' :
                            genOldIdents.length = oldVals.length := by
                          have := HoldValsLen
                          have := HgenOldLen
                          omega
                        have HrdR1_olds :
                            ReadValues σ_R1 genOldIdents oldVals := by
                          show ReadValues
                            (updatedStates σO genOldIdents oldVals)
                            genOldIdents oldVals
                          exact readValues_updatedStatesSame
                                  HoldValsLenE' HoldNd
                        have Hσ_R1_v :
                            σ_R1 (genOldIdents[ni_val]'Hni_lt_genOld) =
                              some (oldVals[ni_val]'Hni_lt_oldVals) :=
                          readValues_get HrdR1_olds
                            (i:=ni_val) (hi:=Hni_lt_genOld) (hi':=Hni_lt_oldVals)
                        have Hσ_havoc_v :
                            σ_havoc (genOldIdents[ni_val]'Hni_lt_genOld) =
                              some (oldVals[ni_val]'Hni_lt_oldVals) :=
                          HrdHavoc_olds_pos ni_val Hni_lt_genOld Hni_lt_oldVals
                        rw [Hv_eq_gen, Hσ_R1_v, Hσ_havoc_v]
                      | none =>
                        -- (b2) inputOnlyOldSubst flavor — via shared helper.
                        obtain ⟨_ni2_val, _Hni2_lt_inKeys, _Hni2_lt_inArgs,
                                _HargExpr_eq_inArgs, _Hk1_in_inArgs, HargExpr_in,
                                _Hin_notin_outs, Hk1_flat⟩ :=
                          b2_var_witness hfind Hf Hv_in
                        -- k1 ∈ getVars w.  By HargVarsNotIn{Out,In}Keys:
                        have Hk1_notin_outs' :
                            k1 ∉ proc.header.outputs.keys :=
                          HargVarsNotInOutKeys w HargExpr_in k1 Hv_in
                        have Hk1_notin_ins' :
                            k1 ∉ proc.header.inputs.keys :=
                          HargVarsNotInInKeys w HargExpr_in k1 Hv_in
                        -- k1 ∈ σ-defined via Hevalargs.
                        have HargIsDef :
                            Imperative.isDefined σ
                              (List.flatMap
                                (Imperative.HasVarsPure.getVars (P:=Expression))
                                inArgs) :=
                          evalExpressions_isDefined_flatMap Hevalargs
                        have Hk1_σ_some : (σ k1).isSome := HargIsDef k1 Hk1_flat
                        -- k1 not isOldTempIdent.
                        have Hk1_notOld' : ¬ isOldTempIdent k1 := by
                          intro Hold
                          have HNone := Hgenrel.oldFresh k1 Hold
                          have HSome : ¬ (σ k1).isNone := by
                            simp only [Option.isNone_iff_eq_none,
                                       ← Option.isSome_iff_ne_none]
                            exact Hk1_σ_some
                          exact HSome HNone
                        -- k1 not isTempIdent.  Via isNotDefined of argTemps/outTemps.
                        have Hk1_notin_argT' :
                            k1 ∉ argTemps := by
                          intro h
                          have := HndefArg_σ k1 h
                          rw [this] at Hk1_σ_some
                          simp at Hk1_σ_some
                        have Hk1_notin_outT' :
                            k1 ∉ outTemps := by
                          intro h
                          have := HndefOut_σ k1 h
                          rw [this] at Hk1_σ_some
                          simp at Hk1_σ_some
                        have Hk1_notin_genOld' :
                            k1 ∉ genOldIdents := by
                          intro h
                          have := HndefOld_σ k1 h
                          rw [this] at Hk1_σ_some
                          simp at Hk1_σ_some
                        -- σ_R1 k1 = σ_havoc k1 via the layered store-
                        -- agreement helper, plus the σ → σ' → σ_havoc tail.
                        have HσR1_σ :
                            updatedStates σO genOldIdents oldVals k1 = σ k1 :=
                          σR1_eq_σ_for_notTouched Hinitin Hinitout Hhav1
                            Hk1_notin_ins' Hk1_notin_outs' Hk1_notin_genOld'
                        have H5 : σ k1 = σ' k1 := by
                          rw [Hσ'_eq, updatedStates_get_notin Hk1_notin_lhs]
                        have Hk1_notin_layered :
                            k1 ∉ argTemps ++
                                  outTemps ++ genOldIdents := by
                          intro h
                          rcases List.mem_append.mp h with h | h
                          · rcases List.mem_append.mp h with h | h
                            · exact Hk1_notin_argT' h
                            · exact Hk1_notin_outT' h
                          · exact Hk1_notin_genOld' h
                        have H6 : σ' k1 = σ_havoc k1 := by
                          show σ' k1 =
                            updatedStates σ'
                              (argTemps ++
                                outTemps ++ genOldIdents)
                              (argVals ++ oVals ++ oldVals) k1
                          rw [updatedStates_get_notin Hk1_notin_layered]
                        show updatedStates σO genOldIdents oldVals k1 = σ_havoc k1
                        rw [HσR1_σ, H5, H6]
                  -- Hpred_disj: filtered_ks' disjoint from entry's vars.
                  have HfiltArgT_sub_argT :
                      ∀ x ∈ filtered_argTemps, x ∈ argTemps := by
                    intro x Hx
                    show x ∈ argTemps
                    -- filtered_argTemps = filtered_argSubst.unzip.snd ⊆ argTemps.
                    have Hx' : x ∈ filtered_argSubst.unzip.snd := Hx
                    simp only [List.unzip_eq_map, List.mem_map] at Hx'
                    rcases Hx' with ⟨pair, Hpair_mem, Hpair_snd⟩
                    have Hpair_in_zip := (List.mem_filter.mp Hpair_mem).1
                    -- pair ∈ inputs.keys.zip argTemps ⇒ pair.snd ∈ argTemps.
                    have Hsnd_in :
                        pair.snd ∈ argTemps :=
                      (List.of_mem_zip Hpair_in_zip).2
                    rw [← Hpair_snd]; exact Hsnd_in
                  have Hpred_disj :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        filtered_ks'.Disjoint
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr) := by
                    intro entry Hentry
                    obtain ⟨c, Hc_in, Hentry_eq⟩ :=
                      forall_post_filtered_decompose entry Hentry
                    intro x Hin1 Hin2
                    -- x ∈ filtered_ks' = lhs ++ filtered_argTemps.
                    -- x ∈ entry.snd.expr.getVars.
                    rw [Hentry_eq] at Hin2
                    rcases getVars_substFvars_mem Hin2 with
                      Hclass_a | ⟨k', w, Hk_in, Hf, Hv_in⟩
                    · -- ── Class (a): x ∈ getVars c.expr ──
                      obtain ⟨Hx_post, _Hf_none⟩ := Hclass_a
                      -- HpostsVarsFresh_orig: ¬tmp_, ¬old_, x ∉ lhs.
                      have HfreshK := HpostVarsFresh_via_c c Hc_in x Hx_post
                      have Hx_notTemp : ¬ isTempIdent x := HfreshK.1
                      have Hx_notLhs : x ∉ CallArg.getLhs args := HfreshK.2.2
                      -- Show contradiction.
                      cases List.mem_append.mp Hin1 with
                      | inl Hx_lhs =>
                        rw [hCallArgsLhs] at Hx_notLhs
                        exact Hx_notLhs Hx_lhs
                      | inr Hx_filtArgT =>
                        have Hx_argT : x ∈ argTemps :=
                          HfiltArgT_sub_argT x Hx_filtArgT
                        exact Hx_notTemp
                          ((List.Forall_mem_iff.mp HargTemp) x Hx_argT)
                    · -- ── Class (b): x ∈ getVars w for some (k', w) ∈ oldSubst_L6 ──
                      cases hfind : Map.find?
                                      (Core.Transform.createOldVarsSubst
                                        oldTripsCanonical_L6) k' with
                      | some w' =>
                        -- (b1) createOldVarsSubst flavor — via shared helper.
                        obtain ⟨ni_val, Hni_lt_genOld, _Hw_eq, Hx_eq_gen⟩ :=
                          b1_var_witness hfind Hf Hv_in
                        rw [Hx_eq_gen] at Hin1
                        -- genOldIdents[ni_val] ∈ filtered_ks' = lhs ++ filtered_argTemps.
                        -- Each branch yields contradiction.
                        cases List.mem_append.mp Hin1 with
                        | inl Hx_lhs =>
                          -- HlhsDisjOld: lhs.Disjoint genOldIdents.
                          exact HlhsDisjOld Hx_lhs (List.getElem_mem _)
                        | inr Hx_filtArgT =>
                          -- genOldIdents[i] is isOldTempIdent, but
                          -- filtered_argTemps ⊆ argTemps which are isTempIdent;
                          -- and isTempIdent and isOldTempIdent are disjoint
                          -- (via HoldIdentsTemp + HargTemp).
                          have Hx_argT :
                              genOldIdents[ni_val]'Hni_lt_genOld ∈ argTemps :=
                            HfiltArgT_sub_argT _ Hx_filtArgT
                          have Hx_isTemp : isTempIdent
                              (genOldIdents[ni_val]'Hni_lt_genOld) :=
                            (List.Forall_mem_iff.mp HargTemp) _ Hx_argT
                          have Hx_isOld : isOldTempIdent
                              (genOldIdents[ni_val]'Hni_lt_genOld) :=
                            (List.Forall_mem_iff.mp HoldIdentsTemp)
                              _ (List.getElem_mem _)
                          exact isTempIdent_isOldTempIdent_disjoint
                            Hx_isTemp Hx_isOld
                      | none =>
                        -- (b2) inputOnlyOldSubst flavor — via shared helper.
                        obtain ⟨_ni2_val, _Hni2_lt_inKeys, _Hni2_lt_inArgs,
                                _HargExpr_eq_inArgs, _Hk1_in_inArgs, HargExpr_in,
                                _Hin_notin_outs, Hx_flat⟩ :=
                          b2_var_witness hfind Hf Hv_in
                        -- x ∈ σ-defined via Hevalargs.
                        have HargIsDef :
                            Imperative.isDefined σ
                              (List.flatMap
                                (Imperative.HasVarsPure.getVars (P:=Expression))
                                inArgs) :=
                          evalExpressions_isDefined_flatMap Hevalargs
                        have Hx_σ_some : (σ x).isSome := HargIsDef x Hx_flat
                        -- Now case-split on x ∈ filtered_ks'.
                        cases List.mem_append.mp Hin1 with
                        | inl Hx_lhs =>
                          -- x ∉ lhs via HargVarsNotInLhs (clause 3).
                          have Hx_notLhs :
                              x ∉ CallArg.getLhs args :=
                            HargVarsNotInLhs w HargExpr_in x Hv_in
                          rw [hCallArgsLhs] at Hx_notLhs
                          exact Hx_notLhs Hx_lhs
                        | inr Hx_filtArgT =>
                          -- x ∈ argTemps ⇒ σ x = none, but σ x is some.
                          have Hx_argT :
                              x ∈ argTemps :=
                            HfiltArgT_sub_argT x Hx_filtArgT
                          have Hx_σ_none : σ x = none := HndefArg_σ x Hx_argT
                          rw [Hx_σ_none] at Hx_σ_some
                          simp at Hx_σ_some
                  -- HpostPayload: combined per-entry payload for L6.
                  have HpostPayload :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        Imperative.invStores σ_R1 σ_havoc
                          ((Imperative.HasVarsPure.getVars (P:=Expression)
                              entry.snd.expr).removeAll
                            (filtered_ks ++ filtered_ks')) ∧
                        filtered_ks'.Disjoint
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr) ∧
                        δ σ_R1 entry.snd.expr =
                          some Imperative.HasBool.tt := by
                    intro entry Hentry
                    refine ⟨Hinv entry Hentry,
                            Hpred_disj entry Hentry,
                            HpostEval_bridge entry Hentry⟩
                  -- D2f: Apply H_assumes_zip to derive HL6 (L6 segment of glue).
                  obtain ⟨assumeLabels, _HassumeLabelsLen, HassumeShape⟩ :=
                    HassumesShape
                  -- Bridge: `assumeSubst = filtered_ks.zip (createFvars filtered_ks')`.
                  have HassumeSubst_eq :
                      ((proc'.header.outputs.keys.zip
                          (Core.Transform.createFvars (CallArg.getLhs args))) ++
                        (proc'.header.inputs.keys.zip
                          (Core.Transform.createFvars argTemps)).filter
                          (fun (id, _) =>
                            !(ListMap.keys proc'.header.outputs).contains id)) =
                      filtered_ks.zip
                        (Core.Transform.createFvars filtered_ks') := by
                    rw [HprocEq]
                    show _ = (proc.header.outputs.keys ++ filtered_inputs).zip
                      (Core.Transform.createFvars (lhs ++ filtered_argTemps))
                    rw [createFvarsApp]
                    rw [List.zip_append
                          (show proc.header.outputs.keys.length =
                                (Core.Transform.createFvars lhs).length by
                            rw [createFvarsLength,
                                HoutKeys_lhs_len])]
                    -- Head: bridge via hCallArgsLhs.
                    rw [hCallArgsLhs]
                    congr 1
                    show (proc.header.inputs.keys.zip
                          (argTemps.map Core.Transform.createFvar)).filter _ =
                      filtered_argSubst.unzip.fst.zip
                        (filtered_argSubst.unzip.snd.map
                          Core.Transform.createFvar)
                    rw [List.zip_map_right]
                    rw [List.filter_map]
                    -- Bridge composed `!`/`Prod.map` filter to filtered_argSubst.
                    have HfiltEq :
                        (proc.header.inputs.keys.zip argTemps).filter
                          ((fun (x : Expression.Ident × Expression.Expr) =>
                              !(ListMap.keys proc.header.outputs).contains x.1) ∘
                            Prod.map id Core.Transform.createFvar) =
                          filtered_argSubst := by
                      show _ = (proc.header.inputs.keys.zip argTemps).filter
                          (fun pr =>
                            ¬ (proc.header.outputs.keys).contains pr.1)
                      apply List.filter_congr
                      intro pr _
                      cases pr with
                      | mk a b =>
                        by_cases h :
                            (ListMap.keys proc.header.outputs).contains a
                        · simp [h, Function.comp, Prod.map]
                        · simp [h, Function.comp, Prod.map]
                    rw [HfiltEq]
                    -- Massage the RHS: zip_map_right reverse + zip_unzip.
                    rw [show filtered_argSubst.unzip.fst.zip
                            (filtered_argSubst.unzip.snd.map
                              Core.Transform.createFvar) =
                          (filtered_argSubst.unzip.fst.zip
                            filtered_argSubst.unzip.snd).map
                            (Prod.map id Core.Transform.createFvar) from
                        List.zip_map_right]
                    rw [show filtered_argSubst.unzip.fst.zip
                            filtered_argSubst.unzip.snd =
                          filtered_argSubst from List.zip_unzip _]
                  -- ── Apply H_assumes_zip ──
                  have HL6_pre :
                      EvalStatementsContract π φ ⟨σ_havoc, δ, false⟩
                        ((posts_filtered_L6.zip assumeLabels).map
                          (fun (entry, lbl) =>
                            Statement.assume lbl
                              (Lambda.LExpr.substFvars entry.snd.expr
                                (filtered_ks.zip
                                  (Core.Transform.createFvars filtered_ks')))
                              (entry.snd.md.setCallSiteFileRange md)))
                        ⟨σ_havoc, δ, false⟩ := by
                    apply H_assumes_zip
                      (σA := σ_R1) (σ' := σ_havoc)
                      (ks := filtered_ks)
                      (ks' := filtered_ks')
                      (posts := posts_filtered_L6.toList)
                      (labels := assumeLabels)
                      Hwfb Hwfvars Hwfval Hwfc
                      Hkslen Hnd Hdef Hsubst
                    intros entry Hentry
                    exact HpostPayload entry Hentry
                  -- Bridge to the actual `assumes` list via HassumeShape.
                  have HL6 :
                      EvalStatementsContract π φ ⟨σ_havoc, δ, false⟩
                        assumes ⟨σ_havoc, δ, false⟩ := by
                    -- HassumeShape proc'-keys agree with proc via HprocEq.
                    rw [HassumeShape]
                    rw [HassumeSubst_eq]
                    exact HL6_pre
                  -- ── D2g: Chain L1-L6 via EvalCallElim_glue ──
                  exact EvalCallElim_glue HL1 HL2 HL3 HL4 HL5 HL6
          · -- inner `Except.error` branch — contradiction
            rename_i e_err heq_err
            simp only [pure, StateT.pure, Prod.mk.injEq] at Helim
            exact absurd Helim.1 (by simp)

end -- public section

end CallElimCorrect
