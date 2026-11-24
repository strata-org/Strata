/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.Denote.LExprAnnotatedProps
public import Strata.DL.Lambda.Denote.LExprResolveAnnotated
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LExprTProps
public import Strata.DL.Lambda.TypeFactoryProps
public import Strata.Util.StringProps
public import Strata.Util.ListUtilsProps
public import Strata.Util.HMapsProps
import Strata.Util.NameProofs
import Strata.DL.Imperative.CmdProps
public import Strata.Languages.Core.WF
import Strata.Languages.Core.StatementProps
import Strata.Languages.Core.ProcedureProps
public import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
import Strata.Languages.Core.CallWFProps
import Strata.Languages.Core.IdentifiersProps
import Strata.DL.Lambda.LTyWFCheckSound
import Strata.DL.Lambda.LTyWF
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.DL.Lambda.LExprAliasFree
import Strata.DL.Lambda.LExprAnnotRel
import Strata.DL.Lambda.LExprWFProps
import Strata.Languages.Core.Statement
import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.Stmt
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.LTyWFProps
import Strata.DL.Lambda.NamePrefixesProps
import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Typing.Props.SkolemScopeProps
public import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
import all Strata.Languages.Core.Typing.Props.TypeSkolemProps

/-! # Properties of the skolemizer's output

Deskolemization undoes the skolemizer, and the skolemizer's output keeps its annotations
free of rigid-name clashes and adds no free variables.

Key theorems:
* `mapExprTys_deskolemizeTy_skolemizeBody`: deskolemizing a skolemized expression gives back the
  original expression.
* `mapStmtsTys_deskolemizeTy_skolemizeStmts`: the same for statement lists. -/

public section

namespace Core

open Lambda Imperative

open Strata.Util (HMap HMaps)

/-! ## Deskolemization undoes the skolemizer -/

/-- Deskolemizing by `σ` undoes skolemizing an expression by `σ` when its annotations name no
    constant of `σ` and the constants of `σ` are distinct. -/
theorem mapExprTys_deskolemizeTy_skolemizeBody (nm : Option String)
    {σ : RigidNames} (hnd : (σ.map Prod.snd).Nodup) (e : Expression.Expr)
    (hallowed : allExprTys (mtyAllTyConsNames (notRigidConst σ)) e = true) :
    mapExprTys (deskolemizeTy σ) (skolemizeBody nm σ e) = e := by
  have annot_roundtrip (uty : Option LMonoTy)
      (h : uty.all (mtyAllTyConsNames (notRigidConst σ)) = true) :
      (uty.map (skolemizeTy σ)).map (deskolemizeTy σ) = uty ∧
        uty.map (deskolemizeTy σ) = uty := by
    cases uty with
    | none => simp
    | some t =>
      simp only [Option.all_some] at h
      have hfix : deskolemizeTy σ t = t :=
        deskolemizeTy_eq_self_of_notRigidConst t h
      refine ⟨?_, by simp only [Option.map_some, hfix]⟩
      simp only [Option.map_some, deskolemizeTy_skolemizeTy_eq_deskolemizeTy hnd, hfix]
  rw [allExprTys_eq_allUserProvidedTypes] at hallowed
  show LExpr.replaceUserProvidedType (skolemizeBody nm σ e) (deskolemizeTy σ) = e
  induction e with
  | const m c => rfl
  | bvar m b => rfl
  | op m o uty =>
    simp only [LExpr.allUserProvidedTypes] at hallowed
    obtain ⟨hsk, hfix⟩ := annot_roundtrip uty hallowed
    simp only [skolemizeBody_op]
    split
    · simp only [LExpr.replaceUserProvidedType, hsk]
    · simp only [LExpr.replaceUserProvidedType, hfix]
  | fvar m x uty =>
    simp only [LExpr.allUserProvidedTypes] at hallowed
    simp only [skolemizeBody_fvar, LExpr.replaceUserProvidedType,
      (annot_roundtrip uty hallowed).1]
  | abs m n uty b ihb =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hallowed
    simp only [skolemizeBody_abs, LExpr.replaceUserProvidedType,
      (annot_roundtrip uty hallowed.1).1, ihb hallowed.2]
  | quant m qk n aty tr b ihtr ihb =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hallowed
    simp only [skolemizeBody_quant, LExpr.replaceUserProvidedType,
      (annot_roundtrip aty hallowed.1.1).1, ihtr hallowed.1.2, ihb hallowed.2]
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hallowed
    simp only [skolemizeBody_app, LExpr.replaceUserProvidedType, ih1 hallowed.1, ih2 hallowed.2]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hallowed
    simp only [skolemizeBody_ite, LExpr.replaceUserProvidedType,
      ihc hallowed.1.1, iht hallowed.1.2, ihf hallowed.2]
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hallowed
    simp only [skolemizeBody_eq, LExpr.replaceUserProvidedType, ih1 hallowed.1, ih2 hallowed.2]

/-- Deskolemization undoes the skolemizer on an `ExprOrNondet`. -/
private theorem exprOrNondet_deskolemize_roundtrip (nm : Option String) (σ : RigidNames)
    (hnd : (σ.map Prod.snd).Nodup)
    (e : ExprOrNondet Expression)
    (h : allExprOrNondetTys (mtyAllTyConsNames (notRigidConst σ)) e = true) :
    (e.map (skolemizeBody nm σ ·)).map (mapExprTys (deskolemizeTy σ) ·) = e := by
  cases e with
  | nondet => rfl
  | det e' =>
    simp only [allExprOrNondetTys] at h
    simp only [ExprOrNondet.map,
      mapExprTys_deskolemizeTy_skolemizeBody nm hnd e' h]

/-- Deskolemization undoes the skolemizer on an optional expression. -/
private theorem optExpr_deskolemize_roundtrip (nm : Option String) (σ : RigidNames)
    (hnd : (σ.map Prod.snd).Nodup)
    (m : Option Expression.Expr)
    (h : m.all (allExprTys (mtyAllTyConsNames (notRigidConst σ))) = true) :
    (m.map (skolemizeBody nm σ ·)).map (mapExprTys (deskolemizeTy σ) ·) = m := by
  cases m with
  | none => rfl
  | some e =>
    simp only [Option.all_some] at h
    simp only [Option.map_some,
      mapExprTys_deskolemizeTy_skolemizeBody nm hnd e h]

/-- Deskolemization undoes the skolemizer on a list of labeled expressions. -/
private theorem labeled_deskolemize_roundtrip (nm : Option String) (σ : RigidNames)
    (hnd : (σ.map Prod.snd).Nodup)
    (i : List (String × Expression.Expr))
    (h : i.all (fun (_, e) => allExprTys (mtyAllTyConsNames (notRigidConst σ)) e) = true) :
    (i.map (fun (l, e) => (l, skolemizeBody nm σ e))).map
        (fun (l, e) => (l, mapExprTys (deskolemizeTy σ) e)) = i := by
  induction i with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨l, e⟩ := p
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, ih h.2,
      mapExprTys_deskolemizeTy_skolemizeBody nm hnd e h.1]

/-- Deskolemization undoes the skolemizer on a command whose annotations name no constant
    of `σ`. -/
private theorem mapCmdTys_deskolemizeTy_skolemizeCmd (nm : Option String) (σ : RigidNames)
    (hnd : (σ.map Prod.snd).Nodup) (c : Command)
    (hallowed : allCmdTys (mtyAllTyConsNames (notRigidConst σ)) c = true) :
    mapCmdTys (deskolemizeTy σ) (skolemizeCmd nm σ c) = c := by
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      simp only [allCmdTys, Bool.and_eq_true] at hallowed
      simp only [skolemizeCmd, mapCmdTys, mapCmdWith,
        mapLTyTys_deskolemize_roundtrip σ hnd ty hallowed.1,
        exprOrNondet_deskolemize_roundtrip nm σ hnd e hallowed.2]
    | set x e md =>
      simp only [allCmdTys] at hallowed
      simp only [skolemizeCmd, mapCmdTys, mapCmdWith,
        exprOrNondet_deskolemize_roundtrip nm σ hnd e hallowed]
    | assert l b md =>
      simp only [allCmdTys] at hallowed
      simp only [skolemizeCmd, mapCmdTys, mapCmdWith,
        mapExprTys_deskolemizeTy_skolemizeBody nm hnd b hallowed]
    | assume l b md =>
      simp only [allCmdTys] at hallowed
      simp only [skolemizeCmd, mapCmdTys, mapCmdWith,
        mapExprTys_deskolemizeTy_skolemizeBody nm hnd b hallowed]
    | cover l b md =>
      simp only [allCmdTys] at hallowed
      simp only [skolemizeCmd, mapCmdTys, mapCmdWith,
        mapExprTys_deskolemizeTy_skolemizeBody nm hnd b hallowed]
  | call pname tyArgs args md =>
    simp only [allCmdTys, Bool.and_eq_true, List.all_eq_true] at hallowed
    have htys : (tyArgs.map (·.map (mapLTyTys (skolemizeTy σ)))).map
        (·.map (mapLTyTys (deskolemizeTy σ))) = tyArgs := by
      cases tyArgs with
      | none => rfl
      | some tys =>
        have hall := hallowed.1
        simp only [Option.all_some, List.all_eq_true] at hall
        simp only [Option.map_some, List.map_map, Option.some.injEq]
        refine Eq.trans (List.map_congr_left ?_) (List.map_id tys)
        intro ty hty
        exact mapLTyTys_deskolemize_roundtrip σ hnd ty (hall ty hty)
    replace hallowed := hallowed.2
    simp only [skolemizeCmd, mapCmdTys, mapCmdWith, List.map_map, htys, CmdExt.call.injEq,
      true_and, and_true]
    refine Eq.trans (List.map_congr_left ?_) (List.map_id args)
    intro a ha
    have hone := hallowed a ha
    cases a with
    | inArg e =>
      simp only at hone
      simp only [Function.comp_apply, id_eq, CallArg.mapInput,
        mapExprTys_deskolemizeTy_skolemizeBody nm hnd e hone]
    | inoutArg id => rfl
    | outArg id => rfl

/-- Deskolemization undoes the skolemizer on a statement list whose annotations name no
    constant of `σ`. -/
theorem mapStmtsTys_deskolemizeTy_skolemizeStmts (nm : Option String) (σ : RigidNames)
    (hnd : (σ.map Prod.snd).Nodup)
    (ss : List Statement)
    (hallowed : allStmtsTys (mtyAllTyConsNames (notRigidConst σ)) ss = true) :
    mapStmtsTys (deskolemizeTy σ) (skolemizeStmts nm σ ss) = ss := by
  revert hallowed
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      allStmtTys (mtyAllTyConsNames (notRigidConst σ)) s = true →
        mapStmtTys (deskolemizeTy σ) (skolemizeStmt nm σ s) = s) with
  | case1 c =>
    rename_i h
    simp only [allStmtTys] at h
    simp only [skolemizeStmt_cmd, mapStmtTys_cmd,
      mapCmdTys_deskolemizeTy_skolemizeCmd nm σ hnd c h]
  | case2 l bss md ih =>
    rename_i h
    simp only [allStmtTys] at h
    simp only [skolemizeStmt_block, mapStmtTys_block, ih h]
  | case3 c tss ess md iht ihe =>
    rename_i h
    simp only [allStmtTys, Bool.and_eq_true] at h
    simp only [skolemizeStmt_ite, mapStmtTys_ite,
      exprOrNondet_deskolemize_roundtrip nm σ hnd (.det c) h.1.1, iht h.1.2, ihe h.2]
  | case4 tss ess md iht ihe =>
    rename_i h
    simp only [allStmtTys, Bool.and_eq_true] at h
    simp only [skolemizeStmt_ite, mapStmtTys_ite,
      exprOrNondet_deskolemize_roundtrip nm σ hnd .nondet h.1.1, iht h.1.2, ihe h.2]
  | case5 g m i bss md ih =>
    rename_i h
    simp only [allStmtTys, Bool.and_eq_true] at h
    simp only [skolemizeStmt_loop, mapStmtTys_loop,
      exprOrNondet_deskolemize_roundtrip nm σ hnd (.det g) h.1.1.1,
      optExpr_deskolemize_roundtrip nm σ hnd m h.1.1.2,
      labeled_deskolemize_roundtrip nm σ hnd i h.1.2, ih h.2]
  | case6 m i bss md ih =>
    rename_i h
    simp only [allStmtTys, Bool.and_eq_true] at h
    simp only [skolemizeStmt_loop, mapStmtTys_loop,
      exprOrNondet_deskolemize_roundtrip nm σ hnd .nondet h.1.1.1,
      optExpr_deskolemize_roundtrip nm σ hnd m h.1.1.2,
      labeled_deskolemize_roundtrip nm σ hnd i h.1.2, ih h.2]
  | case7 l md => simp only [skolemizeStmt_exit, mapStmtTys_exit]
  | case8 t md => simp only [skolemizeStmt_typeDecl, mapStmtTys_typeDecl]
  | case9 =>
    intro _
    simp only [skolemizeStmts_empty, mapStmtsTys_nil]
  | case10 s rest ihs ihr =>
    intro h
    simp only [allStmtsTys, Bool.and_eq_true] at h
    simp only [skolemizeStmts_cons, mapStmtsTys_cons, ihs h.1, ihr h.2]

/-! ## The skolemizer's output satisfies `annotNoRigidClash` -/

/-- An annotation naming no constant of `σ` satisfies `annotNoRigidClash σ` both skolemized and
    untouched. -/
private theorem annot_noRigidClash (σ : RigidNames) (uty : Option LMonoTy)
    (h : uty.all (mtyAllTyConsNames (notRigidConst σ)) = true) :
    (uty.map (skolemizeTy σ)).all (annotNoRigidClash σ) = true
      ∧ uty.all (annotNoRigidClash σ) = true := by
  cases uty with
  | none => simp
  | some t =>
    simp only [Option.all_some] at h
    refine ⟨?_, ?_⟩
    · simp only [Option.map_some, Option.all_some]
      exact annotNoRigidClash_skolemizeTy σ t
    · simp only [Option.all_some]
      exact annotNoRigidClash_of_notRigidConst t h

/-- Skolemizing an expression turns annotations satisfying `P` into annotations satisfying `Q`,
    if every annotation satisfying `P` satisfies `Q` both skolemized and untouched. -/
private theorem allExprTys_skolemizeBody_of_annot (nm : Option String) (σ : RigidNames)
    (P Q : LMonoTy → Bool)
    (hannot : ∀ uty : Option LMonoTy, uty.all P = true →
      (uty.map (skolemizeTy σ)).all Q = true ∧ uty.all Q = true)
    (e : Expression.Expr) (hP : allExprTys P e = true) :
    allExprTys Q (skolemizeBody nm σ e) = true := by
  rw [allExprTys_eq_allUserProvidedTypes] at hP ⊢
  induction e with
  | const m c => rfl
  | bvar m b => rfl
  | op m o uty =>
    simp only [LExpr.allUserProvidedTypes] at hP
    obtain ⟨hsk, hfix⟩ := hannot uty hP
    simp only [skolemizeBody_op]
    split
    · simp only [LExpr.allUserProvidedTypes]
      exact hsk
    · simp only [LExpr.allUserProvidedTypes]
      exact hfix
  | fvar m x uty =>
    simp only [LExpr.allUserProvidedTypes] at hP
    simp only [skolemizeBody_fvar, LExpr.allUserProvidedTypes]
    exact (hannot uty hP).1
  | abs m n uty b ihb =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hP
    simp only [skolemizeBody_abs, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    exact ⟨(hannot uty hP.1).1, ihb hP.2⟩
  | quant m qk n aty tr b ihtr ihb =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hP
    simp only [skolemizeBody_quant, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    exact ⟨⟨(hannot aty hP.1.1).1, ihtr hP.1.2⟩, ihb hP.2⟩
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hP
    simp only [skolemizeBody_app, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    exact ⟨ih1 hP.1, ih2 hP.2⟩
  | ite m c t fe ihc iht ihf =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hP
    simp only [skolemizeBody_ite, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    exact ⟨⟨ihc hP.1.1, iht hP.1.2⟩, ihf hP.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at hP
    simp only [skolemizeBody_eq, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    exact ⟨ih1 hP.1, ih2 hP.2⟩

/-- Skolemizing an expression whose annotations name no constant of `σ` gives one whose
    annotations all satisfy `annotNoRigidClash σ`. -/
theorem allExprTys_annotNoRigidClash_skolemizeBody (nm : Option String)
    (σ : RigidNames) (e : Expression.Expr)
    (hallowed : allExprTys (mtyAllTyConsNames (notRigidConst σ)) e = true) :
    allExprTys (annotNoRigidClash σ) (skolemizeBody nm σ e) = true :=
  allExprTys_skolemizeBody_of_annot nm σ _ _ (annot_noRigidClash σ) e hallowed

/-- Skolemizing the annotations of an expression keeps the types of its literals fixed by
    deskolemization. -/
theorem ConstTysFixed_skolemizeBody (nm : Option String) {σ : RigidNames}
    {e : Expression.Expr} (h : ConstTysFixed σ e) :
    ConstTysFixed σ (skolemizeBody nm σ e) := by
  intro c hc
  rw [getConsts_skolemizeBody] at hc
  exact h c hc

/-! ### Any annotation condition the skolemizer's output meets -/

/-- An annotation satisfying `P` satisfies `Q` skolemized by `σ` and as written, when `Q` holds
    of every type satisfying `P` in both forms. -/
private theorem annot_of_skolemizeTy (σ : RigidNames) {P : LMonoTy → Bool} (Q : LMonoTy → Bool)
    (hsk : ∀ t, P t = true → Q (skolemizeTy σ t) = true)
    (hfix : ∀ t, P t = true → Q t = true)
    (uty : Option LMonoTy) (h : uty.all P = true) :
    (uty.map (skolemizeTy σ)).all Q = true ∧ uty.all Q = true := by
  cases uty with
  | none => simp
  | some t =>
    simp only [Option.all_some] at h
    simp only [Option.map_some, Option.all_some]
    exact ⟨hsk t h, hfix t h⟩

/-- Skolemizing an expression whose annotations satisfy `P` gives annotations
    satisfying `Q`, when `Q` holds of every type satisfying `P` as written and skolemized. -/
private theorem allExprTys_skolemizeBody_of_skolemizeTy (nm : Option String) (σ : RigidNames)
    {P : LMonoTy → Bool} (Q : LMonoTy → Bool)
    (hsk : ∀ t, P t = true → Q (skolemizeTy σ t) = true)
    (hfix : ∀ t, P t = true → Q t = true)
    (e : Expression.Expr) (h : allExprTys P e = true) :
    allExprTys Q (skolemizeBody nm σ e) = true :=
  allExprTys_skolemizeBody_of_annot nm σ P Q (annot_of_skolemizeTy σ Q hsk hfix) e h

/-- Skolemizing an `ExprOrNondet` whose annotations satisfy `P` gives annotations
    satisfying `Q`, when `Q` holds of every type satisfying `P` as written and skolemized. -/
private theorem allExprOrNondetTys_skolemizeBody_of_skolemizeTy (nm : Option String)
    (σ : RigidNames) {P : LMonoTy → Bool} (Q : LMonoTy → Bool)
    (hsk : ∀ t, P t = true → Q (skolemizeTy σ t) = true)
    (hfix : ∀ t, P t = true → Q t = true)
    (e : ExprOrNondet Expression)
    (h : allExprOrNondetTys P e = true) :
    allExprOrNondetTys Q (e.map (skolemizeBody nm σ ·)) = true := by
  cases e with
  | nondet => rfl
  | det e' =>
    simp only [allExprOrNondetTys] at h ⊢
    exact allExprTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix e' h

/-- Skolemizing an optional expression whose annotations satisfy `P` gives annotations
    satisfying `Q`, when `Q` holds of every type satisfying `P` as written and skolemized. -/
private theorem optExpr_skolemizeBody_of_skolemizeTy (nm : Option String) (σ : RigidNames)
    {P : LMonoTy → Bool} (Q : LMonoTy → Bool)
    (hsk : ∀ t, P t = true → Q (skolemizeTy σ t) = true)
    (hfix : ∀ t, P t = true → Q t = true)
    (m : Option Expression.Expr)
    (h : m.all (allExprTys P) = true) :
    (m.map (skolemizeBody nm σ ·)).all (allExprTys Q) = true := by
  cases m with
  | none => rfl
  | some e =>
    simp only [Option.all_some] at h
    simp only [Option.map_some, Option.all_some]
    exact allExprTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix e h

/-- Skolemizing labeled expressions whose annotations satisfy `P` gives annotations
    satisfying `Q`, when `Q` holds of every type satisfying `P` as written and skolemized. -/
private theorem labeled_skolemizeBody_of_skolemizeTy (nm : Option String) (σ : RigidNames)
    {P : LMonoTy → Bool} (Q : LMonoTy → Bool)
    (hsk : ∀ t, P t = true → Q (skolemizeTy σ t) = true)
    (hfix : ∀ t, P t = true → Q t = true)
    (i : List (String × Expression.Expr))
    (h : i.all (fun (_, e) => allExprTys P e) = true) :
    (i.map (fun (l, e) => (l, skolemizeBody nm σ e))).all
        (fun (_, e) => allExprTys Q e) = true := by
  induction i with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨l, e⟩ := p
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨allExprTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix e h.1, ih h.2⟩

/-- Skolemizing a command whose annotations satisfy `P` gives annotations
    satisfying `Q`, when `Q` holds of every type satisfying `P` as written and skolemized. -/
private theorem allCmdTys_skolemizeCmd_of_skolemizeTy (nm : Option String) (σ : RigidNames)
    {P : LMonoTy → Bool} (Q : LMonoTy → Bool)
    (hsk : ∀ t, P t = true → Q (skolemizeTy σ t) = true)
    (hfix : ∀ t, P t = true → Q t = true)
    (c : Command) (hallowed : allCmdTys P c = true) :
    allCmdTys Q (skolemizeCmd nm σ c) = true := by
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      simp only [allCmdTys, Bool.and_eq_true] at hallowed
      simp only [skolemizeCmd, mapCmdWith, allCmdTys, Bool.and_eq_true]
      refine ⟨?_, allExprOrNondetTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix e hallowed.2⟩
      cases ty with
      | forAll vs mty => exact hsk mty hallowed.1
    | set x e md =>
      simp only [skolemizeCmd, mapCmdWith, allCmdTys] at hallowed ⊢
      exact allExprOrNondetTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix e hallowed
    | assert l b md | assume l b md | cover l b md =>
      simp only [skolemizeCmd, mapCmdWith, allCmdTys] at hallowed ⊢
      exact allExprTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix b hallowed
  | call pname tyArgs args md =>
    simp only [skolemizeCmd, mapCmdWith, allCmdTys, Bool.and_eq_true,
      List.all_eq_true] at hallowed ⊢
    refine ⟨?_, ?_⟩
    · cases tyArgs with
      | none => rfl
      | some tys =>
        have hall := hallowed.1
        simp only [Option.map_some, Option.all_some, List.all_eq_true] at hall ⊢
        intro ty hty
        obtain ⟨ty0, hty0, ty0eq⟩ := List.mem_map.mp hty
        subst ty0eq
        cases ty0 with
        | forAll vs mty => exact hsk mty (hall _ hty0)
    intro a ha
    obtain ⟨a0, ha0, ha0eq⟩ := List.mem_map.mp ha
    have hone := hallowed.2 a0 ha0
    cases a0 with
    | inArg e =>
      simp only [CallArg.mapInput] at hone ha0eq
      subst ha0eq
      simp only
      exact allExprTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix e hone
    | inoutArg id =>
      simp only [CallArg.mapInput] at ha0eq
      subst ha0eq
      rfl
    | outArg id =>
      simp only [CallArg.mapInput] at ha0eq
      subst ha0eq
      rfl

/-- Skolemizing a statement list whose annotations satisfy `P` gives annotations
    satisfying `Q`, when `Q` holds of every type satisfying `P` as written and skolemized. -/
theorem allStmtsTys_skolemizeStmts_of_skolemizeTy (nm : Option String) (σ : RigidNames)
    {P : LMonoTy → Bool} (Q : LMonoTy → Bool)
    (hsk : ∀ t, P t = true → Q (skolemizeTy σ t) = true)
    (hfix : ∀ t, P t = true → Q t = true)
    (ss : List Statement)
    (hallowed : allStmtsTys P ss = true) :
    allStmtsTys Q (skolemizeStmts nm σ ss) = true := by
  revert hallowed
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      allStmtTys P s = true →
        allStmtTys Q (skolemizeStmt nm σ s) = true) with
  | case1 c =>
    rename_i h
    simp only [skolemizeStmt_cmd, allStmtTys] at h ⊢
    exact allCmdTys_skolemizeCmd_of_skolemizeTy nm σ Q hsk hfix c h
  | case2 l bss md ih =>
    rename_i h
    simp only [skolemizeStmt_block, allStmtTys] at h ⊢
    exact ih h
  | case3 c tss ess md iht ihe =>
    rename_i h
    simp only [skolemizeStmt_ite, allStmtTys, Bool.and_eq_true] at h ⊢
    exact ⟨⟨allExprOrNondetTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix (.det c) h.1.1,
      iht h.1.2⟩, ihe h.2⟩
  | case4 tss ess md iht ihe =>
    rename_i h
    simp only [skolemizeStmt_ite, allStmtTys, Bool.and_eq_true] at h ⊢
    exact ⟨⟨allExprOrNondetTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix .nondet h.1.1,
      iht h.1.2⟩, ihe h.2⟩
  | case5 g m i bss md ih =>
    rename_i h
    simp only [skolemizeStmt_loop, allStmtTys, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨allExprOrNondetTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix (.det g) h.1.1.1,
      optExpr_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix m h.1.1.2⟩,
      labeled_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix i h.1.2⟩, ih h.2⟩
  | case6 m i bss md ih =>
    rename_i h
    simp only [skolemizeStmt_loop, allStmtTys, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨allExprOrNondetTys_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix .nondet h.1.1.1,
      optExpr_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix m h.1.1.2⟩,
      labeled_skolemizeBody_of_skolemizeTy nm σ Q hsk hfix i h.1.2⟩, ih h.2⟩
  | case7 l md => simp only [skolemizeStmt_exit, allStmtTys]
  | case8 t md => simp only [skolemizeStmt_typeDecl, allStmtTys]
  | case9 => intro _; simp only [skolemizeStmts_empty, allStmtsTys]
  | case10 s rest ihs ihr =>
    intro h
    simp only [skolemizeStmts_cons, allStmtsTys, Bool.and_eq_true] at h ⊢
    exact ⟨ihs h.1, ihr h.2⟩

/-! ## The skolemizer preserves the syntactic variable and call sets -/

/-- Skolemizing a command's annotations leaves the variables it modifies alone. -/
theorem Command.modifiedVars_skolemizeCmd (nm : Option String) (σ : RigidNames)
    (c : Command) :
    Command.modifiedVars (skolemizeCmd nm σ c) = Command.modifiedVars c :=
  Command.modifiedVars_mapCmdWith _ _ c

/-- Skolemizing a command's annotations leaves the variables it defines alone. -/
theorem Command.definedVars_skolemizeCmd (nm : Option String) (σ : RigidNames)
    (c : Command) :
    Command.definedVars (skolemizeCmd nm σ c) = Command.definedVars c :=
  Command.definedVars_mapCmdWith _ _ c

/-- Skolemizing a statement list's annotations leaves the variables it modifies alone. -/
theorem skolemizeStmts_modifiedVars (nm : Option String) (σ : RigidNames)
    (ss : List Statement) :
    Block.modifiedVars (skolemizeStmts nm σ ss) = Block.modifiedVars ss :=
  Block.modifiedVars_mapExpr_mapCmdWith _ _ ss

/-- Skolemizing a statement list's annotations preserves its defined variables. -/
theorem skolemizeStmts_definedVars (nm : Option String) (σ : RigidNames)
    (ss : List Statement) :
    ∀ b, Block.definedVars (skolemizeStmts nm σ ss) b = Block.definedVars ss b :=
  Block.definedVars_mapExpr_mapCmdWith _ _ ss

/-- Skolemizing a statement list's annotations leaves the procedures it calls alone. -/
theorem skolemizeStmts_calledProcedureNames (nm : Option String) (σ : RigidNames)
    (ss : List Statement) :
    Statements.calledProcedureNames (skolemizeStmts nm σ ss) =
      Statements.calledProcedureNames ss :=
  Block.calledProcedureNames_mapExpr_mapCmdWith _ _ ss

/-! ### Skolemizing does not create a free variable -/

/-- Skolemizing annotations does not turn an expression that is not a free variable into one. -/
theorem skolemizeBody_ne_fvar (selfName : Option String) (σ : RigidNames)
    (e : Expression.Expr) (h : ∀ mid x ann, e ≠ .fvar mid x ann) :
    ∀ mid x ann, skolemizeBody selfName σ e ≠ .fvar mid x ann := by
  intro mid x ann heq
  cases e
  case fvar mid' y ann' => exact h mid' y ann' rfl
  case op =>
    simp only [skolemizeBody_op] at heq
    split at heq <;> simp only [reduceCtorEq] at heq
  case const => simp only [skolemizeBody_const, reduceCtorEq] at heq
  case bvar => simp only [skolemizeBody_bvar, reduceCtorEq] at heq
  case abs => simp only [skolemizeBody_abs, reduceCtorEq] at heq
  case quant => simp only [skolemizeBody_quant, reduceCtorEq] at heq
  case app => simp only [skolemizeBody_app, reduceCtorEq] at heq
  case ite => simp only [skolemizeBody_ite, reduceCtorEq] at heq
  case eq => simp only [skolemizeBody_eq, reduceCtorEq] at heq

/-! ### The deskolemized ambient scope -/

/-- `Γ` with its types alias-resolved, substituted by `S` and then deskolemized. -/
def substDeskolemizedAmbient (σ : RigidNames) (S : Subst) (Γ : TContext Unit) :
    TContext Unit :=
  { Γ with types :=
      HMaps.mapValues (mapLTyTys (deskolemizeTy σ)) (TContext.subst Γ.dealias S).types }

/-- Lookup in the deskolemized ambient scope maps the original scheme through alias resolution,
    substitution and deskolemization. -/
theorem substDeskolemizedAmbient_find? (σ : RigidNames) (S : Subst) (Γ : TContext Unit)
    (x : Expression.Ident) :
    (substDeskolemizedAmbient σ S Γ).types.find? x
      = ((Γ.types.find? x).map (fun t => LTy.subst S (Γ.resolveScheme t))).map
          (mapLTyTys (deskolemizeTy σ)) := by
  show HMaps.find?
      (HMaps.mapValues (mapLTyTys (deskolemizeTy σ)) (TContext.subst Γ.dealias S).types) x = _
  rw [HMaps.find?_mapValues, TContext.subst_dealias_find?]

/-! ### Annotations of a skolemized expression -/

/-- `skolemizeBody` skolemizes each binder annotation. -/
private theorem binderAnnotations_skolemizeBody (nm : Option String) (σ : RigidNames) :
    ∀ e : Expression.Expr, LExpr.binderAnnotations (skolemizeBody nm σ e) =
      (LExpr.binderAnnotations e).map (skolemizeTy σ) := by
  intro e
  induction e <;> simp_all [skolemizeBody, LExpr.replaceUserProvidedType,
    LExpr.binderAnnotations, Option.toList_map, apply_ite]

/-- `skolemizeBody` skolemizes each free-variable annotation. -/
theorem fvarAnnotations_skolemizeBody (nm : Option String) (σ : RigidNames) :
    ∀ e : Expression.Expr, LExpr.fvarAnnotations (skolemizeBody nm σ e) =
      (LExpr.fvarAnnotations e).map (skolemizeTy σ) := by
  intro e
  induction e <;> simp_all [skolemizeBody, LExpr.replaceUserProvidedType,
    LExpr.fvarAnnotations, Option.toList_map, apply_ite]

/-- After skolemizing, an expression's free-variable and binder annotations avoid `ps` when every
    variable of the written annotations is outside `ps` or renamed by `σ`. -/
theorem annotsAvoid_skolemizeBody {ps : List TyIdentifier} (nm : Option String) (σ : RigidNames)
    (e : Expression.Expr)
    (h : ∀ t ∈ LExpr.fvarAnnotations e ++ LExpr.binderAnnotations e,
      ∀ v ∈ LMonoTy.freeVars t, v ∉ ps ∨ v ∈ σ.map Prod.fst) :
    LExpr.AnnotsAvoid (skolemizeBody nm σ e) ps := by
  intro t ht v hv
  rw [fvarAnnotations_skolemizeBody, binderAnnotations_skolemizeBody, ← List.map_append,
    List.mem_map] at ht
  obtain ⟨t0, ht0, rfl⟩ := ht
  obtain ⟨hv0, hvσ⟩ := LMonoTy.mem_freeVars_skolemizeTy σ t0 v hv
  exact (h t0 ht0 v hv0).resolve_right hvσ

end Core

end -- public section
