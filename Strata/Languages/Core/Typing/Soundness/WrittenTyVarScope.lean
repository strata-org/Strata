/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Soundness.Command
public import Strata.Languages.Core.WrittenTyVarScope
public import Strata.Languages.Core.Typing.Props.WrittenTyVarScopeProps
public import Strata.DL.Lambda.LExprTypeSpecProps
import all Strata.Languages.Core.Typing.Soundness.Command
import all Strata.Languages.Core.Typing.Props.WrittenTyVarScopeProps
import Strata.Languages.Core.Typing.Props.TypeSkolemProps
import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Languages.Core.StatementType
import Strata.Languages.Core.Statement
import Strata.DL.Imperative.Cmd
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExpr
import Strata.Util.Tactics
import Strata.DL.Lambda.LTyUnify
import Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.LExprTypeEnv
import Strata.Languages.Core.Typing.Spec.CmdTypeSpec

/-! ## Commands typed by the typechecker spec after scoping their written type variables
A typing of a command with its written type variables renamed to checker names gives a typing
of the written command, each written type variable denoting the `S`-instance of its checker name.

Key theorems: `TypeSpec.CmdExtHasType.of_rename` (the typing transfer),
`TypeSpec.CmdExtHasType.rename_scopeAdmissible` (renaming keeps the scope admissible),
`renameCmd_varsAvoid` and `TypeSpec.WrittenEnv.Tracks.noParam` (renamed commands and tracked
environments avoid the type parameters). -/

public section

namespace Core

open Lambda Imperative
open TypeSpec
open WrittenTyVarScope

/-! ### Renaming the annotations of an expression -/

/-- An annotation's checker name is a name a user may write only if the written name is. -/
private theorem annotName_admissible (m : ScopeMap) (v : TyIdentifier)
    (h : TyVarAdmissibility.notGeneratedOrRigid (annotName m v) = true) :
    TyVarAdmissibility.notGeneratedOrRigid v = true := by
  unfold annotName at h
  by_cases hv : TyVarAdmissibility.notGeneratedOrRigid v = true
  · exact hv
  · rw [ite_eq_right hv] at h
    exact h

/-- A renamed annotation is an instance of the written one. -/
private theorem annotInstantiates_renameAnnot (m : ScopeMap) (a : Option LMonoTy) :
    AnnotInstantiates (renameAnnot m a) a := by
  cases a with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some t => exact Or.inr ⟨t, restrictTo (fun v => .ftvar (annotName m v)) t, rfl, rfl⟩

/-- The annotations of a renamed optional annotation are the renamings of the written ones. -/
private theorem toList_renameAnnot (m : ScopeMap) (a : Option LMonoTy) :
    (renameAnnot m a).toList = a.toList.map (renameTy (annotName m)) := by
  cases a <;> rfl

/-- Renaming an expression's annotations rewrites each free-variable annotation to an instance of
    it, keeps the free variables, and renames every free-variable and binder annotation. -/
private theorem renameExpr_facts (m : ScopeMap) :
    ∀ e : Expression.Expr,
      AnnotInstRewrite (renameExpr m e) e ∧
      Lambda.LExpr.LExpr.getVars (renameExpr m e) = Lambda.LExpr.LExpr.getVars e ∧
      LExpr.fvarAnnotations (renameExpr m e) =
        (LExpr.fvarAnnotations e).map (renameTy (annotName m)) ∧
      LExpr.binderAnnotations (renameExpr m e) =
        (LExpr.binderAnnotations e).map (renameTy (annotName m)) := by
  intro e
  induction e with
  | const md c => exact ⟨.const md c, rfl, rfl, rfl⟩
  | op md o ty => exact ⟨.op md o ty, rfl, rfl, rfl⟩
  | bvar md i => exact ⟨.bvar md i, rfl, rfl, rfl⟩
  | fvar md x ty =>
    exact ⟨.fvar md x (annotInstantiates_renameAnnot m ty), rfl, toList_renameAnnot m ty, rfl⟩
  | abs md name ty b ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨.abs md name (annotInstantiates_renameAnnot m ty) h1, ?_, ?_, ?_⟩
    · simp only [renameExpr_abs, Lambda.LExpr.LExpr.getVars, h2]
    · simp only [renameExpr_abs, LExpr.fvarAnnotations, h3]
    · simp only [renameExpr_abs, LExpr.binderAnnotations, h4, toList_renameAnnot, List.map_append]
  | quant md k name ty tr b ihtr ihb =>
    obtain ⟨t1, t2, t3, t4⟩ := ihtr
    obtain ⟨b1, b2, b3, b4⟩ := ihb
    refine ⟨.quant md k name (annotInstantiates_renameAnnot m ty) t1 b1, ?_, ?_, ?_⟩
    · simp only [renameExpr_quant, Lambda.LExpr.LExpr.getVars, t2, b2]
    · simp only [renameExpr_quant, LExpr.fvarAnnotations, t3, b3, List.map_append]
    · simp only [renameExpr_quant, LExpr.binderAnnotations, t4, b4, toList_renameAnnot,
        List.map_append]
  | app md f a ihf iha =>
    obtain ⟨f1, f2, f3, f4⟩ := ihf
    obtain ⟨a1, a2, a3, a4⟩ := iha
    refine ⟨.app md f1 a1, ?_, ?_, ?_⟩
    · simp only [renameExpr_app, Lambda.LExpr.LExpr.getVars, f2, a2]
    · simp only [renameExpr_app, LExpr.fvarAnnotations, f3, a3, List.map_append]
    · simp only [renameExpr_app, LExpr.binderAnnotations, f4, a4, List.map_append]
  | ite md c t e ihc iht ihe =>
    obtain ⟨c1, c2, c3, c4⟩ := ihc
    obtain ⟨t1, t2, t3, t4⟩ := iht
    obtain ⟨e1, e2, e3, e4⟩ := ihe
    refine ⟨.ite md c1 t1 e1, ?_, ?_, ?_⟩
    · simp only [renameExpr_ite, Lambda.LExpr.LExpr.getVars, c2, t2, e2]
    · simp only [renameExpr_ite, LExpr.fvarAnnotations, c3, t3, e3, List.map_append]
    · simp only [renameExpr_ite, LExpr.binderAnnotations, c4, t4, e4, List.map_append]
  | eq md a b iha ihb =>
    obtain ⟨a1, a2, a3, a4⟩ := iha
    obtain ⟨b1, b2, b3, b4⟩ := ihb
    refine ⟨.eq md a1 b1, ?_, ?_, ?_⟩
    · simp only [renameExpr_eq, Lambda.LExpr.LExpr.getVars, a2, b2]
    · simp only [renameExpr_eq, LExpr.fvarAnnotations, a3, b3, List.map_append]
    · simp only [renameExpr_eq, LExpr.binderAnnotations, a4, b4, List.map_append]

/-- In the typechecker spec, an expression meets the written-annotation requirement whenever its
    annotation renaming does. -/
theorem writtenAnnotsOk_of_renameExpr {C : LContext CoreLParams} {Γ : TContext Unit}
    (m : ScopeMap) (e : Expression.Expr)
    (h : WrittenAnnotsOk C Γ (renameExpr m e)) :
    WrittenAnnotsOk C Γ e := by
  obtain ⟨-, -, hfv, hbind⟩ := renameExpr_facts m e
  obtain ⟨hfa, hba⟩ := h
  refine ⟨?_, ?_⟩
  · intro t ht
    have hmem : renameTy (annotName m) t ∈ LExpr.fvarAnnotations (renameExpr m e) := by
      rw [hfv]
      exact List.mem_map_of_mem ht
    obtain ⟨r', hr'⟩ := hfa _ hmem
    refine SourceTyWF.of_renaming [restrictTo (fun v => .ftvar (annotName m v)) t] ?_ hr'
    intro v hv
    exact Or.inr ⟨annotName m v, restrictTo_ftvar _ t v hv, annotName_admissible m v⟩
  · intro t ht v hv
    have hmem : renameTy (annotName m) t ∈ LExpr.binderAnnotations (renameExpr m e) := by
      rw [hbind]
      exact List.mem_map_of_mem ht
    exact annotName_admissible m v (hba _ hmem _ (mem_freeVars_renameTy _ t v hv))

/-- Renaming the annotations of an expression keeps its free term variables. -/
private theorem getFvars_renameExpr (m : ScopeMap) (e : Expression.Expr) :
    HasFvars.getFvars (P := Expression) (renameExpr m e) =
      HasFvars.getFvars (P := Expression) e :=
  (renameExpr_facts m e).2.1

/-! ### Renaming call arguments and commands -/

/-- Renaming a call's arguments keeps the variables it assigns. -/
private theorem getLhs_renameCallArgs (m : ScopeMap) :
    ∀ args : List (CallArg Expression),
      CallArg.getLhs (renameCallArgs m args) = CallArg.getLhs args :=
  CallArg.getLhs_map_congr (renameExpr m)

/-- Renaming a call's arguments renames the annotations of its input expressions. -/
private theorem getInputExprs_renameCallArgs (m : ScopeMap) :
    ∀ args : List (CallArg Expression),
      CallArg.getInputExprs (renameCallArgs m args) =
        (CallArg.getInputExprs args).map (renameExpr m)
  | [] => rfl
  | .inArg e :: args => by
    simp only [renameCallArgs, CallArg.mapInput, CallArg.getInputExprs, Calls.getInputExprs,
      List.filterMap_cons, List.map_cons, List.cons.injEq, true_and]
    exact getInputExprs_renameCallArgs m args
  | .inoutArg id :: args => by
    simp only [renameCallArgs, CallArg.mapInput, CallArg.getInputExprs, Calls.getInputExprs,
      List.filterMap_cons, List.map_cons, List.cons.injEq]
    exact ⟨rfl, getInputExprs_renameCallArgs m args⟩
  | .outArg id :: args => by
    simp only [renameCallArgs, List.map_cons, CallArg.mapInput, CallArg.getInputExprs,
      Calls.getInputExprs, List.filterMap_cons]
    exact getInputExprs_renameCallArgs m args

/-- Renaming a command keeps the procedures it calls. -/
theorem calledProcedureNames_renameCmd (rigid : List TyIdentifier) (m : ScopeMap)
    (st : ScopeState) (c : Command) :
    CmdExt.calledProcedureNames (renameCmd rigid m st c).1 = CmdExt.calledProcedureNames c := by
  cases c with
  | call => rfl
  | cmd cc =>
    cases cc with
    | init _ xty _ _ =>
      obtain ⟨vars, ty⟩ := xty
      cases vars <;> rfl
    | set | assert | assume | cover => rfl

/-- Renaming the annotations of an expression keeps its literals. -/
theorem getConsts_renameExpr (m : ScopeMap) (e : Expression.Expr) :
    LExpr.getConsts (renameExpr m e) = LExpr.getConsts e := by
  induction e with
  | const | op | bvar | fvar => rfl
  | abs _ _ _ _ ih =>
    simp only [renameExpr_abs, LExpr.getConsts]
    exact ih
  | quant _ _ _ _ _ _ ihtr ihb =>
    simp only [renameExpr_quant, LExpr.getConsts]
    rw [ihtr, ihb]
  | app _ _ _ ihf iha =>
    simp only [renameExpr_app, LExpr.getConsts]
    rw [ihf, iha]
  | ite _ _ _ _ ihc iht ihe =>
    simp only [renameExpr_ite, LExpr.getConsts]
    rw [ihc, iht, ihe]
  | eq _ _ _ iha ihb =>
    simp only [renameExpr_eq, LExpr.getConsts]
    rw [iha, ihb]

/-- Renaming the annotations of an expression keeps the type names of its literals. -/
theorem exprLitTyNames_renameExpr (m : ScopeMap) (e : Expression.Expr) :
    exprLitTyNames (renameExpr m e) = exprLitTyNames e := by
  unfold exprLitTyNames
  rw [getConsts_renameExpr]

/-- Renaming a command keeps the type names of the literals of the expressions it reads. -/
theorem litTyNames_renameCmd (rigid : List TyIdentifier) (m : ScopeMap)
    (st : ScopeState) (c : Command) :
    (Statement.cmdExprs (renameCmd rigid m st c).1).flatMap exprLitTyNames =
      (Statement.cmdExprs c).flatMap exprLitTyNames := by
  have hopt : ∀ (m' : ScopeMap) (e : ExprOrNondet Expression),
      (renameExprOrNondet m' e).toList.flatMap exprLitTyNames =
        e.toList.flatMap exprLitTyNames := by
    intro m' e
    cases e <;> simp only [renameExprOrNondet, ExprOrNondet.map, ExprOrNondet.toList,
      List.flatMap_cons, List.flatMap_nil, exprLitTyNames_renameExpr]
  cases c with
  | cmd cc =>
    cases cc with
    | init _ xty e _ =>
      obtain ⟨vars, ty⟩ := xty
      cases vars with
      | nil =>
        simp only [renameCmd, Statement.cmdExprs, Cmd.readExprs]
        exact hopt _ e
      | cons _ _ => rfl
    | set _ e _ =>
      simp only [renameCmd, Statement.cmdExprs, Cmd.readExprs]
      exact hopt _ e
    | assert _ e _ | assume _ e _ | cover _ e _ =>
      simp only [renameCmd, Statement.cmdExprs, Cmd.readExprs, List.flatMap_cons,
        List.flatMap_nil, exprLitTyNames_renameExpr]
  | call _ _ args _ =>
    simp only [renameCmd, renameCallArgs, Statement.cmdExprs]
    induction args with
    | nil => rfl
    | cons a rest ih =>
      cases a <;> simp only [List.map_cons, CallArg.mapInput, CallArg.getInputExprs,
        Calls.getInputExprs, List.filterMap_cons, List.flatMap_cons,
        exprLitTyNames_renameExpr] at ih ⊢ <;>
        simp only [ih]

/-- Renaming a command keeps the variables it modifies. -/
theorem Command.modifiedVars_renameCmd (rigid : List TyIdentifier)
    (m : ScopeMap) (st : ScopeState) (c : Command) :
    Command.modifiedVars (renameCmd rigid m st c).1 = Command.modifiedVars c := by
  cases c with
  | cmd cc =>
    cases cc with
    | init _ xty _ _ =>
      obtain ⟨vars, ty⟩ := xty
      cases vars <;> rfl
    | set | assert | assume | cover => rfl
  | call _ _ args _ =>
    simp only [renameCmd, Command.modifiedVars]
    exact getLhs_renameCallArgs m args

/-- Renaming a command keeps the variables it defines. -/
theorem Command.definedVars_renameCmd (rigid : List TyIdentifier)
    (m : ScopeMap) (st : ScopeState) (c : Command) :
    Command.definedVars (renameCmd rigid m st c).1 = Command.definedVars c := by
  cases c with
  | cmd cc =>
    cases cc with
    | init _ xty _ _ =>
      obtain ⟨vars, ty⟩ := xty
      cases vars <;> rfl
    | set | assert | assume | cover => rfl
  | call => rfl

/-! ### Environments that a scope map tracks -/

/-- `Δ` binds exactly the names `m` binds, each to the `S`-instance of its checker name; `m` binds
    no rigid name and maps each name a user may write to such a name. -/
structure TypeSpec.WrittenEnv.Tracks (S : Subst) (rigid : List TyIdentifier) (m : ScopeMap)
    (Δ : WrittenEnv) : Prop where
  noRigid : ∀ r ∈ rigid, m.lookup r = none
  sound : ∀ v t, Δ v = some t → ∃ w, m.lookup v = some w ∧ t = LMonoTy.subst S (.ftvar w)
  complete : ∀ v w, m.lookup v = some w → (Δ v).isSome
  admissible : ∀ v w, m.lookup v = some w → TyVarAdmissibility.notGeneratedOrRigid v = true →
    TyVarAdmissibility.notGeneratedOrRigid w = true

/-- The empty scope map tracks the empty environment. -/
theorem TypeSpec.WrittenEnv.Tracks.empty (S : Subst) (rigid : List TyIdentifier) :
    WrittenEnv.Tracks S rigid [] (fun _ => none) where
  noRigid := fun _ _ => rfl
  sound := fun _ _ h => by cases h
  complete := fun _ _ h => by cases h
  admissible := fun _ _ h => by cases h

/-! ### Reading renamed annotations -/

/-- Reading an annotation's renaming through the `S`-instances of every name equals reading the
    annotation through an environment the scope map tracks, when each of its type variables is
    rigid or bound there and `S` fixes the rigid names. -/
private theorem instAnnotTy_substEnv_renameTy {S : Subst} {rigid : List TyIdentifier} {m : ScopeMap}
    {Δ : WrittenEnv} (htr : WrittenEnv.Tracks S rigid m Δ)
    (hfix : ∀ v ∈ rigid, LMonoTy.subst S (.ftvar v) = .ftvar v) (t : LMonoTy)
    (ht : ∀ v ∈ LMonoTy.freeVars t, v ∈ rigid ∨ (Δ v).isSome) :
    instAnnotTy (substEnv S) (renameTy (annotName m) t) = instAnnotTy Δ t := by
  show LMonoTy.subst [restrictTo (readTyVar (substEnv S)) (renameTy (annotName m) t)]
      (renameTy (annotName m) t) = LMonoTy.subst [restrictTo (readTyVar Δ) t] t
  rw [← subst_restrictTo_renameTy]
  refine subst_restrictTo_congr _ _ t ?_
  intro v hv
  rw [restrictTo_ftvar (readTyVar (substEnv S)) _ (annotName m v)
    (mem_freeVars_renameTy _ t v hv)]
  by_cases hadm : TyVarAdmissibility.notGeneratedOrRigid v = true
  · have hf : annotName m v = checkerName m v := by
      simp only [annotName, hadm, ite_true]
    cases hl : m.lookup v with
    | some w =>
      have hcw : checkerName m v = w := by
        simp only [checkerName, hl, Option.getD_some]
      have hadmw := htr.admissible v w hl hadm
      obtain ⟨t', hΔ⟩ := Option.isSome_iff_exists.mp (htr.complete v w hl)
      obtain ⟨w', hw', ht'⟩ := htr.sound v t' hΔ
      rw [hl, Option.some.injEq] at hw'
      subst hw'
      simp only [readTyVar, hf, hcw, hadmw, hadm, ite_true, substEnv, Option.getD_some, hΔ, ht']
    | none =>
      have hΔ : Δ v = none := by
        cases hΔ : Δ v with
        | none => rfl
        | some t' =>
          obtain ⟨w, hw, -⟩ := htr.sound v t' hΔ
          rw [hl] at hw
          cases hw
      have hr : v ∈ rigid := by
        rcases ht v hv with hr | hs
        · exact hr
        · rw [hΔ] at hs
          cases hs
      have hcv : checkerName m v = v := by
        simp only [checkerName, hl, Option.getD_none]
      simp only [readTyVar, hf, hcv, hadm, ite_true, substEnv, Option.getD_some, hΔ,
        Option.getD_none, hfix v hr]
  · have hadm' : TyVarAdmissibility.notGeneratedOrRigid v = false := Bool.eq_false_iff.mpr hadm
    have hf : annotName m v = v := by
      simp only [annotName, hadm', Bool.false_eq_true, ↓reduceIte]
    simp only [readTyVar, hf, hadm', Bool.false_eq_true, ↓reduceIte]

/-- Reading an expression's annotation renaming through `Δ₁` equals reading the expression
    through `Δ₂` when this holds for each of its free-variable and binder annotations. -/
private theorem instAnnots_renameExpr_eq (m : ScopeMap) (Δ₁ Δ₂ : WrittenEnv) :
    ∀ e : Expression.Expr,
      (∀ t ∈ LExpr.fvarAnnotations e ++ LExpr.binderAnnotations e,
        instAnnotTy Δ₁ (renameTy (annotName m) t) = instAnnotTy Δ₂ t) →
      instAnnots Δ₁ (renameExpr m e) = instAnnots Δ₂ e := by
  have hopt : ∀ (ty : Option LMonoTy),
      (∀ t ∈ ty.toList, instAnnotTy Δ₁ (renameTy (annotName m) t) = instAnnotTy Δ₂ t) →
      (renameAnnot m ty).map (instAnnotTy Δ₁) = ty.map (instAnnotTy Δ₂) := by
    intro ty hty
    cases ty with
    | none => rfl
    | some t =>
      simp only [renameAnnot, Option.map_some, Option.some.injEq]
      exact hty t (List.mem_singleton.mpr rfl)
  intro e
  induction e
  case const | op | bvar => intro _; rfl
  case' fvar md x ty =>
    intro h
    simp only [renameExpr_fvar, instAnnots]
    rw [hopt ty ?_]
  case' abs md n ty b ih =>
    intro h
    simp only [renameExpr_abs, instAnnots]
    rw [hopt ty ?_, ih ?_]
  case' quant md k n ty tr b iht ihb =>
    intro h
    simp only [renameExpr_quant, instAnnots]
    rw [hopt ty ?_, iht ?_, ihb ?_]
  case' app md f a ihf iha =>
    intro h
    simp only [renameExpr_app, instAnnots]
    rw [ihf ?_, iha ?_]
  case' ite md c t f ihc iht ihf =>
    intro h
    simp only [renameExpr_ite, instAnnots]
    rw [ihc ?_, iht ?_, ihf ?_]
  case' eq md a b iha ihb =>
    intro h
    simp only [renameExpr_eq, instAnnots]
    rw [iha ?_, ihb ?_]
  -- Each remaining goal restricts `h` to the annotations of the node or a direct subterm.
  all_goals
    intro u hu
    apply h u
    simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at hu ⊢
    grind

/-- Reading an in-scope expression's annotation renaming through the `S`-instances of every name
    equals reading it through an environment the scope map tracks when `S` fixes the rigid names. -/
theorem instAnnots_substEnv_renameExpr {S : Subst} {rigid : List TyIdentifier} {m : ScopeMap}
    {Δ : WrittenEnv} (htr : WrittenEnv.Tracks S rigid m Δ)
    (hfix : ∀ v ∈ rigid, LMonoTy.subst S (.ftvar v) = .ftvar v) (e : Expression.Expr)
    (hscope : AnnotsInScope rigid Δ e) :
    instAnnots (substEnv S) (renameExpr m e) = instAnnots Δ e :=
  instAnnots_renameExpr_eq m _ _ e (fun t ht =>
    instAnnotTy_substEnv_renameTy htr hfix t (fun v hv => hscope t ht v hv))

/-! ### Annotation scope and calls with renamed arguments -/

/-- The checker's scope test on an expression gives `AnnotsInScope` in every environment that binds
    each name the scope map binds. -/
theorem annotsInScope_of_unboundAnnotVar? {rigid : List TyIdentifier} {m : ScopeMap}
    {Δ : WrittenEnv} (hcomplete : ∀ v w, m.lookup v = some w → (Δ v).isSome)
    {e : Expression.Expr} (h : unboundAnnotVar? false rigid m e = none) :
    AnnotsInScope rigid Δ e := by
  intro t ht v hv
  have hmem : v ∈ exprTyVars e := List.mem_flatMap.mpr ⟨t, ht, hv⟩
  have hnot := List.find?_eq_none.mp h v hmem
  by_cases hr : v ∈ rigid
  · exact Or.inl hr
  · right
    cases hl : m.lookup v with
    | none =>
      exfalso
      apply hnot
      simp [hl, hr]
    | some w => exact hcomplete v w hl

/-! ### From an exact typing of a renamed command to a scoped typing of the written one -/

/-- If a declaration is scoped at its renamed type through the `S`-instances of every name, then
    it is scoped at the written type through any environment the scope map tracks, and binding
    the declared type's variables extends the tracked environment accordingly. -/
private theorem scopedAnnotInst_of_exact {aliases : List TypeAlias} {rigid : List TyIdentifier}
    {S : Subst} {Δ : WrittenEnv} {σ : SubstOne} {m : ScopeMap} {st : ScopeState}
    {ty mty : LMonoTy}
    (hfix : ∀ v ∈ rigid, LMonoTy.subst S (.ftvar v) = .ftvar v)
    (htr : WrittenEnv.Tracks S rigid m Δ)
    (hexact : ScopedAnnotInst aliases rigid (substEnv S) σ
      (renameTy (checkerName (bindVars rigid (LMonoTy.freeVars ty) m st).1) ty) mty) :
    ScopedAnnotInst aliases rigid Δ
        (restrictTo (fun v => LMonoTy.subst S
          (.ftvar (checkerName (bindVars rigid (LMonoTy.freeVars ty) m st).1 v))) ty) ty mty ∧
      WrittenEnv.Tracks S rigid (bindVars rigid (LMonoTy.freeVars ty) m st).1
        (Δ.bindFirst rigid ty (restrictTo (fun v => LMonoTy.subst S
          (.ftvar (checkerName (bindVars rigid (LMonoTy.freeVars ty) m st).1 v))) ty)) := by
  obtain ⟨-, hid, hae⟩ := hexact
  have hsubst : LMonoTy.subst [σ]
      (renameTy (checkerName (bindVars rigid (LMonoTy.freeVars ty) m st).1) ty) =
      LMonoTy.subst S
        (renameTy (checkerName (bindVars rigid (LMonoTy.freeVars ty) m st).1) ty) := by
    apply agree_on_freeVars_implies_subst_eq
    intro v hv
    exact hid v hv _ rfl
  rw [hsubst] at hae
  have hnor := bindVars_noRigid rigid (LMonoTy.freeVars ty) m st htr.1
  have hnameRigid : ∀ v ∈ rigid,
      checkerName (bindVars rigid (LMonoTy.freeVars ty) m st).1 v = v := by
    intro v hv
    simp only [checkerName, hnor v hv, Option.getD_none]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hnor, ?_, ?_, bindVars_admissible rigid _ m st htr.admissible⟩⟩
  · intro v hv
    by_cases hvm : v ∈ LMonoTy.freeVars ty
    · rw [restrictTo_ftvar _ ty v hvm, hnameRigid v hv]
      exact hfix v hv
    · exact restrictTo_ftvar_of_not_mem _ ty v hvm
  · intro v hv t hΔ
    obtain ⟨w, hmw, rfl⟩ := htr.2 v t hΔ
    rw [restrictTo_ftvar _ ty v hv]
    simp only [checkerName, bindVars_mono rigid _ m st v w hmw, Option.getD_some]
  · rw [subst_restrictTo_renameTy]
    exact hae
  · intro v t hΔ'
    simp only [WrittenEnv.bindFirst] at hΔ'
    split at hΔ'
    · rename_i t₀ hΔv
      cases hΔ'
      obtain ⟨w, hmw, rfl⟩ := htr.2 v t hΔv
      exact ⟨w, bindVars_mono rigid _ m st v w hmw, rfl⟩
    · split at hΔ'
      · rename_i hcond
        cases hΔ'
        obtain ⟨w, hw⟩ := bindVars_binds rigid _ m st v hcond.1 hcond.2
        refine ⟨w, hw, ?_⟩
        rw [restrictTo_ftvar _ ty v hcond.1]
        simp only [checkerName, hw, Option.getD_some]
      · cases hΔ'
  · intro v w hvw
    simp only [WrittenEnv.bindFirst]
    rcases bindVars_lookup_cases rigid _ m st v w hvw with hold | ⟨hmem, hnr, -⟩
    · have hsome := htr.3 v w hold
      cases hΔv : Δ v with
      | some t => rfl
      | none => simp [hΔv] at hsome
    · cases hΔv : Δ v with
      | some t => rfl
      | none => simp [hmem, hnr]

/-- A valid declared type has only type variables a user may write, when the aliases are
    well-formed. -/
private theorem ValidDeclaredTy.freeVars_admissible {C : LContext CoreLParams}
    {aliases : List TypeAlias} {t : LMonoTy} (hwf : ∀ a ∈ aliases, TypeAlias.WF a)
    (h : ValidDeclaredTy C aliases t) :
    ∀ v ∈ LMonoTy.freeVars t, TyVarAdmissibility.notGeneratedOrRigid v = true := by
  obtain ⟨r, hres, hty⟩ := h
  intro v hv
  exact hty.admissible v ((AliasEquiv.freeVars_iff hwf hres.aliasEquiv v).mp hv)

/-- A type is a valid declared type whenever its renaming is, when its type variables are
    all names a user may write. -/
private theorem ValidDeclaredTy.of_renameTy {C : LContext CoreLParams} {aliases : List TypeAlias}
    (f : TyIdentifier → TyIdentifier) {t : LMonoTy}
    (hadm : ∀ v ∈ LMonoTy.freeVars t, TyVarAdmissibility.notGeneratedOrRigid v = true)
    (h : ValidDeclaredTy C aliases (renameTy f t)) : ValidDeclaredTy C aliases t := by
  obtain ⟨r, hr⟩ := h
  exact SourceTyWF.of_renaming
    [LExpr.buildSubstFromFunction (LMonoTy.freeVars t) (fun v => .ftvar (f v))]
    (fun v hv => Or.inl (hadm v hv)) hr

/-- If a renamed command has a typing, then renaming keeps the scope admissible, and the type
    variables of the command's declared type, if any, are names a user may write. -/
theorem TypeSpec.CmdExtHasType.rename_scopeAdmissible {C : LContext CoreLParams} {P : Program}
    {Γ Γ' : TContext Unit} {Δ Δ' : WrittenEnv} (rigid : List TyIdentifier) (m : ScopeMap)
    (st : ScopeState) (c : Command) (hwf : ∀ a ∈ Γ.aliases, TypeAlias.WF a)
    (hinv : ScopeAdmissible rigid m st)
    (h : CmdExtHasType C P Δ Γ (renameCmd rigid m st c).1 Γ' Δ') :
    ScopeAdmissible rigid (renameCmd rigid m st c).2.1 (renameCmd rigid m st c).2.2 ∧
      ∀ x ty e md, c = .cmd (.init x (.forAll [] ty) e md) →
        ∀ v ∈ LMonoTy.freeVars ty, TyVarAdmissibility.notGeneratedOrRigid v = true := by
  refine renameCmd_scopeAdmissible rigid m st c hinv ?_
  intro x ty e md hc
  subst hc
  cases e with
  | det e =>
    simp only [renameCmd, renameExprOrNondet, ExprOrNondet.map] at h
    cases h with
    | cmd _ _ _ hcmd =>
      cases hcmd with
      | init_det _ _ _ _ _ _ _ _ _ _ hxty hdecl _ _ _ _ _ =>
        cases hxty
        exact ValidDeclaredTy.freeVars_admissible hwf hdecl.2
  | nondet =>
    simp only [renameCmd, renameExprOrNondet, ExprOrNondet.map] at h
    cases h with
    | cmd _ _ _ hcmd =>
      cases hcmd with
      | init_nondet _ _ _ _ _ _ _ _ hxty hdecl _ _ =>
        cases hxty
        exact ValidDeclaredTy.freeVars_admissible hwf hdecl.2

/-- A typing of a renamed call read through the `S`-instances of every name gives a typing of the
    written call from any environment the scope map tracks, ending in that same environment. -/
private theorem TypeSpec.CmdExtHasType.of_rename_call {C : LContext CoreLParams} {P : Program}
    {Γ Γ' : TContext Unit} {Δ₀' : WrittenEnv} (S : Subst)
    (hfix : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v)
    (m : ScopeMap) (pname : String) (tyArgs : Option (List Expression.Ty))
    (args : List (CallArg Expression)) (md : MetaData Expression)
    (h : CmdExtHasType C P (substEnv S) Γ (.call pname tyArgs (renameCallArgs m args) md) Γ' Δ₀')
    (hin : ∀ e ∈ CallArg.getInputExprs args, unboundAnnotVar? false C.rigidTypeVars m e = none) :
    Δ₀' = substEnv S ∧ ∀ Δ, WrittenEnv.Tracks S C.rigidTypeVars m Δ →
      ∃ Δ', WrittenEnv.Tracks S C.rigidTypeVars m Δ' ∧
        CmdExtHasType C P Δ Γ (.call pname tyArgs args md) Γ' Δ' := by
  match h with
  | .call _ _ _ _ _ proc _ σ _ hfind hcall hlhsSome hinTy hinAnn _ houtTy heqv =>
    refine ⟨rfl, fun Δ htr => ?_⟩
    have hscope : ∀ e ∈ CallArg.getInputExprs args, AnnotsInScope C.rigidTypeVars Δ e := by
      intro e he
      exact annotsInScope_of_unboundAnnotVar? htr.3 (hin e he)
    have hinE := getInputExprs_renameCallArgs m args
    have hlhs := getLhs_renameCallArgs m args
    rw [hlhs] at hlhsSome houtTy
    have hshape := (CallArg.map_mapInput_const (renameExpr m) (.boolConst Core.valueLoc true)
                    args).symm
    refine ⟨Δ, htr, .call _ _ _ _ _ proc _ σ _ hfind
      (hcall.transfer (.boolConst Core.valueLoc true) hfind hfind rfl rfl hshape) hlhsSome
      ?_ ?_ hscope houtTy heqv⟩
    · intro i hi hj
      have hi' : i < (CallArg.getInputExprs (renameCallArgs m args)).length := by
        rw [hinE, List.length_map]
        exact hi
      obtain ⟨mty, hae, hmatch⟩ := hinTy i hi' hj
      refine ⟨mty, hae, ?_⟩
      simp only [hinE, List.getElem_map] at hmatch
      have hsc := hscope _ (List.getElem_mem hi)
      generalize (CallArg.getInputExprs args)[i] = e at hmatch hsc ⊢
      have hread := instAnnots_substEnv_renameExpr htr hfix e hsc
      cases e with
      | fvar fmd x ann =>
        cases ann with
        | none => simpa only [renameExpr_fvar, renameAnnot, Option.map_none] using hmatch
        | some t =>
          show LExpr.HasType C Γ (instAnnots Δ (.fvar fmd x (some t))) _
          rw [← hread]
          exact hmatch
      | const | op | bvar | abs | quant | app | ite | eq =>
        show LExpr.HasType C Γ (instAnnots Δ _) _
        rw [← hread]
        exact hmatch
    · intro e he
      have hmem : renameExpr m e ∈ CallArg.getInputExprs (renameCallArgs m args) := by
        rw [hinE]
        exact List.mem_map_of_mem he
      exact writtenAnnotsOk_of_renameExpr m e (hinAnn (renameExpr m e) hmem)

/-- A typing of a renamed command read through the `S`-instances of every name ends in that
    environment and gives a typing of the written command from any environment the scope map
    tracks, ending in one the updated scope map tracks. -/
theorem TypeSpec.CmdExtHasType.of_rename {C : LContext CoreLParams} {P : Program}
    {Γ Γ' : TContext Unit} {Δ₀' : WrittenEnv} (S : Subst)
    (hfix : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v)
    (m : ScopeMap) (st : ScopeState) (c : Command)
    (hwfA : ∀ a ∈ Γ.aliases, TypeAlias.WF a) (hinv : ScopeAdmissible C.rigidTypeVars m st)
    (h : CmdExtHasType C P (substEnv S) Γ (renameCmd C.rigidTypeVars m st c).1 Γ' Δ₀')
    (hin : ∀ e ∈ Statement.cmdExprs c,
      unboundAnnotVar? false C.rigidTypeVars (renameCmd C.rigidTypeVars m st c).2.1 e = none) :
    Δ₀' = substEnv S ∧ ∀ Δ, WrittenEnv.Tracks S C.rigidTypeVars m Δ →
      ∃ Δ', WrittenEnv.Tracks S C.rigidTypeVars (renameCmd C.rigidTypeVars m st c).2.1 Δ' ∧
        CmdExtHasType C P Δ Γ c Γ' Δ' := by
  obtain ⟨-, hadmDecl⟩ := h.rename_scopeAdmissible C.rigidTypeVars m st c hwfA hinv
  cases c with
  | call pname tyArgs args md =>
    simp only [renameCmd] at h hin ⊢
    exact CmdExtHasType.of_rename_call S hfix m pname tyArgs args md h hin
  | cmd cc =>
    cases cc with
    | init x xty e md =>
      obtain ⟨vars, ty⟩ := xty
      cases vars with
      | cons _ _ =>
        simp only [renameCmd] at h ⊢
        match h with
        | .cmd _ _ _ _ _ (.init_det _ _ _ _ _ _ _ _ _ _ _ _ hxty _ _ _ _ _ _) =>
          cases hxty
        | .cmd _ _ _ _ _ (.init_nondet _ _ _ _ _ _ _ _ _ _ hxty _ _ _) =>
          cases hxty
      | nil =>
        have hadmTy := hadmDecl x ty e md rfl
        cases e with
        | det e =>
          simp only [renameCmd, renameExprOrNondet, ExprOrNondet.map] at h hin ⊢
          match h with
          | .cmd _ _ _ _ _ (.init_det _ _ _ _ _ mty _ _ _ _ hfind hfv hxty ⟨hinst, hsrc⟩
              hwk hexpr hann _ heqv) =>
            cases hxty
            refine ⟨rfl, fun Δ htr => ?_⟩
            obtain ⟨hinst', htr'⟩ := scopedAnnotInst_of_exact hfix htr hinst
            have hfv' : x ∉ HasFvars.getFvars (P := Expression) e := by
              rw [← getFvars_renameExpr _ e]
              exact hfv
            have hread : e ∈ [e] := List.mem_singleton.mpr rfl
            have hscope := annotsInScope_of_unboundAnnotVar? htr'.3 (hin e hread)
            have hexpr' : LExpr.HasType C Γ
                (instAnnots (Δ.bindFirst C.rigidTypeVars ty
                  (restrictTo (fun v => LMonoTy.subst S (.ftvar (checkerName
                    (bindVars C.rigidTypeVars (LMonoTy.freeVars ty) m st).1 v))) ty)) e)
                (.forAll [] mty) := by
              rw [← instAnnots_substEnv_renameExpr htr' hfix e hscope]
              exact hexpr
            have hdecl := ValidDeclaredTy.of_renameTy _ hadmTy hsrc
            exact ⟨_, htr', .cmd _ _ _ _ _ (.init_det _ _ _ _ _ _ _ _ _ _ hfind hfv' rfl
              ⟨hinst', hdecl⟩ hwk hexpr' (writtenAnnotsOk_of_renameExpr _ e hann) hscope
              heqv)⟩
        | nondet =>
          simp only [renameCmd, renameExprOrNondet, ExprOrNondet.map] at h ⊢
          match h with
          | .cmd _ _ _ _ _
              (.init_nondet _ _ _ _ _ _ _ _ _ hfind hxty ⟨hinst, hsrc⟩ hwk heqv) =>
            cases hxty
            refine ⟨rfl, fun Δ htr => ?_⟩
            obtain ⟨hinst', htr'⟩ := scopedAnnotInst_of_exact hfix htr hinst
            have hdecl := ValidDeclaredTy.of_renameTy _ hadmTy hsrc
            exact ⟨_, htr', .cmd _ _ _ _ _ (.init_nondet _ _ _ _ _ _ _ _ _ hfind rfl
              ⟨hinst', hdecl⟩ hwk heqv)⟩
    | set x e md =>
      cases e with
      | det e =>
        simp only [renameCmd, renameExprOrNondet, ExprOrNondet.map] at h hin ⊢
        match h with
        | .cmd _ _ _ _ _ (.set_det _ _ _ mty _ _ _ hfind hexpr hann _ heqv) =>
          refine ⟨rfl, fun Δ htr => ?_⟩
          have hread : e ∈ [e] := List.mem_singleton.mpr rfl
          have hscope := annotsInScope_of_unboundAnnotVar? htr.3 (hin e hread)
          have hexpr' : LExpr.HasType C Γ (instAnnots Δ e) (.forAll [] mty) := by
            rw [← instAnnots_substEnv_renameExpr htr hfix e hscope]
            exact hexpr
          exact ⟨Δ, htr, .cmd _ _ _ _ _ (.set_det _ _ _ mty _ _ _ hfind hexpr'
            (writtenAnnotsOk_of_renameExpr _ e hann) hscope heqv)⟩
      | nondet =>
        simp only [renameCmd, renameExprOrNondet, ExprOrNondet.map] at h ⊢
        match h with
        | .cmd _ _ _ _ _ (.set_nondet _ _ _ mty _ _ hfind heqv) =>
          exact ⟨rfl, fun Δ htr => ⟨Δ, htr, .cmd _ _ _ _ _
            (.set_nondet _ _ _ mty _ _ hfind heqv)⟩⟩
    | assert l e md | assume l e md | cover l e md =>
      simp only [renameCmd] at h hin ⊢
      match h with
      | .cmd _ _ _ _ _ hc =>
        cases hc <;> rename_i hexpr hann _ heqv
        all_goals
          refine ⟨rfl, fun Δ htr => ?_⟩
          have hread : e ∈ [e] := List.mem_singleton.mpr rfl
          have hscope := annotsInScope_of_unboundAnnotVar? htr.3 (hin e hread)
          have hexpr' : LExpr.HasType C Γ (instAnnots Δ e) (.forAll [] .bool) := by
            rw [← instAnnots_substEnv_renameExpr htr hfix e hscope]
            exact hexpr
          have hann' := writtenAnnotsOk_of_renameExpr _ e hann
          first
            | exact ⟨Δ, htr, .cmd _ _ _ _ _ (.assert _ _ _ _ _ _ hexpr' hann' hscope heqv)⟩
            | exact ⟨Δ, htr, .cmd _ _ _ _ _ (.assume _ _ _ _ _ _ hexpr' hann' hscope heqv)⟩
            | exact ⟨Δ, htr, .cmd _ _ _ _ _ (.cover _ _ _ _ _ _ hexpr' hann' hscope heqv)⟩

/-! ### Renamed commands avoid the type parameters -/

/-- Renaming an expression's annotations through a scope map whose names avoid `ps` keeps its
    free-variable and binder annotations avoiding `ps`. -/
theorem annotsAvoid_renameExpr {ps : List TyIdentifier} {m : ScopeMap}
    (hm : ∀ p ∈ m, p.2 ∉ ps) {e : Expression.Expr} (he : LExpr.AnnotsAvoid e ps) :
    LExpr.AnnotsAvoid (renameExpr m e) ps := by
  obtain ⟨-, -, hf, hb⟩ := renameExpr_facts m e
  have hname : ∀ v, v ∉ ps → annotName m v ∉ ps := by
    intro v hv
    unfold annotName
    split
    · exact checkerName_not_mem hm hv
    · exact hv
  intro t ht
  rw [hf, hb, List.mem_append, List.mem_map, List.mem_map] at ht
  rcases ht with ⟨t0, ht0, rfl⟩ | ⟨t0, ht0, rfl⟩
  · exact freeVars_renameTy_not_mem _ hname t0 (he t0 (List.mem_append_left _ ht0))
  · exact freeVars_renameTy_not_mem _ hname t0 (he t0 (List.mem_append_right _ ht0))

/-- Renaming a command that avoids `ps`, from a scope map and walk state that avoid `ps`, gives a
    command, scope map and walk state that avoid `ps`. -/
theorem renameCmd_varsAvoid {ps : List TyIdentifier} (rigid : List TyIdentifier)
    (m : ScopeMap) (st : ScopeState) (c : Command) (hc : Command.VarsAvoid ps c)
    (hsc : ScopeAvoids ps m st) :
    Command.VarsAvoid ps (renameCmd rigid m st c).1 ∧
      ScopeAvoids ps (renameCmd rigid m st c).2.1 (renameCmd rigid m st c).2.2 := by
  cases c with
  | cmd cc =>
    cases cc with
    | init _ xty e _ =>
      obtain ⟨vars, ty⟩ := xty
      cases vars with
      | nil =>
        obtain ⟨hty, he⟩ := hc
        rw [LTy.freeVars_forAll_nil] at hty
        have hr := bindVars_scopeAvoids rigid (LMonoTy.freeVars ty) m st (fun v hv _ => hty v hv)
          hsc
        refine ⟨⟨?_, ?_⟩, hr⟩
        · rw [LTy.freeVars_forAll_nil]
          exact freeVars_renameTy_not_mem _ (fun v hv => checkerName_not_mem hr.names hv) ty hty
        · intro x' hx'
          cases e with
          | det e0 =>
            simp only [renameExprOrNondet, ExprOrNondet.map, ExprOrNondet.det.injEq] at hx'
            subst hx'
            exact annotsAvoid_renameExpr hr.names (he e0 rfl)
          | nondet => cases hx'
      | cons _ _ => exact ⟨hc, hsc⟩
    | set _ e _ =>
      refine ⟨?_, hsc⟩
      intro x' hx'
      cases e with
      | det e0 =>
        simp only [renameExprOrNondet, ExprOrNondet.map, ExprOrNondet.det.injEq] at hx'
        subst hx'
        exact annotsAvoid_renameExpr hsc.names (hc e0 rfl)
      | nondet => cases hx'
    | assert | assume | cover => exact ⟨annotsAvoid_renameExpr hsc.names hc, hsc⟩
  | call _ _ args _ =>
    refine ⟨?_, hsc⟩
    intro e he
    rw [getInputExprs_renameCallArgs, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact annotsAvoid_renameExpr hsc.names (hc e0 he0)

/-- An environment tracked by `m` reads only types avoiding the parameters `σ` renames, when the
    checker names of `m` avoid them and no type in the range of `S` mentions one. -/
theorem TypeSpec.WrittenEnv.Tracks.noParam {σ : RigidNames} {S : Subst}
    {rigid : List TyIdentifier} {m : ScopeMap} {Δ : WrittenEnv}
    (htr : WrittenEnv.Tracks S rigid m Δ) (hm : ∀ p ∈ m, p.2 ∉ σ.map Prod.fst)
    (hS : NoParamRange σ S) : ReadAvoids σ Δ := by
  intro v t hv x hx
  obtain ⟨w, hw, rfl⟩ := htr.sound v t hv
  rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S (.ftvar w) hx) with hx | hx
  · simp only [LMonoTy.freeVars, List.mem_singleton] at hx
    subst hx
    obtain ⟨l₁, l₂, hm', -⟩ := List.lookup_eq_some_iff.mp hw
    have hmem : (v, x) ∈ m := by
      rw [hm']
      exact List.mem_append_right _ List.mem_cons_self
    exact hm (v, x) hmem
  · exact hS x hx

end Core

end -- public section
