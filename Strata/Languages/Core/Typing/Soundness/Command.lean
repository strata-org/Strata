/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementType
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
public import Strata.Languages.Core.Typing.Props.SkolemScopeProps
public import Strata.Languages.Core.Typing.Spec.ProcSigAgreement
import all Strata.Languages.Core.Typing.Props.CmdTypeProps
import all Strata.Languages.Core.Typing.Props.SourceExprResolveProps
import Strata.Languages.Core.Typing.Props.ProcedureTypeProps
public import Strata.Languages.Core.FunctionType
public import Strata.Languages.Core.Typing.Spec.CommandTypeSpec
public import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Imperative.CmdType
public import Strata.Languages.Core.CmdType
import all Strata.Languages.Core.CmdType
import all Strata.DL.Imperative.CmdType
import Strata.DL.Lambda.LExprAnnotRel
import Strata.DL.Lambda.LExprProps
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.DL.Lambda.LTyUnify
import Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.LExprTypeEnvProps
import Strata.DL.Lambda.LExprTProps
import Strata.Languages.Core.StatementProps
import Strata.Languages.Core.Typing.Props.StatementEraseProps
import Strata.Languages.Core.Typing.Props.ExprEraseProps
import Strata.DL.Lambda.LExprTEraseProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.CallWFProps
import all Strata.Languages.Core.StatementType
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Languages.Core.Statement
import all Strata.DL.Imperative.CmdType
import Strata.DL.Imperative.Cmd
import Strata.Languages.Core.Typing.Spec.CmdTypeSpec

/-! ## Soundness of the command typechecker

An accepted command satisfies the typechecker spec under each well-formed substitution absorbing
the solution (`Statement.typeCheckCmd_sound_absorbing`), and in particular under the checker's
own solution (`Statement.typeCheckCmd_sound`).

Key theorems: `Statement.typeCheckCmd_sound_absorbing` and `Statement.typeCheckCmd_sound` (input
soundness), `TypeSpec.CmdExtHasType.deskolemize` (typing survives deskolemization),
`Statement.typeCheckCmd_absorbs` and `Statement.typeCheckCmd_preserves_TEnvWF` (what a checked
command does to the environment) and `Statement.typeCheckCmd_varsAvoid` (the environment keeps
avoiding the type parameters). -/

public section

namespace Core

open Lambda Imperative
open TypeSpec
open Except

/-- The written annotations of a resolved expression are valid in every substitution instance of
    the starting context. -/
theorem resolveSource_writtenAnnotsOk
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (hres : SourceExpr.resolve C Env e = .ok (et, Env')) (S : Subst) :
    WrittenAnnotsOk C (TContext.subst Env.context S) e := by
  have hsource := hres
  refine ⟨?_, SourceExpr.resolve_binderAnnotTyVarsAdmissible C Env Env' e et hsource⟩
  change FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid
    (TContext.subst Env.context S).aliases e
  rw [TContext.subst_aliases]
  exact SourceExpr.resolve_fvarAnnotsWF C Env Env' e et hsource

/-- Expression scoping transports across pointwise context equality. -/
private theorem WellScoped.of_FindEq
    {Γ Γ' : TContext Unit} {e : Expression.Expr}
    (hctx : TContext.FindEq (T := CoreLParams) Γ Γ')
    (h : LExpr.WellScoped e Γ') :
    LExpr.WellScoped e Γ := by
  intro x hx
  have hmem := h x hx
  unfold TContext.knownVars at hmem ⊢
  obtain ⟨ty, hfind⟩ := (Strata.Util.HMaps.mem_keys_iff_find? Γ'.types x.1).mp hmem
  have hfindΓ : Γ.types.find? x.1 = some ty := by
    rw [hctx.find? x.1]
    exact hfind
  exact Strata.Util.HMaps.find?_mem_keys Γ.types hfindΓ

/-- Resolving a source expression produces a substitution that absorbs the one it was given. -/
theorem resolveSource_absorbs
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (h : SourceExpr.resolve C Env e = .ok (et, Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  obtain ⟨EnvR, hresolve, hlinkAbs⟩ :=
    SourceExpr.resolve_link_absorbs C Env Env' e et h
  exact Subst.absorbs_trans _ _ _
    (resolve_absorbs C Env EnvR e et hresolve he hf)
    hlinkAbs

/-- Successful declaration preprocessing accepts only a monotype and agrees with its checked
    instantiation. -/
theorem preprocess_instantiateWithCheck
    (C : LContext CoreLParams) (Env Env1 : TEnv Unit)
    (xty ty1 : LTy) (h : CmdType.preprocess C Env xty = .ok (ty1, Env1)) :
    ∃ m0 mtyP, xty = .forAll [] m0 ∧ ty1 = .forAll [] mtyP ∧
      LTy.instantiateWithCheck (.forAll [] m0) C Env = .ok (mtyP, Env1) := by
  obtain ⟨m0, mtyP, rfl, rfl, hsrc⟩ := preprocess_ok_inv C Env Env1 xty ty1 h
  exact ⟨m0, mtyP, rfl, rfl,
    typeCheckSource_notGeneratedOrRigid_instantiateWithCheck m0 mtyP C Env Env1 hsrc⟩

/-- The Core boolean-type test succeeds only for `bool`. -/
theorem CmdType.isBoolType_inv
    (m : LMonoTy) (h : CmdType.isBoolType (.forAll [] m) = true) :
    m = LMonoTy.bool := by
  by_cases hm : m = LMonoTy.tcons "bool" []
  · exact hm
  · exact absurd h (by simp [CmdType.isBoolType, hm])

/-- If a substituted declaration uses only registered types, so does its substituted type. -/
theorem knownInstance_of_stored_init
    (C : LContext CoreLParams) (S : Subst)
    (x : Expression.Ident) (mty : LMonoTy) (e : ExprOrNondet Expression)
    (md : MetaData Expression)
    (h : allCmdTys (fun m => LMonoTy.knownInstance m C.knownTypes)
      (Statement.Command.subst S
        (CmdExt.cmd (Imperative.Cmd.init x (.forAll [] mty) e md))) = true) :
    LMonoTy.knownInstance (LMonoTy.subst S mty) C.knownTypes = true := by
  simp only [Statement.Command.subst, Statement.Cmd.subst, allCmdTys, allLTyTys,
    Bool.and_eq_true] at h
  exact h.1

/-- Substitution commutes with inserting one context binding up to lookup equality. -/
private theorem subst_insert_FindEq
    (Γ : TContext Unit) (S : Subst) (x : Expression.Ident) (t : LTy) :
    TContext.FindEq (T := CoreLParams)
      { TContext.subst Γ S with
        types := (TContext.subst Γ S).types.insert x (LTy.subst S t) }
      (TContext.subst { Γ with types := Γ.types.insert x t } S) := by
  refine ⟨fun y => ?_, rfl⟩
  simp only [TContext.subst, TContext.types.subst]
  rw [Strata.Util.HMaps.find?_mapValues]
  by_cases hxy : x = y
  · subst hxy
    rw [Strata.Util.HMaps.find?_insert_self, Strata.Util.HMaps.find?_insert_self,
      Option.map_some]
  · rw [Strata.Util.HMaps.find?_insert_ne _ y x _ (fun hc => hxy hc.symm),
      Strata.Util.HMaps.find?_insert_ne _ y x t (fun hc => hxy hc.symm),
      Strata.Util.HMaps.find?_mapValues]

/-- Substitution preserves lookup equality of contexts. -/
theorem TContext.FindEq.subst_subst
    {Γ Γ' : TContext Unit} (S : Subst)
    (h : TContext.FindEq (T := CoreLParams) Γ Γ') :
    TContext.FindEq (T := CoreLParams) (TContext.subst Γ S) (TContext.subst Γ' S) := by
  refine ⟨fun x => ?_, ?_⟩
  · simp only [TContext.subst, TContext.types.subst]
    rw [Strata.Util.HMaps.find?_mapValues, Strata.Util.HMaps.find?_mapValues, h.find? x]
  · simpa only [TContext.subst_aliases] using h.2

/-- Adding one fresh binding to the newest scope agrees with inserting it into any
    pointwise-equivalent context. -/
private theorem addInNewest_insert_FindEq
    (Γ1 Γ2 : TContext Unit) (x : Expression.Ident) (v : LTy)
    (h : TContext.FindEq (T := CoreLParams) Γ1 Γ2)
    (hfresh : Γ1.types.find? x = none) :
    TContext.FindEq (T := CoreLParams)
      { Γ1 with types := Γ1.types.addInNewest (Strata.Util.HMap.single x v) }
      { Γ2 with types := Γ2.types.insert x v } := by
  refine ⟨fun y => ?_, h.2⟩
  by_cases hy : y = x
  · subst y
    rw [Strata.Util.HMaps.find?_addInNewest_self _ _ _
      (Strata.Util.HMaps.all_scopes_find?_none Γ1.types x hfresh),
      Strata.Util.HMaps.find?_insert_self]
  · rw [Strata.Util.HMaps.find?_addInNewest_ne Γ1.types x v y hy,
      Strata.Util.HMaps.find?_insert_ne Γ2.types y x v hy]
    exact h.find? y

/-- Core's local-declaration step adds the binding of `x` to `ty` to the newest scope. -/
private theorem CmdType.update_eq_single (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    CmdType.update Env x ty =
      Env.addInNewestContext (T := CoreLParams) (Strata.Util.HMap.single x ty) := by
  simp only [CmdType.update, Strata.Util.HMap.ofList_singleton]

/-! ### Soundness of the command checker -/

/-- A declared type written as `m0` is scoped at its `S`-instances: the instantiation sending each
    type variable of `m0` to its `S`-image fixes the rigid type variables when `S` does, agrees
    with `substEnv S`, and instantiates `m0` to anything alias-equivalent to `S` applied to it. -/
private theorem scopedAnnotInst_substEnv_restrictTo {aliases : List TypeAlias}
    {rigid : List TyIdentifier} {S : Subst} {m0 mty : LMonoTy}
    (hfix : ∀ v ∈ rigid, LMonoTy.subst S (.ftvar v) = .ftvar v)
    (hae : AliasEquiv aliases (LMonoTy.subst S m0) mty) :
    ScopedAnnotInst aliases rigid (substEnv S)
      (restrictTo (fun v => LMonoTy.subst S (.ftvar v)) m0) m0 mty := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    by_cases hvm : v ∈ LMonoTy.freeVars m0
    · rw [restrictTo_ftvar _ m0 v hvm]
      exact hfix v hv
    · exact restrictTo_ftvar_of_not_mem _ m0 v hvm
  · intro v hv t hΔ
    simp only [substEnv, Option.some.injEq] at hΔ
    rw [restrictTo_ftvar _ m0 v hv, hΔ]
  · have hrestrict : LMonoTy.subst [restrictTo (fun v => LMonoTy.subst S (.ftvar v)) m0] m0 =
        LMonoTy.subst S m0 := by
      apply agree_on_freeVars_implies_subst_eq
      intro v hv
      exact restrictTo_ftvar _ m0 v hv
    rw [hrestrict]
    exact hae

/-- The declaration rule's type obligations hold under `S` for a checked declared monotype `m0`
    as written, stored under `U`, when `S` fixes the rigid type variables, absorbs `U`, and the
    substituted declaration uses only registered types. -/
private theorem declaredTy_obligations
    (C : LContext CoreLParams) (Env : TEnv Unit) (S U : Subst) (x : Expression.Ident)
    (m0 mtyP : LMonoTy) (e : ExprOrNondet Expression) (md : MetaData Expression)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (hfix : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v)
    (hae : AliasEquiv Env.context.aliases m0 mtyP)
    (hsrc : SourceTyWF C TyVarAdmissibility.notGeneratedOrRigid Env.context.aliases m0 mtyP)
    (h_absorbs : Subst.absorbs S U)
    (h_stored : allCmdTys (fun m => LMonoTy.knownInstance m C.knownTypes)
      (Statement.Command.subst S
        (CmdExt.cmd (Imperative.Cmd.init x (.forAll [] (LMonoTy.subst U mtyP)) e md))) = true) :
    LMonoTy.subst S (LMonoTy.subst U mtyP) = LMonoTy.subst S mtyP ∧
      ScopedAnnotInst Env.context.aliases C.rigidTypeVars (substEnv S)
        (restrictTo (fun v => LMonoTy.subst S (.ftvar v)) m0) m0 (LMonoTy.subst S mtyP) ∧
      ValidDeclaredTy C Env.context.aliases m0 ∧
      C.WellKindedTy (LMonoTy.subst S mtyP) := by
  have hkill : LMonoTy.subst S (LMonoTy.subst U mtyP) = LMonoTy.subst S mtyP :=
    LMonoTy.subst_absorbs S U mtyP h_absorbs
  have hkn : LMonoTy.knownInstance (LMonoTy.subst S mtyP) C.knownTypes = true := by
    rw [← hkill]
    exact knownInstance_of_stored_init C S x (LMonoTy.subst U mtyP) e md h_stored
  exact ⟨hkill,
    scopedAnnotInst_substEnv_restrictTo hfix
      (LExpr.AliasEquiv_subst Env.context.aliases m0 mtyP S hae h_env.aliasesWF),
    ⟨mtyP, hsrc⟩,
    LMonoTy.knownInstance_wellKinded _ C.knownTypes hkn⟩

/-- Substituting after declaring a fresh variable is lookup-equal to inserting its substituted
    binding into the substituted lookup-equal context. -/
private theorem update_subst_FindEq
    (Γ : TContext Unit) (E : TEnv Unit) (S : Subst) (x : Expression.Ident) (m : LMonoTy)
    (hctx : TContext.FindEq (T := CoreLParams) E.context Γ)
    (hfresh : E.context.types.find? x = none) :
    TContext.FindEq (T := CoreLParams)
      { TContext.subst Γ S with
        types := (TContext.subst Γ S).types.insert x (.forAll [] (LMonoTy.subst S m)) }
      (TContext.subst (CmdType.update E x (.forAll [] m)).context S) := by
  refine TContext.FindEq.trans (subst_insert_FindEq Γ S x (.forAll [] m)) ?_
  rw [CmdType.update_eq_single]
  exact TContext.FindEq.subst_subst S
    (addInNewest_insert_FindEq E.context Γ x (.forAll [] m) hctx hfresh).symm

/-- After resolving an expression and unifying `a` with its type, the expression with
    annotations read through any well-formed `S` absorbing the solution has type `a` under `S`. -/
private theorem resolveSource_HasType_after_unify
    (C : LContext CoreLParams) (Env E2 : TEnv Unit) (e : Expression.Expr)
    (ea : LExprT CoreLParams.mono) (a : LMonoTy) (Sx : SubstInfo) (S : Subst)
    (hres : SourceExpr.resolve C Env e = .ok (ea, E2))
    (hu : Constraints.unify [(a, ea.toLMonoTy)] E2.stateSubstInfo = .ok Sx)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_absorbs : Subst.absorbs S Sx.subst) (h_wf : SubstWF S)
    (h_known : BinderAnnotsKnown C (LExpr.applyTypeSubst ea.unresolved S)) :
    LExpr.HasType C (TContext.subst Env.context S) (instAnnots (substEnv S) e)
      (.forAll [] (LMonoTy.subst S a)) := by
  have hty : LMonoTy.subst S a = LMonoTy.subst S ea.toLMonoTy :=
    LMonoTy.subst_eq_of_absorbs S Sx.subst a ea.toLMonoTy h_absorbs
      (Constraints.unify_sound _ _ _ hu (a, ea.toLMonoTy) List.mem_cons_self)
  rw [hty]
  exact SourceExpr.resolve_HasType_instAnnots C Env E2 e ea hres
    (SourceExpr.resolve_WellScoped C Env E2 e ea hres)
    h_env h_fac h_mono h_aliasNames S
    (Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ hu) h_absorbs) h_wf h_known

/-- Under any well-formed `S` absorbing the solution, an accepted assertion, assumption or cover
    expression is boolean with valid written annotations, and the substituted contexts agree. -/
private theorem boolCheck_sound
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (cc : Cmd Expression)
    (e e' : Expression.Expr) (ety : LTy) (S : Subst)
    (hinf : CmdType.inferType C Env cc e = .ok (e', ety, Env'))
    (hbool : CmdType.isBoolType ety = true)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (h_wf : SubstWF S)
    (h_known : BinderAnnotsKnown C (LExpr.applyTypeSubst e' S)) :
    LExpr.HasType C (TContext.subst Env.context S) (instAnnots (substEnv S) e)
      (.forAll [] LMonoTy.bool) ∧
      WrittenAnnotsOk C (TContext.subst Env.context S) e ∧
      TContext.FindEq (T := CoreLParams) (TContext.subst Env.context S)
        (TContext.subst Env'.context S) := by
  obtain ⟨ea, hres, rfl, rfl⟩ := CmdType.inferType_inv C Env Env' cc e e' ety hinf
  have hb := CmdType.isBoolType_inv ea.toLMonoTy hbool
  have hctx := SourceExpr.resolve_context_FindEq C Env Env' e ea hres
  have ht := SourceExpr.resolve_HasType_instAnnots C Env Env' e ea hres
    (SourceExpr.resolve_WellScoped C Env Env' e ea hres)
    h_env h_fac h_mono h_aliasNames S h_absorbs h_wf h_known
  rw [hb, LMonoTy.subst_bool] at ht
  exact ⟨ht, resolveSource_writtenAnnotsOk C Env Env' e ea hres S,
    TContext.FindEq.subst_subst S hctx.symm⟩

/-! ### Scopes with alias-resolved types and no aliases -/

/-- Inserting a binding whose scheme resolves to itself commutes with `dealias`, up to lookup. -/
private theorem dealias_insert_FindEq (Γ : TContext Unit) (x : Expression.Ident) (t : LTy)
    (ht : Γ.resolveScheme t = t) :
    TContext.FindEq (T := CoreLParams)
      { Γ.dealias with types := Γ.dealias.types.insert x t }
      { Γ with types := Γ.types.insert x t }.dealias := by
  refine ⟨fun y => ?_, rfl⟩
  rw [TContext.dealias_find? (T := CoreLParams),
    TContext.resolveScheme_congr (T := CoreLParams) (Γ := { Γ with types := Γ.types.insert x t })
      (Γ' := Γ) rfl]
  by_cases hxy : x = y
  · subst hxy
    rw [Strata.Util.HMaps.find?_insert_self, Strata.Util.HMaps.find?_insert_self, Option.map_some,
      ht]
  · rw [Strata.Util.HMaps.find?_insert_ne _ y x _ (fun hc => hxy hc.symm),
      Strata.Util.HMaps.find?_insert_ne _ y x t (fun hc => hxy hc.symm),
      TContext.dealias_find? (T := CoreLParams)]

/-- Declaring a fresh variable at a type that resolves to itself, then resolving and substituting,
    is lookup-equal to inserting its substituted binding into the resolved substituted scope. -/
theorem update_subst_dealias_FindEq
    (Γ : TContext Unit) (E : TEnv Unit) (S : Subst) (x : Expression.Ident) (m : LMonoTy)
    (hctx : TContext.FindEq (T := CoreLParams) E.context Γ)
    (hfresh : E.context.types.find? x = none) (hm : Γ.resolveTy m = m) :
    TContext.FindEq (T := CoreLParams)
      { TContext.subst Γ.dealias S with
        types := (TContext.subst Γ.dealias S).types.insert x (.forAll [] (LMonoTy.subst S m)) }
      (TContext.subst (CmdType.update E x (.forAll [] m)).context.dealias S) := by
  refine TContext.FindEq.trans (subst_insert_FindEq Γ.dealias S x (.forAll [] m)) ?_
  refine TContext.FindEq.subst_subst S ?_
  rw [CmdType.update_eq_single]
  have ht : Γ.resolveScheme (.forAll [] m) = .forAll [] m := by
    rw [TContext.resolveScheme_forAll, hm]
  exact (dealias_insert_FindEq Γ x _ ht).trans
    (addInNewest_insert_FindEq E.context Γ x (.forAll [] m) hctx hfresh).symm.dealias

/-- An expression whose every type annotation is registered has registered binder annotations. -/
theorem binderAnnotsKnown_of_allExprTys (C : LContext CoreLParams) (e : Expression.Expr)
    (h : allExprTys (fun m => LMonoTy.knownInstance m C.knownTypes) e = true) :
    BinderAnnotsKnown C e :=
  Lambda.allUserProvidedTypes_binderAnnotations e
    ((allExprTys_eq_allUserProvidedTypes _ e).symm.trans h)

/-- If a substituted plain command uses only registered types, so do the binder annotations of
    the substitution of any expression it reads. -/
theorem binderAnnotsKnown_of_stored_cmd (C : LContext CoreLParams) (S : Subst)
    (c : Cmd Expression) (e : Expression.Expr) (hc : e ∈ Imperative.Cmd.readExprs c)
    (h : allCmdTys (fun m => LMonoTy.knownInstance m C.knownTypes)
      (Statement.Command.subst S (CmdExt.cmd c)) = true) :
    BinderAnnotsKnown C (LExpr.applyTypeSubst e S) := by
  apply binderAnnotsKnown_of_allExprTys
  cases c with
  | init x ty e0 md =>
    cases e0 with
    | det e' =>
      simp only [Imperative.Cmd.readExprs, ExprOrNondet.toList, List.mem_singleton] at hc
      subst hc
      simp only [Statement.Command.subst, Statement.Cmd.subst, Statement.substExprOrNondet,
        Imperative.ExprOrNondet.map, allCmdTys, allExprOrNondetTys, Bool.and_eq_true] at h
      exact h.2
    | nondet => simp only [Imperative.Cmd.readExprs, ExprOrNondet.toList, List.not_mem_nil] at hc
  | set x e0 md =>
    cases e0 with
    | det e' =>
      simp only [Imperative.Cmd.readExprs, ExprOrNondet.toList, List.mem_singleton] at hc
      subst hc
      simp only [Statement.Command.subst, Statement.Cmd.subst, Statement.substExprOrNondet,
        Imperative.ExprOrNondet.map, allCmdTys, allExprOrNondetTys] at h
      exact h
    | nondet => simp only [Imperative.Cmd.readExprs, ExprOrNondet.toList, List.not_mem_nil] at hc
  | assert l e0 md | assume l e0 md | cover l e0 md =>
    simp only [Imperative.Cmd.readExprs, List.mem_singleton] at hc
    subst hc
    simp only [Statement.Command.subst, Statement.Cmd.subst, allCmdTys] at h
    exact h

/-- If a substituted call uses only registered types, so do the binder annotations of each
    substituted input expression. -/
theorem binderAnnotsKnown_of_call_inputs (C : LContext CoreLParams) (S : Subst)
    (nm : String) (tyArgs : Option (List Expression.Ty)) (args : List (CallArg Expression))
    (md : MetaData Expression)
    (h : allCmdTys (fun m => LMonoTy.knownInstance m C.knownTypes)
      (Statement.Command.subst S (CmdExt.call nm tyArgs args md)) = true) :
    ∀ e ∈ CallArg.getInputExprs args, BinderAnnotsKnown C (LExpr.applyTypeSubst e S) := by
  simp only [Statement.Command.subst, allCmdTys, Bool.and_eq_true, List.all_eq_true] at h
  intro e he
  simp only [CallArg.getInputExprs, Calls.getInputExprs, List.mem_filterMap] at he
  obtain ⟨a, ha, hae⟩ := he
  have hall := h.2 (Statement.CallArg.subst S a) (List.mem_map_of_mem ha)
  cases a with
  | inArg e0 =>
    simp only [Option.some.injEq] at hae
    subst hae
    exact binderAnnotsKnown_of_allExprTys C _ hall
  | inoutArg id =>
    simp only [Option.some.injEq] at hae
    subst hae
    intro t ht
    have hfvar : (HasFvar.mkFvar id : Expression.Expr) = LExpr.fvar Core.coreLoc id none := rfl
    rw [hfvar, LExpr.applyTypeSubst_fvar_none] at ht
    simp only [LExpr.binderAnnotations, List.not_mem_nil] at ht
  | outArg id => simp only [reduceCtorEq] at hae

/-- A successful determinate initialization, run with a well-formed `S` that absorbs the final
    substitution, is typed by the spec in the `S`-applied scope and ends in a scope with the same
    lookups as the checker's. -/
private theorem imperativeCmd_sound_initDet
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (x : CoreIdent) (xty : LTy)
    (expr : Expression.Expr) (md : MetaData Expression) (c' : Cmd Expression) (S : Subst)
    (run : ImperativeCmdRun C Env (.init x xty (.det expr) md) c' Env')
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_stored : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S (CmdExt.cmd c')) = true)
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (h_wf : SubstWF S)
    (hfix : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v) :
    ∃ Δ', CmdHasType C (substEnv S) (TContext.subst Env.context S)
        (.init x xty (.det expr) md) Δ' (substEnv S) ∧
      TContext.FindEq (T := CoreLParams) Δ' (TContext.subst Env'.context S) := by
  cases run with
  | @initDet _ _ ty1 ety ty3 _ e1 _ E1 E2 E3 E4 hlk' hxfv hpre hinf hunif hpost =>
    obtain ⟨m0, mtyP, rfl, rfl, hE1, hae, hsrc⟩ :=
      CmdType.preprocess_inv C Env E1 xty ty1 hpre
    subst E1
    obtain ⟨ea, hres, rfl, rfl⟩ :=
      CmdType.inferType_inv C Env E2
        (.init x (.forAll [] m0) (.det expr) md) expr e1 ety hinf
    obtain ⟨a, b, Sx, ha, hb, hu, rfl⟩ :=
      CmdType.unifyTypes_inv E2 E3 (.forAll [] mtyP)
        (.forAll [] ea.toLMonoTy) hunif
    injection ha with _ ha'
    injection hb with _ hb'
    subst ha'
    subst hb'
    obtain ⟨rfl, rfl⟩ :=
      CmdType.postprocess_inv C (E2.updateSubst Sx) E4 mtyP ty3 hpost
    have habsSx : Subst.absorbs S Sx.subst := h_absorbs
    have hctx : TContext.FindEq (T := CoreLParams)
        E2.context Env.context :=
      SourceExpr.resolve_context_FindEq C Env E2 expr ea hres
    have hfresh : E2.context.types.find? x = none := by
      rw [hctx.find? x, hlk']
    obtain ⟨hkill, hrac, hvalid, hwk⟩ :=
      declaredTy_obligations C Env S (E2.updateSubst Sx).stateSubstInfo.subst x m0 mtyP
        (.det (CmdType.substExpr C (E2.updateSubst Sx) ea.unresolved)) md
        h_env hfix hae hsrc habsSx h_stored
    have hknown : BinderAnnotsKnown C (LExpr.applyTypeSubst ea.unresolved S) := by
      have hk := binderAnnotsKnown_of_stored_cmd C S _ _ (List.mem_singleton.mpr rfl) h_stored
      rwa [CmdType.substExpr,
        LExpr.applyTypeSubst_absorbs S (E2.updateSubst Sx).stateSubstInfo.subst habsSx] at hk
    refine ⟨_, ?_, update_subst_FindEq Env.context E2 S x _ hctx hfresh⟩
    rw [hkill]
    have hbind := WrittenEnv.bindFirst_substEnv (S := S) C.rigidTypeVars m0
      (restrictTo (fun v => LMonoTy.subst S (.ftvar v)) m0)
    have hfind : (TContext.subst Env.context S).types.find? x = none := by
      simp only [TContext.subst, TContext.types.subst,
        Strata.Util.HMaps.find?_mapValues, hlk', Option.map_none]
    have hfv : x ∉ HasFvars.getFvars (P := Expression) expr := by
      change x ∉ LExpr.LExpr.getVars expr
      unfold CmdType.freeVars at hxfv
      rw [getVars_eq_freeVars_idents]
      exact hxfv
    have hexpr : LExpr.HasType C (TContext.subst Env.context S)
        (instAnnots ((substEnv S).bindFirst C.rigidTypeVars m0
          (restrictTo (fun v => LMonoTy.subst S (.ftvar v)) m0)) expr)
        (.forAll [] (LMonoTy.subst S mtyP)) := by
      rw [hbind]
      exact resolveSource_HasType_after_unify C Env E2 expr ea mtyP Sx S hres hu
        h_env h_fac h_mono h_aliasNames habsSx h_wf hknown
    have hscope : AnnotsInScope C.rigidTypeVars ((substEnv S).bindFirst C.rigidTypeVars m0
        (restrictTo (fun v => LMonoTy.subst S (.ftvar v)) m0)) expr := by
      rw [hbind]
      exact annotsInScope_substEnv _ _ _
    have hrule := CmdHasType.init_det (substEnv S) (TContext.subst Env.context S) x
      (.forAll [] m0) expr
      (LMonoTy.subst S mtyP) m0 (restrictTo (fun v => LMonoTy.subst S (.ftvar v)) m0) md _
      hfind hfv
      rfl ⟨hrac, hvalid⟩ hwk hexpr
      (resolveSource_writtenAnnotsOk C Env E2 expr ea hres S) hscope (TContext.Equiv.refl _)
    rwa [hbind] at hrule

/-- An accepting imperative-command run types the source command as written, under each
    well-formed `S` that absorbs the solution and fixes the rigid type variables, with written type
    variables denoting their `S`-images. -/
private theorem imperativeCmd_sound
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (cc c' : Cmd Expression) (S : Subst)
    (run : ImperativeCmdRun C Env cc c' Env')
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_stored : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S (CmdExt.cmd c')) = true)
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (h_wf : SubstWF S)
    (hfix : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v) :
    ∃ Δ', CmdHasType C (substEnv S) (TContext.subst Env.context S) cc Δ' (substEnv S) ∧
      TContext.FindEq (T := CoreLParams) Δ' (TContext.subst Env'.context S) := by
  cases run with
  | @initNondet x xty ty1 ty2 md E1 E2 hlk' hpre hpost =>
    obtain ⟨m0, mtyP, rfl, rfl, hE1, hae, hsrc⟩ :=
      CmdType.preprocess_inv C Env E1 xty ty1 hpre
    subst E1
    obtain ⟨hty2, hE2⟩ := CmdType.postprocess_inv C Env E2 mtyP ty2 hpost
    subst ty2
    subst E2
    obtain ⟨hkill, hrac, hvalid, hwk⟩ :=
      declaredTy_obligations C Env S Env.stateSubstInfo.subst x m0 mtyP .nondet md
        h_env hfix hae hsrc h_absorbs h_stored
    refine ⟨_, ?_, update_subst_FindEq Env.context Env S x _
      (TContext.FindEq.refl _) hlk'⟩
    rw [hkill]
    have hfind : (TContext.subst Env.context S).types.find? x = none := by
      simp only [TContext.subst, TContext.types.subst,
        Strata.Util.HMaps.find?_mapValues, hlk', Option.map_none]
    have hrule := CmdHasType.init_nondet (substEnv S) (TContext.subst Env.context S) x
      (.forAll [] m0) (LMonoTy.subst S mtyP) m0
      (restrictTo (fun v => LMonoTy.subst S (.ftvar v)) m0) md _
      hfind rfl
      ⟨hrac, hvalid⟩ hwk (TContext.Equiv.refl _)
    rwa [WrittenEnv.bindFirst_substEnv] at hrule
  | @initDet x xty ty1 ety ty3 expr e1 md E1 E2 E3 E4 hlk' hxfv hpre hinf hunif hpost =>
    exact imperativeCmd_sound_initDet C Env _ x xty expr md _ S
      (.initDet hlk' hxfv hpre hinf hunif hpost) h_env h_fac
      h_mono h_aliasNames h_stored h_absorbs h_wf hfix
  | @setNondet x xty md hlk' hmono =>
    obtain ⟨mty, rfl⟩ := LTy.eq_forAll_nil_of_isMonoType hmono
    refine ⟨TContext.subst Env.context S, ?_, TContext.FindEq.refl _⟩
    refine CmdHasType.set_nondet (substEnv S) (TContext.subst Env.context S)
      x (LMonoTy.subst S mty) md _ ?_ (TContext.Equiv.refl _)
    exact TContext_types_subst_find _ _ _ _ hlk'
  | @setDet x xty ety expr e1 md E2 _ hlk' hinf hunif =>
    obtain ⟨ea, hres, rfl, rfl⟩ :=
      CmdType.inferType_inv C Env E2 (.set x (.det expr) md) expr e1 ety hinf
    obtain ⟨a, b, Sx, ha, hb, hu, rfl⟩ :=
      CmdType.unifyTypes_inv E2 Env' (Env.context.resolveScheme xty) (.forAll [] ea.toLMonoTy)
        hunif
    injection hb with _ hb'
    subst hb'
    obtain ⟨a0, rfl, rfl⟩ := TContext.resolveScheme_eq_forAll_nil ha
    have hctx : TContext.FindEq (T := CoreLParams) E2.context Env.context :=
      SourceExpr.resolve_context_FindEq C Env E2 expr ea hres
    have hknown : BinderAnnotsKnown C (LExpr.applyTypeSubst ea.unresolved S) :=
      binderAnnotsKnown_of_stored_cmd C S _ _ (List.mem_singleton.mpr rfl) h_stored
    refine ⟨TContext.subst Env.context S, ?_,
      TContext.FindEq.subst_subst S hctx.symm⟩
    refine CmdHasType.set_det (substEnv S) (TContext.subst Env.context S)
      x (LMonoTy.subst S a0) expr md _ ?_ ?_
      (resolveSource_writtenAnnotsOk C Env E2 expr ea hres S)
      (annotsInScope_substEnv _ _ _) (TContext.Equiv.refl _)
    · exact TContext_types_subst_find _ _ _ _ hlk'
    · have hae : AliasEquiv (TContext.subst Env.context S).aliases
          (LMonoTy.subst S (Env.context.resolveTy a0)) (LMonoTy.subst S a0) := by
        rw [TContext.subst_aliases]
        exact LExpr.AliasEquiv_subst Env.context.aliases _ _ S
          (LExpr.AliasEquiv.symm (TContext.aliasEquiv_resolveTy (T := CoreLParams) _ a0))
          h_env.aliasesWF
      exact LExpr.HasType.talias (C := C) _ _ _ _ hae
        (resolveSource_HasType_after_unify C Env E2 expr ea _ Sx S hres hu
          h_env h_fac h_mono h_aliasNames h_absorbs h_wf hknown)
  | @assert l e e1 ety md _ hinf hbool | @assume l e e1 ety md _ hinf hbool
  | @cover l e e1 ety md _ hinf hbool =>
    have hknown : BinderAnnotsKnown C (LExpr.applyTypeSubst e1 S) :=
      binderAnnotsKnown_of_stored_cmd C S _ _ (List.mem_singleton.mpr rfl) h_stored
    obtain ⟨ht, hw, hfind⟩ :=
      boolCheck_sound C Env Env' _ e e1 ety S hinf hbool h_env h_fac h_mono h_aliasNames
        h_absorbs h_wf hknown
    refine ⟨_, ?_, hfind⟩
    first
      | exact CmdHasType.assert (substEnv S) _ l e md _ ht hw
          (annotsInScope_substEnv _ _ _) (TContext.Equiv.refl _)
      | exact CmdHasType.assume (substEnv S) _ l e md _ ht hw
          (annotsInScope_substEnv _ _ _) (TContext.Equiv.refl _)
      | exact CmdHasType.cover (substEnv S) _ l e md _ ht hw
          (annotsInScope_substEnv _ _ _) (TContext.Equiv.refl _)

/-- Resolving a list of source expressions keeps the environment well formed, keeps its context
    lookup-equal (equivalent when it has a scope), and absorbs the starting substitution. The
    same holds for the environment each expression starts from, and the final substitution
    absorbs the one each expression produces. -/
theorem SourceExpr.resolves_step
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (exprs : List Expression.Expr) (ets : List (LExprT CoreLParams.mono))
    (h : SourceExpr.resolves C Env exprs = .ok (ets, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env' ∧
      TContext.FindEq (T := CoreLParams) Env'.context Env.context ∧
      (Env.context.types ≠ [] → TContext.Equiv (T := CoreLParams) Env'.context Env.context) ∧
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst ∧
      ets.length = exprs.length ∧
      ∀ i (hi : i < exprs.length) (hj : i < ets.length),
        ∃ Ei Ei',
          SourceExpr.resolve C Ei exprs[i] = .ok (ets[i], Ei') ∧
          LExpr.TEnvWF (T := CoreLParams) Ei ∧
          TContext.FindEq (T := CoreLParams) Ei.context Env.context ∧
          (Env.context.types ≠ [] →
            TContext.Equiv (T := CoreLParams) Ei.context Env.context ∧ Ei.context.types ≠ []) ∧
          Subst.absorbs Env'.stateSubstInfo.subst Ei'.stateSubstInfo.subst := by
  induction exprs generalizing Env ets with
  | nil =>
      simp only [SourceExpr.resolves] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨h_env, TContext.FindEq.refl _, fun _ => TContext.Equiv.refl _,
        Subst.absorbs_refl _ Env'.stateSubstInfo.isWF, rfl, ?_⟩
      intro i hi
      simp at hi
  | cons e rest ih =>
    obtain ⟨et, Env2, etsR, hr, hs, rfl⟩ := SourceExpr.resolves_cons_inv h
    have hwf2 : LExpr.TEnvWF (T := CoreLParams) Env2 :=
      SourceExpr.resolve_TEnvWF C Env Env2 e et hr h_env h_fac
    have hctx2 : TContext.FindEq (T := CoreLParams) Env2.context Env.context :=
      SourceExpr.resolve_context_FindEq C Env Env2 e et hr
    have heq2 : Env.context.types ≠ [] →
        TContext.Equiv (T := CoreLParams) Env2.context Env.context := fun hne =>
      SourceExpr.resolve_context_equiv_of_ne C Env Env2 e et hr hne
    have hne2 : Env.context.types ≠ [] → Env2.context.types ≠ [] := fun hne =>
      (heq2 hne).symm.types_ne_nil hne
    have habs2 : Subst.absorbs Env2.stateSubstInfo.subst Env.stateSubstInfo.subst :=
      resolveSource_absorbs e et C Env Env2 hr h_env h_fac
    obtain ⟨hwfR, hctxR, heqR, habsR, hlenR, hstepR⟩ := ih Env2 etsR hs hwf2
    refine ⟨hwfR, hctxR.trans hctx2, fun hne => (heqR (hne2 hne)).trans (heq2 hne),
      Subst.absorbs_trans _ _ _ habs2 habsR, by simp [hlenR], ?_⟩
    intro i hi hj
    match i with
    | 0 =>
      exact ⟨Env, Env2, hr, h_env, TContext.FindEq.refl _,
        fun hne => ⟨TContext.Equiv.refl _, hne⟩, habsR⟩
    | n + 1 =>
      obtain ⟨Ei, Ei', hri, hwfi, hctxi, heqi, habsi⟩ :=
        hstepR n (by simpa using hi) (by simpa using hj)
      exact ⟨Ei, Ei', by simpa using hri, hwfi, hctxi.trans hctx2,
        fun hne => (heqi (hne2 hne)).imp_left (·.trans (heq2 hne)), habsi⟩

/-- Instantiating context variables in a monomorphic scope keeps the environment and returns
    their stored types up to aliases and the solved substitution. -/
theorem Identifier.instantiateAndSubsts_inv (C : LContext CoreLParams) :
    ∀ (xs : List Expression.Ident) (Env Env' : TEnv Unit) (mtys : List LMonoTy),
      Lambda.Identifier.instantiateAndSubsts xs C Env = .ok (some (mtys, Env')) →
      MonoScope Env.context →
      Env' = Env ∧ mtys.length = xs.length ∧
        ∀ i (hi : i < xs.length) (hj : i < mtys.length),
          ∃ m0 r,
            Env.context.types.find? xs[i] = some (.forAll [] m0) ∧
            AliasEquiv Env.context.aliases m0 r ∧ r = Env.context.resolveTy m0 ∧
            mtys[i] = LMonoTy.subst Env.stateSubstInfo.subst r := by
  intro xs
  induction xs with
  | nil =>
    intro Env Env' mtys h _
    simp only [Lambda.Identifier.instantiateAndSubsts, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, ?_⟩
    intro i hi
    simp at hi
  | cons x rest ih =>
    intro Env Env' mtys h h_mono
    obtain ⟨xty, EnvA, mtysR, hhd, htail, rfl⟩ := Lambda.Identifier.instantiateAndSubsts_cons_inv h
    cases hfind : Env.context.types.find? x with
    | none =>
      simp only [Lambda.Identifier.instantiateAndSubst, hfind, pure, Except.pure] at hhd
      exact absurd hhd (by simp)
    | some ty =>
      obtain ⟨m0, rfl⟩ := MonoScope.find?_forAll h_mono hfind
      simp only [Lambda.Identifier.instantiateAndSubst, hfind, LTy.instantiateAndSubst,
        bind, Except.bind, pure, Except.pure] at hhd
      cases hi : LTy.instantiateWithCheck (.forAll [] m0) C Env with
      | error msg => rw [hi] at hhd; simp only [reduceCtorEq] at hhd
      | ok v =>
        obtain ⟨r, EnvR⟩ := v
        rw [hi] at hhd
        obtain ⟨hEnvR, hresolve, hae, -⟩ :=
          instantiateWithCheck_forAll_nil_env_eq C Env EnvR m0 r hi
        subst EnvR
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hhd
        obtain ⟨rfl, rfl⟩ := hhd
        obtain ⟨hEnvB, hlenR, hstepR⟩ := ih Env Env' mtysR htail h_mono
        subst Env'
        refine ⟨rfl, by simp [hlenR], ?_⟩
        intro i hi hj
        match i with
        | 0 =>
          exact ⟨m0, r, hfind, hae,
            TContext.resolveTy_of_resolveAliases (T := CoreLParams) hresolve, rfl⟩
        | n + 1 =>
          obtain ⟨m0', r', hf', hae', hr', hv'⟩ :=
            hstepR n (by simpa using hi) (by simpa using hj)
          exact ⟨m0', r', by simpa using hf', hae', hr', by simpa using hv'⟩

/-- Instantiating fresh signature names keeps the solved substitution. -/
private theorem instantiateEnv_stateSubstInfo
    (ids : List TyIdentifier) (mtys mtys' : LMonoTys)
    (Env Env' : TEnv Unit)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  unfold LMonoTys.instantiateEnv at h
  elim_err h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]

/-- Signature instantiation keeps the context and solved substitution and returns a renaming of
    the signature up to aliases. The renaming sends each type parameter to the type the
    parameters themselves instantiate to in the same environment. -/
theorem LMonoTySignature.instantiate_inv
    (C : LContext CoreLParams) (Env EnvR : TEnv Unit)
    (tyArgs : List TyIdentifier) (sig sig' : @LMonoTySignature Unit)
    (h : LMonoTySignature.instantiate C Env tyArgs sig = .ok (sig', EnvR)) :
    EnvR.context = Env.context ∧ EnvR.stateSubstInfo = Env.stateSubstInfo ∧
      Env.genEnv.genState.tyGen ≤ EnvR.genEnv.genState.tyGen ∧
      ∃ Sren : Subst,
        AliasEquivList Env.context.aliases
          (sig.values.map (LMonoTy.subst Sren)) sig'.values ∧
        (∀ x : TyIdentifier, ∃ y, LMonoTy.subst Sren (.ftvar x) = .ftvar y) ∧
        sig'.values = sig.values.map (fun t => Env.context.resolveTy (LMonoTy.subst Sren t)) ∧
        ∃ EnvJ, LMonoTys.instantiateEnv tyArgs (tyArgs.map LMonoTy.ftvar) Env
          = .ok (tyArgs.map (fun a => LMonoTy.subst Sren (.ftvar a)), EnvJ) := by
  obtain ⟨mtysI, EnvI0, hinst, hres0, -⟩ :=
    LMonoTySignature.instantiate_resolveAliases C Env EnvR tyArgs sig sig' h
  have hEnvR : EnvR = EnvI0 :=
    LMonoTys.resolveAliases_env_eq mtysI EnvI0 sig'.values EnvR hres0
  obtain ⟨Sren, EnvI, hren, hctxI, hres, -, hself⟩ :=
    LMonoTySignature.instantiate_resolveAliases_subst C Env EnvR tyArgs sig sig' h
  refine ⟨?_, ?_, ?_, Sren, ?_, hren, ?_, EnvI, hself⟩
  · rw [hEnvR]
    exact LExpr.LMonoTys.instantiateEnv_context tyArgs sig.values Env mtysI EnvI0 hinst
  · rw [hEnvR]
    exact instantiateEnv_stateSubstInfo tyArgs sig.values mtysI Env EnvI0 hinst
  · rw [hEnvR]
    exact LMonoTys.instantiateEnv_tyGen_mono tyArgs sig.values Env mtysI EnvI0 hinst
  · rw [← hctxI]
    exact (LMonoTys.resolveAliases_sourceTysResolve (T := CoreLParams)
      _ EnvI sig'.values EnvR hres).aliasEquiv
  · rw [TContext.resolveTys_of_resolveAliases (T := CoreLParams) hres, hctxI, List.map_map]
    rfl

/-- Advancing only the fresh-name counter preserves well-formedness. -/
theorem TEnvWF.of_sig_step
    (Env Env' : TEnv Unit)
    (hctx : Env'.context = Env.context)
    (hsubst : Env'.stateSubstInfo = Env.stateSubstInfo)
    (hgen : Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen)
    (h : LExpr.TEnvWF (T := CoreLParams) Env) :
    LExpr.TEnvWF (T := CoreLParams) Env' where
  aliasesWF := by rw [hctx]; exact h.aliasesWF
  substFreshForGen := by
    rw [hsubst]
    intro v hv n hn
    exact h.substFreshForGen v hv n (Nat.le_trans hgen hn)
  ctxFreshForGen := by
    rw [hctx]
    intro v hv n hn
    exact h.ctxFreshForGen v hv n (Nat.le_trans hgen hn)
  boundVarsNodup := by rw [hctx]; exact h.boundVarsNodup
  boundVarsFresh := by
    rw [hctx]
    intro y ty hy v hv n hn
    exact h.boundVarsFresh y ty hy v hv n (Nat.le_trans hgen hn)

/-- Linking annotations on an unannotated variable reference keeps the environment. -/
private theorem linkFVarAnnotations_fvar_none_env_eq
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (m : CoreLParams.Metadata) (x : Expression.Ident)
    (et : LExprT CoreLParams.mono)
    (h : SourceExpr.linkFVarAnnotations C (LExpr.fvar m x none) et Env = .ok Env') :
    Env' = Env := by
  cases et <;> simp_all only [SourceExpr.linkFVarAnnotations, reduceCtorEq]
  elim_err h
  simp only [Except.ok.injEq] at h
  exact h.symm

/-- Resolving a bare variable keeps the environment and returns its stored type up to aliases and
    the solved substitution. -/
theorem SourceExpr.resolve_fvar_none_inv
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (m : CoreLParams.Metadata) (x : Expression.Ident)
    (et : LExprT CoreLParams.mono) (m0 : LMonoTy)
    (h : SourceExpr.resolve C Env (LExpr.fvar m x none) = .ok (et, Env'))
    (hfind : Env.context.types.find? x = some (.forAll [] m0))
    (hne : Env.context.types ≠ []) :
    Env' = Env ∧ ∃ r,
      AliasEquiv Env.context.aliases m0 r ∧ r = Env.context.resolveTy m0 ∧
      et.toLMonoTy = LMonoTy.subst Env.stateSubstInfo.subst r := by
  have hsource := h
  obtain ⟨EnvR, hdirect, hlink⟩ :=
    SourceExpr.resolve_decompose C Env Env' (LExpr.fvar m x none) et hsource
  have hisEmpty : Env.context.types.isEmpty = false := by
    cases htypes : Env.context.types with
    | nil => exact absurd htypes hne
    | cons _ _ => rfl
  unfold LExpr.resolve at hdirect
  simp only [hisEmpty, Bool.false_eq_true, ite_false, bind, Except.bind] at hdirect
  rw [LExpr.resolveAux.eq_def (T := CoreLParams)] at hdirect
  simp only [LExpr.inferFVar, hfind, bind, Except.bind] at hdirect
  cases hi : LTy.instantiateWithCheck (.forAll [] m0) C Env with
  | error msg => rw [hi] at hdirect; simp only [reduceCtorEq] at hdirect
  | ok v =>
    obtain ⟨r, EnvA⟩ := v
    rw [hi] at hdirect
    obtain ⟨hEnvA, hresolve, hae, -⟩ := instantiateWithCheck_forAll_nil_env_eq C Env EnvA m0 r hi
    subst hEnvA
    simp only [Except.ok.injEq, Prod.mk.injEq] at hdirect
    obtain ⟨het, hEnvR⟩ := hdirect
    have hEnv' : Env' = EnvR :=
      linkFVarAnnotations_fvar_none_env_eq C EnvR Env' m x et hlink
    refine ⟨hEnv'.trans hEnvR.symm, r, hae,
      TContext.resolveTy_of_resolveAliases (T := CoreLParams) hresolve, ?_⟩
    rw [← het, LExpr.applySubstT_toLMonoTy]
    rfl

/-- Substituting a type whose variables all lie in `L` by the map sending each variable of `L`
    to its image under a renaming `Sren` and then `S` agrees with applying `Sren` and then `S`. -/
theorem LMonoTy.subst_ofScopes_rename_eq (S Sren : Subst) (L : List TyIdentifier) (ty : LMonoTy)
    (hty : ∀ v, v ∈ LMonoTy.freeVars ty → v ∈ L) :
    LMonoTy.subst (Strata.Util.HMaps.ofScopes
        [L.map (fun v => (v, LMonoTy.subst S (LMonoTy.subst Sren (.ftvar v))))]) ty
      = LMonoTy.subst S (LMonoTy.subst Sren ty) := by
  refine (LMonoTy.subst_subst_of_pointwise Sren S _ ty fun x hx => ?_).symm
  refine (LMonoTy.subst_ftvar_of_some ?_).symm
  show Strata.Util.HMaps.find? [Strata.Util.HMap.ofList _] x = _
  rw [Strata.Util.HMaps.find?_single_scope]
  exact Strata.Util.HMap.find?_ofList_self_map _
    (fun v => LMonoTy.subst S (LMonoTy.subst Sren (.ftvar v))) x (hty x hx)

/-- For a checked call and any `S` absorbing the unifier's solution, `S` fixes the substitution
    of the signature instantiation, the instantiated signature has one type per parameter, and
    argument and result types match the instantiated parameter types under `S`. -/
theorem call_sig_unify_facts
    (Env Env_sig Env_res : TEnv Unit) (Suni : SubstInfo) (S Sren : Subst) (proc : Procedure)
    (io_sig : @LMonoTySignature Unit) (argsa : List (LExprT CoreLParams.mono))
    (lhs_tys : LMonoTys)
    (hsigSub : Env_sig.stateSubstInfo = Env.stateSubstInfo)
    (hsigAE : AliasEquivList Env.context.aliases
      ((proc.header.inputs ++ proc.header.outputs).values.map (LMonoTy.subst Sren))
      io_sig.values)
    (hresAbs : Subst.absorbs Env_res.stateSubstInfo.subst Env_sig.stateSubstInfo.subst)
    (huni : Constraints.unify
      ((argsa.map LExpr.toLMonoTy).zip
          ((LMonoTys.subst Env_sig.stateSubstInfo.subst io_sig.values).take
            proc.header.inputs.length) ++
        lhs_tys.zip
          ((LMonoTys.subst Env_sig.stateSubstInfo.subst io_sig.values).drop
            proc.header.inputs.length))
      Env_res.stateSubstInfo = .ok Suni)
    (h_absorbs : Subst.absorbs S Suni.subst) :
    (∀ t, LMonoTy.subst S (LMonoTy.subst Env.stateSubstInfo.subst t) = LMonoTy.subst S t) ∧
    io_sig.values.length = proc.header.inputs.length + proc.header.outputs.length ∧
    (∀ i t u, i < proc.header.inputs.length →
      (argsa.map LExpr.toLMonoTy)[i]? = some t → io_sig.values[i]? = some u →
      LMonoTy.subst S t = LMonoTy.subst S u) ∧
    (∀ j t u, j < proc.header.outputs.length → lhs_tys[j]? = some t →
      io_sig.values[proc.header.inputs.length + j]? = some u →
      LMonoTy.subst S t = LMonoTy.subst S u) := by
  have habsSig : Subst.absorbs S Env_sig.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ hresAbs
      (Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ huni) h_absorbs)
  have hkillSig : ∀ t,
      LMonoTy.subst S (LMonoTy.subst Env_sig.stateSubstInfo.subst t) = LMonoTy.subst S t :=
    fun t => LMonoTy.subst_absorbs S _ t habsSig
  have hvals : (proc.header.inputs ++ proc.header.outputs).values
      = proc.header.inputs.values ++ proc.header.outputs.values :=
    ListMap.values_append _ _
  have hsound := Constraints.unify_sound _ _ _ huni
  have hconstr : ∀ t u, (t, LMonoTy.subst Env_sig.stateSubstInfo.subst u) ∈
      (argsa.map LExpr.toLMonoTy).zip
          ((LMonoTys.subst Env_sig.stateSubstInfo.subst io_sig.values).take
            proc.header.inputs.length) ++
        lhs_tys.zip
          ((LMonoTys.subst Env_sig.stateSubstInfo.subst io_sig.values).drop
            proc.header.inputs.length) →
      LMonoTy.subst S t = LMonoTy.subst S u := by
    intro t u hmem
    rw [LMonoTy.subst_eq_of_absorbs S Suni.subst t _ h_absorbs (hsound _ hmem), hkillSig]
  have hio : ∀ (k : Nat) (u : LMonoTy), io_sig.values[k]? = some u →
      (LMonoTys.subst Env_sig.stateSubstInfo.subst io_sig.values)[k]?
        = some (LMonoTy.subst Env_sig.stateSubstInfo.subst u) := by
    intro k u hu
    rw [LMonoTys.subst_eq_map, List.getElem?_map, hu, Option.map_some]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hsigSub]
    exact hkillSig
  · have hl := hsigAE.length_eq
    rw [List.length_map, hvals, List.length_append, ListMap.values_length,
      ListMap.values_length] at hl
    exact hl.symm
  · intro i t u hi ht hu
    refine hconstr t u (List.mem_append_left _
      (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨ht, ?_⟩)))
    rw [List.getElem?_take, ite_eq_left hi]
    exact hio _ u hu
  · intro j t u hj ht hu
    refine hconstr t u (List.mem_append_right _
      (List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨ht, ?_⟩)))
    rw [List.getElem?_drop]
    exact hio _ u hu

/-- A successful `call` run, with a well-formed `S` that absorbs the final substitution, is typed
    by the spec in the `S`-applied scope and ends in a scope with the same lookups as the
    checker's. -/
private theorem Statement.typeCheckCmd_sound_absorbing_call
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (nm : String)
    (tyArgs : Option (List Expression.Ty)) (callArgs : List (CallArg Expression))
    (md : MetaData Expression) (c' : Command) (S : Subst)
    (run : CmdRun C Env P (.call nm tyArgs callArgs md) c' Env')
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_stored : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S c') = true)
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (h_wf : SubstWF S) :
    ∃ Γ', CmdExtHasType C P (substEnv S)
        (TContext.subst Env.context S) (.call nm tyArgs callArgs md) Γ' (substEnv S) ∧
      TContext.FindEq (T := CoreLParams) Γ'
        (TContext.subst Env'.context S) := by
  cases run with
  | @call _ _ _ _ proc lhs_tys io_sig argsa EnvLhs Env_sig Env_res Suni
      instTys EnvA hproc hlhsSome hwf hlhs hsig hres huni hargs =>
    have hargsLen := (hwf.argsMatch hproc).inputCount
    obtain ⟨hEnvLhs, hlhsTysLen, hlhsStep⟩ :=
      Identifier.instantiateAndSubsts_inv C _ Env EnvLhs lhs_tys hlhs h_mono
    subst EnvLhs
    obtain ⟨hsigCtx, hsigSub, hsigGen, Sren, hsigAE, -, -⟩ :=
      LMonoTySignature.instantiate_inv C Env Env_sig proc.header.typeArgs
        (proc.header.inputs ++ proc.header.outputs) io_sig hsig
    have hsigWF : LExpr.TEnvWF (T := CoreLParams) Env_sig :=
      TEnvWF.of_sig_step Env Env_sig hsigCtx hsigSub hsigGen h_env
    obtain ⟨-, hresCtx, -, hresAbs, hresLen, hresStep⟩ :=
      SourceExpr.resolves_step C Env_sig Env_res (CallArg.getInputExprs callArgs) argsa hres
        hsigWF h_fac
    have hsigFind : TContext.FindEq (T := CoreLParams) Env_sig.context Env.context := by
      rw [hsigCtx]
    have habsRes : Subst.absorbs S Env_res.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _
        (Constraints.unify_absorbs _ _ _ huni) h_absorbs
    have hargsaLen : argsa.length = proc.header.inputs.length := by
      rw [hresLen, hargsLen]
    let σ : List (TyIdentifier × LMonoTy) :=
      (LMonoTys.freeVars
        (proc.header.inputs.values ++ proc.header.outputs.values)).map
          (fun v => (v, LMonoTy.subst S (LMonoTy.subst Sren (.ftvar v))))
    obtain ⟨hkill, hiolen, hinpEq, hretEq⟩ :=
      call_sig_unify_facts Env Env_sig Env_res Suni S Sren proc io_sig argsa lhs_tys
        hsigSub hsigAE hresAbs huni h_absorbs
    have hinLen : proc.header.inputs.values.length = proc.header.inputs.length :=
      ListMap.values_length _
    have houtLen : proc.header.outputs.values.length = proc.header.outputs.length :=
      ListMap.values_length _
    have hkey := LMonoTy.subst_ofScopes_rename_eq S Sren
    have hbridge := AliasEquivList_rename_subst_getElem Env.context.aliases h_env.aliasesWF
      Sren S _ _
      ((ListMap.values_append proc.header.inputs proc.header.outputs).symm ▸ hsigAE)
    refine ⟨TContext.subst Env.context S, ?_, ?_⟩
    · refine CmdExtHasType.call (substEnv S)
        (TContext.subst Env.context S) nm tyArgs callArgs proc md
        σ _ hproc hwf ?_ ?_ ?_ (fun _ _ => annotsInScope_substEnv _ _ _) ?_
        (TContext.Equiv.refl _)
      · intro v hv
        simp only [TContext.subst, TContext.types.subst,
          Strata.Util.HMaps.find?_mapValues, Option.isSome_map]
        exact hlhsSome v hv
      · intro i hi hj
        have hiIn : i < proc.header.inputs.length := by rw [← hinLen]; exact hj
        have hai : i < argsa.length := by omega
        have hii : i < io_sig.values.length := by omega
        have happ : i <
            (proc.header.inputs.values ++ proc.header.outputs.values).length := by
          rw [List.length_append]
          omega
        have happL :
            (proc.header.inputs.values ++ proc.header.outputs.values)[i]
              = proc.header.inputs.values[i] := by
          refine (List.getElem_eq_iff happ).mpr ?_
          rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
        have hkeyIn :
            LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])
                proc.header.inputs.values[i]
              = LMonoTy.subst S
                  (LMonoTy.subst Sren proc.header.inputs.values[i]) :=
          hkey _ _ (fun _ hv =>
            LMonoTys.freeVars_mem_subset (List.mem_append_left _ (List.getElem_mem hj)) hv)
        have hbr : AliasEquiv Env.context.aliases
            (LMonoTy.subst S (LMonoTy.subst Sren proc.header.inputs.values[i]))
            (LMonoTy.subst S io_sig.values[i]) := by
          have hb := hbridge i happ hii
          rwa [happL] at hb
        have hsame :
            LMonoTy.subst S argsa[i].toLMonoTy
              = LMonoTy.subst S io_sig.values[i] := by
          refine hinpEq i _ _ hiIn ?_ (List.getElem?_eq_getElem hii)
          rw [List.getElem?_map, List.getElem?_eq_getElem hai, Option.map_some]
        have hiSrc : i < (CallArg.getInputExprs callArgs).length := hi
        obtain ⟨Ei, Ei', hri, hwfi, hctxi, -, habsi⟩ :=
          hresStep i hiSrc hai
        have hctxiEnv : TContext.FindEq (T := CoreLParams) Ei.context Env.context :=
          hctxi.trans hsigFind
        have hscopei : LExpr.WellScoped (CallArg.getInputExprs callArgs)[i]
            Ei.context :=
          SourceExpr.resolve_WellScoped C Ei Ei' _ argsa[i] hri
        have hscope0 : LExpr.WellScoped (CallArg.getInputExprs callArgs)[i]
            Env.context :=
          WellScoped.of_FindEq hctxiEnv.symm hscopei
        have hmonoi : MonoScope Ei.context := MonoScope_of_findEq hctxiEnv h_mono
        have habsiS : Subst.absorbs S Ei'.stateSubstInfo.subst :=
          Subst.absorbs_trans _ _ _ habsi habsRes
        split
        · rename_i mm x harg
          have hxknown : x ∈ Env.context.knownVars := by
            exact hscope0 (x, none) (by simp [harg, LExpr.freeVars])
          obtain ⟨xty, hfind⟩ :=
            (Strata.Util.HMaps.mem_keys_iff_find? Env.context.types x).mp hxknown
          obtain ⟨m0, rfl⟩ := MonoScope.find?_forAll h_mono hfind
          have hfindEi : Ei.context.types.find? x = some (.forAll [] m0) := by
            rw [hctxiEnv.find? x]
            exact hfind
          have hneEi : Ei.context.types ≠ [] := by
            intro hnil
            rw [hnil] at hfindEi
            simp [Strata.Util.HMaps.find?] at hfindEi
          rw [harg] at hri
          obtain ⟨hEi', r, hae, -, htyr⟩ :=
            SourceExpr.resolve_fvar_none_inv C Ei Ei' mm x argsa[i] m0
              hri hfindEi hneEi
          subst Ei'
          have habsEi : Subst.absorbs S Ei.stateSubstInfo.subst :=
            habsiS
          have haliasIn : ∀ a ∈ Ei.context.aliases, a ∈ Env.context.aliases := by
            intro a ha
            rwa [hctxiEnv.2] at ha
          refine ⟨LMonoTy.subst S m0, ?_, ?_⟩
          · change AliasEquiv _ _ _
            rw [TContext.subst_aliases, hkeyIn]
            refine AliasEquiv.trans ?_ (LExpr.AliasEquiv.symm hbr)
            rw [← hsame, htyr, LMonoTy.subst_absorbs S _ r habsEi,
              ← hctxiEnv.2]
            exact LExpr.AliasEquiv_subst Ei.context.aliases m0 r S hae
              (fun a ha => h_env.aliasesWF a (haliasIn a ha))
          · exact TContext_types_subst_find _ _ _ _ hfind
        · rename_i hnotfv
          have hBi : BinderAnnotsKnown C (LExpr.applyTypeSubst (LExpr.unresolved argsa[i]) S) := by
            have hnewLen : (argsa.map LExpr.unresolved).length
                = (CallArg.getInputExprs callArgs).length := by
              rw [List.length_map]
              omega
            rcases CallArg.getInputExprs_replaceInArgs_getElem? callArgs
                (argsa.map LExpr.unresolved) hnewLen i with hA | ⟨idb, hB1, -⟩
            · have hget : (CallArg.getInputExprs
                  (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)))[i]?
                  = some (LExpr.unresolved argsa[i]) := by
                rw [hA, List.getElem?_map, List.getElem?_eq_getElem hai, Option.map_some]
              exact binderAnnotsKnown_of_call_inputs C S nm _ _ md h_stored _
                (List.mem_of_getElem? hget)
            · rw [List.getElem?_eq_getElem hiSrc, Option.some.injEq] at hB1
              exact absurd hB1 (hnotfv Core.coreLoc idb)
          have hANi : ∀ al ∈ Ei.context.aliases, C.knownTypes.containsName al.name = false := by
            intro al hal
            rw [hctxiEnv.2] at hal
            exact h_aliasNames al hal
          have htypedEi :=
            SourceExpr.resolve_HasType_instAnnots C Ei Ei'
              (CallArg.getInputExprs callArgs)[i] argsa[i] hri hscopei hwfi h_fac
              hmonoi hANi S habsiS h_wf hBi
          have htyped :
              LExpr.HasType C (TContext.subst Env.context S)
                (instAnnots (substEnv S) (CallArg.getInputExprs callArgs)[i])
                (.forAll [] (LMonoTy.subst S argsa[i].toLMonoTy)) :=
            HasType_FindEq C _ _ _ _
              (TContext.FindEq.subst_subst S hctxiEnv).symm htypedEi
          have hgeneral :
              ∃ mty,
                AliasEquiv (TContext.subst Env.context S).aliases mty
                  (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])
                    proc.header.inputs.values[i]) ∧
                LExpr.HasType C (TContext.subst Env.context S)
                  (instAnnots (substEnv S) (CallArg.getInputExprs callArgs)[i])
                  (.forAll [] mty) := by
            refine ⟨LMonoTy.subst S argsa[i].toLMonoTy, ?_, htyped⟩
            rw [TContext.subst_aliases, hkeyIn, hsame]
            exact LExpr.AliasEquiv.symm hbr
          exact hgeneral
      · intro e he
        obtain ⟨i, hiSrc, rfl⟩ := List.getElem_of_mem he
        have hai : i < argsa.length := by omega
        obtain ⟨Ei, Ei', hri, -, hctxi, -, -⟩ := hresStep i hiSrc hai
        exact writtenAnnotsOk_of_aliases_eq
          (TContext.FindEq.subst_subst S (hctxi.trans hsigFind)).symm.aliases
          (resolveSource_writtenAnnotsOk C Ei Ei' _ argsa[i] hri S)
      · intro j hj hj2
        have hjc : j < (CallArg.getLhs callArgs).length := hj
        have hjOut : j < proc.header.outputs.length := by rw [← houtLen]; exact hj2
        have hlv : j < lhs_tys.length := by rw [hlhsTysLen]; exact hjc
        have hii : proc.header.inputs.length + j < io_sig.values.length := by omega
        have happ : proc.header.inputs.length + j
            < (proc.header.inputs.values ++ proc.header.outputs.values).length := by
          rw [List.length_append]
          omega
        have happR :
            (proc.header.inputs.values ++ proc.header.outputs.values)[
              proc.header.inputs.length + j] = proc.header.outputs.values[j] := by
          refine (List.getElem_eq_iff happ).mpr ?_
          have hidx : proc.header.inputs.length + j - proc.header.inputs.values.length = j := by
            omega
          rw [List.getElem?_append_right (by omega), hidx, List.getElem?_eq_getElem hj2]
        obtain ⟨m0, r, hfind, hae, -, hval⟩ := hlhsStep j hjc hlv
        have hkeyOut :
            LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])
                proc.header.outputs.values[j]
              = LMonoTy.subst S
                  (LMonoTy.subst Sren proc.header.outputs.values[j]) :=
          hkey _ _ (fun _ hv =>
            LMonoTys.freeVars_mem_subset (List.mem_append_right _ (List.getElem_mem hj2)) hv)
        have hbr : AliasEquiv Env.context.aliases
            (LMonoTy.subst S (LMonoTy.subst Sren proc.header.outputs.values[j]))
            (LMonoTy.subst S
              io_sig.values[proc.header.inputs.length + j]) := by
          have hb := hbridge (proc.header.inputs.length + j) happ hii
          rwa [happR] at hb
        have hsame :
            LMonoTy.subst S lhs_tys[j]
              = LMonoTy.subst S
                io_sig.values[proc.header.inputs.length + j] :=
          hretEq j _ _ hjOut (List.getElem?_eq_getElem hlv)
            (List.getElem?_eq_getElem hii)
        refine ⟨LMonoTy.subst S m0, ?_, ?_⟩
        · change AliasEquiv _ _ _
          rw [TContext.subst_aliases, hkeyOut]
          refine AliasEquiv.trans ?_ (LExpr.AliasEquiv.symm hbr)
          rw [← hsame, hval, hkill]
          exact LExpr.AliasEquiv_subst Env.context.aliases m0 r S hae
            h_env.aliasesWF
        · exact TContext_types_subst_find _ _ _ _ hfind
    · change TContext.FindEq (T := CoreLParams) (TContext.subst Env.context S)
        (TContext.subst Env_res.context S)
      exact (TContext.FindEq.subst_subst S (hresCtx.trans hsigFind)).symm

/-- Input soundness: under any well-formed `S` absorbing the output substitution and fixing the
    rigid type variables, an accepted command, as written, satisfies the typechecker spec with
    written type variables read via `S`. -/
theorem Statement.typeCheckCmd_sound_absorbing
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (S : Subst)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_stored : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S c') = true)
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (h_wf : SubstWF S)
    (hfix : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst S (.ftvar v) = .ftvar v) :
    ∃ Γ', CmdExtHasType C P (substEnv S)
        (TContext.subst Env.context S) c Γ' (substEnv S) ∧
      TContext.FindEq (T := CoreLParams) Γ'
        (TContext.subst Env'.context S) := by
  have hrun := Statement.typeCheckCmd_ok_inv h
  cases c with
  | call nm tyArgs callArgs md =>
    exact Statement.typeCheckCmd_sound_absorbing_call C Env Env' P nm tyArgs callArgs md c' S
      hrun h_env h_fac h_mono h_aliasNames h_stored h_absorbs h_wf
  | cmd cc =>
    cases hrun with
    | @cmd _ cc' Env' run =>
      obtain ⟨Δ', hcmd, hfind⟩ :=
        imperativeCmd_sound C Env Env' cc cc' S run h_env h_fac h_mono
          h_aliasNames h_stored h_absorbs h_wf hfix
      exact ⟨Δ', CmdExtHasType.cmd (P := P) _ _ _ _ _ hcmd, hfind⟩

/-- Input soundness at the checker's own solution: an accepted command, as written, satisfies the
    typechecker spec with written type variables read via the output substitution, in the
    substituted input context, when that substitution fixes the rigid type variables. -/
theorem Statement.typeCheckCmd_sound
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_stored : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst Env'.stateSubstInfo.subst c') = true)
    (hfix : ∀ v ∈ C.rigidTypeVars, LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v) :
    ∃ Γ', CmdExtHasType C P (substEnv Env'.stateSubstInfo.subst)
        (TContext.subst Env.context Env'.stateSubstInfo.subst) c Γ'
        (substEnv Env'.stateSubstInfo.subst) ∧
      TContext.FindEq (T := CoreLParams) Γ'
        (TContext.subst Env'.context Env'.stateSubstInfo.subst) :=
  Statement.typeCheckCmd_sound_absorbing C Env Env' P c c'
    Env'.stateSubstInfo.subst h h_env h_fac h_mono h_aliasNames
    h_stored
    (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF) Env'.stateSubstInfo.isWF hfix

/-! ### Source resolution and local-declaration facts -/

/-- A successfully resolved source expression is well typed according to its stored annotations. -/
theorem resolveSource_HasTypeA
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (h : SourceExpr.resolve C Env e = .ok (et, Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context) :
    LExpr.HasTypeA [] et.unresolved et.toLMonoTy := by
  obtain ⟨EnvR, hresolve, -⟩ := SourceExpr.resolve_decompose C Env Env' e et h
  exact Lambda.resolve_HasTypeA e et C Env EnvR hresolve he hf hr

/-- Under any substitution `S` absorbing the final one, a resolved source expression agrees with
    the alias-resolved input scope under `S` and a table whose signatures name no input alias. -/
private theorem resolveSource_annotAgree
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (h : SourceExpr.resolve C Env e = .ok (et, Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hmono : MonoScope Env.context) (hsig : FactorySigsFixed Env.context.aliases C.functions)
    (S : Subst) (habs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    TypeSpec.ScopesAnnotAgree C (TContext.subst Env.context.resolveTypes S).types
      (LExpr.unresolved (LExpr.applySubstT et S)) := by
  obtain ⟨EnvDirect, hres, hlink⟩ := SourceExpr.resolve_link_absorbs C Env Env' e et h
  exact resolve_annotAgree C Env EnvDirect e et hres he hf hmono hsig S
    (Subst.absorbs_trans _ _ _ hlink habs)

/-- Under any substitution `S` absorbing the final one, a resolved source expression with `S`
    applied to its annotations agrees with the substituted alias-free form of any scope with the
    input scope's lookups, when the table's signatures are fixed for the input aliases. -/
theorem resolveSource_annotAgree_dealias
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (h : SourceExpr.resolve C Env e = .ok (et, Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hmono : MonoScope Env.context) (hsig : FactorySigsFixed Env.context.aliases C.functions)
    {Γ : TContext Unit} (hΓ : TContext.FindEq (T := CoreLParams) Γ Env.context)
    (S : Subst) (habs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    TypeSpec.ScopesAnnotAgree C (TContext.subst Γ.dealias S).types
      (LExpr.applyTypeSubst (LExpr.unresolved et) S) := by
  have ha := TypeSpec.ScopesAnnotAgree.applyTypeSubst_unresolved et S
    (resolveSource_annotAgree e et C Env Env' h he hf hmono hsig S habs)
  exact TypeSpec.ScopesAnnotAgree.of_find? (Γ := TContext.subst Env.context.resolveTypes S)
    (TContext.FindEq.subst_subst S hΓ.dealias).find? ha

/-- Every free variable of a resolved expression is known in the input environment. -/
theorem resolveSource_getVars_mem_knownVars
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (h : SourceExpr.resolve C Env e = .ok (et, Env')) :
    ∀ id ∈ LExpr.LExpr.getVars et, id ∈ TContext.knownVars Env.context := by
  obtain ⟨EnvR, hresolve, -⟩ := SourceExpr.resolve_decompose C Env Env' e et h
  exact Lambda.LExpr.Proofs.resolve_getVars_mem_knownVars C Env EnvR e et hresolve

/-- Adding a local declaration gives a nonempty scope stack. -/
private theorem CmdType.update_context_types_ne
    (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    (CmdType.update Env x ty).context.types ≠ [] := by
  simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
  cases Env.genEnv.context.types with
  | nil | cons _ _ =>
    simp only [Strata.Util.HMaps.addInNewest]
    exact List.cons_ne_nil _ _

/-! ## Procedure signatures resolved against aliases -/

/-- Scanning resolved declarations finds the resolution of what scanning the declarations
    finds. -/
private theorem find?_go_resolveSig (Γ : TContext Unit) (k : DeclKind) (x : Expression.Ident) :
    ∀ ds : Decls, Program.find?.go k x (ds.map (Decl.resolveSig Γ))
      = (Program.find?.go k x ds).map (Decl.resolveSig Γ) := by
  intro ds
  induction ds with
  | nil => simp only [List.map_nil, Program.find?_go_nil, Option.map_none]
  | cons d ds ih =>
    rw [List.map_cons, Program.find?_go_cons, Program.find?_go_cons, Decl.resolveSig_kind,
      Decl.resolveSig_name]
    split
    · rfl
    · exact ih

/-- Looking up a procedure of the resolved program finds the resolution of the program's. -/
theorem Program.resolveSigs_find? (A : List TypeAlias) (P : Program) (x : Expression.Ident) :
    Program.Procedure.find? (P.resolveSigs A) x
      = (Program.Procedure.find? P x).map (Procedure.resolveSig { aliases := A }) := by
  rw [Program.Procedure.find?_eq_go, Program.Procedure.find?_eq_go]
  simp only [Program.resolveSigs]
  rw [find?_go_resolveSig]
  cases Program.find?.go DeclKind.proc x P.decls with
  | none => rfl
  | some d => cases d <;> rfl

/-- `q2` has `q1`'s type parameters and parameter names, and `q1`'s parameter types
    alias-resolved against `A`. -/
structure ProcSigResolved (A : List TypeAlias) (q1 q2 : Procedure) : Prop where
  typeArgs : q1.header.typeArgs = q2.header.typeArgs
  inputsKeys  : q1.header.inputs.keys  = q2.header.inputs.keys
  outputsKeys : q1.header.outputs.keys = q2.header.outputs.keys
  inputsVals  : q2.header.inputs.values
    = q1.header.inputs.values.map ({ aliases := A } : TContext Unit).resolveTy
  outputsVals : q2.header.outputs.values
    = q1.header.outputs.values.map ({ aliases := A } : TContext Unit).resolveTy

/-- A procedure whose parameter types are the alias resolutions of another's agrees with it up to
    those aliases. -/
theorem ProcSigResolved.sigAgree {A : List TypeAlias} {q1 q2 : Procedure}
    (h : ProcSigResolved A q1 q2) : ProcSigAgree A q1 q2 := by
  refine ⟨h.inputsKeys, h.outputsKeys, ?_, ?_⟩
  · rw [h.inputsVals]
    exact AliasEquivList.map_resolveTy (T := CoreLParams) { aliases := A } _
  · rw [h.outputsVals]
    exact AliasEquivList.map_resolveTy (T := CoreLParams) { aliases := A } _

/-- When a call checks, some renaming of the callee's type variables turns its declared parameter
    types into types whose alias resolution at the call site's context is registered. -/
theorem Statement.typeCheckCmd_call_sigResolved
    (C : Expression.TyContext) (Env : Expression.TyEnv) (program : Program)
    (nm : String) (callArgs : List (CallArg Expression)) (mdc : MetaData Expression)
    {tyArgs : Option (List Expression.Ty)}
    (rc : Command × Expression.TyEnv) (proc : Procedure)
    (h : Statement.typeCheckCmd C Env program (.call nm tyArgs callArgs mdc) = .ok rc)
    (hfind : Program.Procedure.find? program nm = some proc) :
    ∃ (S : Subst) (EnvI EnvR : Expression.TyEnv) (rtys : LMonoTys),
      (∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
      EnvI.context = Env.context ∧
      LMonoTys.resolveAliases
          ((proc.header.inputs.values ++ proc.header.outputs.values).map (LMonoTy.subst S))
          EnvI = .ok (rtys, EnvR) ∧
      ∀ mty ∈ rtys, isInstanceOfKnownType mty C = true := by
  obtain ⟨c', Env'⟩ := rc
  cases Statement.typeCheckCmd_ok_inv h with
  | @call _ _ _ _ found lhsTys ioSig argsa Envlhs EnvSig EnvRes Suni
      instTys EnvA hpf hlhsSome hwf hlhs hsig hres hunify hargs =>
    rw [hfind, Option.some.injEq] at hpf
    subst found
    have hctxlhs : Envlhs.context = Env.context :=
      Identifier.instantiateAndSubsts_context _ C Env lhsTys Envlhs hlhs
    obtain ⟨S, EnvI, hSftvar, hctxI, hresolve, hknown, -⟩ :=
      LMonoTySignature.instantiate_resolveAliases_subst C Envlhs EnvSig
        proc.header.typeArgs (proc.header.inputs ++ proc.header.outputs) ioSig hsig
    refine ⟨S, EnvI, EnvSig, ioSig.values, hSftvar, hctxI.trans hctxlhs, ?_, hknown⟩
    rw [← ListMap.values_append]
    exact hresolve

/-! ## Alias preservation -/

/-- Typing an extended command with written type variables in scope preserves the alias list. -/
theorem TypeSpec.CmdExtHasType.aliases_eq
    {C : LContext CoreLParams} {P : Program} {Δ Δ' : WrittenEnv} {Γ Γ' : TContext Unit}
    {c : Command} (h : CmdExtHasType C P Δ Γ c Γ' Δ') : Γ'.aliases = Γ.aliases := by
  cases h with
  | cmd _ _ _ hcmd => cases hcmd <;> rename_i hEqv <;> exact hEqv.2
  | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEqv => exact hEqv.2

/-! ## Deskolemization relations -/

/-- `Γ'` deskolemizes `Γ` over `σ`: same aliases, and every stored scheme deskolemized. -/
@[expose] def DeskolemizesScope (σ : RigidNames) (Γ Γ' : TContext Unit) : Prop :=
  Γ'.aliases = Γ.aliases ∧
  ∀ x, Γ'.types.find? x = (Γ.types.find? x).map (mapLTyTys (deskolemizeTy σ))

/-- `DeskolemizesScope` respects lookup equivalence on the source side. -/
theorem DeskolemizesScope.of_equiv_left (σ : RigidNames) (Γ₀ Γ Γ' : TContext Unit)
    (heq : TContext.Equiv (T := CoreLParams) Γ₀ Γ)
    (h : DeskolemizesScope σ Γ Γ') : DeskolemizesScope σ Γ₀ Γ' := by
  obtain ⟨halias, hfind⟩ := h
  refine ⟨by rw [halias, heq.toFindEq.2], fun x => ?_⟩
  rw [hfind x, ← heq.toFindEq.find? x]

/-- Inserting corresponding monomorphic bindings preserves scope deskolemization. -/
theorem DeskolemizesScope.insert (σ : RigidNames) (Γ Γ' : TContext Unit)
    (h : DeskolemizesScope σ Γ Γ') (x : Identifier Unit) (mty : LMonoTy) :
    DeskolemizesScope σ
      { Γ with types := Γ.types.insert x (.forAll [] mty) }
      { Γ' with types := Γ'.types.insert x (.forAll [] (deskolemizeTy σ mty)) } := by
  refine ⟨h.1, fun y => ?_⟩
  by_cases hy : y = x
  · subst y
    rw [Strata.Util.HMaps.find?_insert_self, Strata.Util.HMaps.find?_insert_self]
    simp only [Option.map_some, mapLTyTys]
  · rw [Strata.Util.HMaps.find?_insert_ne _ _ _ _ hy,
      Strata.Util.HMaps.find?_insert_ne _ _ _ _ hy, h.2 y]

/-- `Csk` is `Crig` skolemized by `σ`: the same type lookups once `σ`'s constants are added to
    `Crig`, the same rigid type parameters, and deskolemized function signatures. -/
structure AmbientDeskol (σ : RigidNames) (Csk Crig : LContext CoreLParams) : Prop where
  knownTypes_eq : ∀ x : String, Csk.knownTypes[x]? = (addSkolemTypes Crig σ).knownTypes[x]?
  rigidTypeVars_eq : Csk.rigidTypeVars = Crig.rigidTypeVars
  functions_deskol : FactorySigDeskolemizes σ Csk.functions Crig.functions

/-- Deskolemizing an expression, its type scope and its ambient context keeps annotation
    agreement, when every signature is well formed and safe to deskolemize. -/
theorem TypeSpec.ScopesAnnotAgree.deskolemize {σ : RigidNames} {Csk Crig : LContext CoreLParams}
    {Γ Γ' : TContext Unit}
    (hamb : AmbientDeskol σ Csk Crig) (hsc : DeskolemizesScope σ Γ Γ')
    (hwf : FactorySigWF (T := CoreLParams) Csk.functions)
    (hsafe : FactorySigDeskolSafe σ Csk.functions)
    {e : Expression.Expr} (ha : TypeSpec.ScopesAnnotAgree Csk Γ.types e) :
    TypeSpec.ScopesAnnotAgree Crig Γ'.types (mapExprTys (deskolemizeTy σ) e) := by
  refine ⟨fun x ann hx => ?_, fun o ty ho => ?_, fun o ho => ?_⟩
  · simp only [mapExprTys, LExpr.freeVars_replaceUserProvidedType] at hx
    obtain ⟨⟨y, oty⟩, hmem, heq⟩ := List.mem_map.mp hx
    cases oty with
    | none => simp at heq
    | some ann0 =>
      simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [hsc.2 y, ha.fvarsDeclared y ann0 hmem]
      rfl
  · simp only [mapExprTys, LExpr.opAnnots_replaceUserProvidedType] at ho
    obtain ⟨⟨o0, ty0⟩, hmem, heq⟩ := List.mem_map.mp ho
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨f, xs, body, hf, hty, τ, rfl⟩ := ha.opsInstantiate o0 ty0 hmem
    obtain ⟨f', hf', hty'⟩ := hamb.functions_deskol.find_type o0.name f _ hf hty
    have hsafeB : deskolemizeTy σ body = body ∨
        ∀ v ∈ LMonoTy.freeVars body, v ∉ σ.map Prod.fst := by
      rcases hsafe o0.name f _ hf hty with hfix | hdisj
      · simp only [mapLTyTys, LTy.forAll.injEq, true_and] at hfix
        exact Or.inl hfix
      · have hclosed := (factory_type_nodup_closed (C := Csk) hwf hf hty).2
        exact Or.inr fun v hv hvσ => hdisj (hclosed v hv) hvσ
    obtain ⟨τ', hτ'⟩ := deskolemizeTy_subst_instance σ τ _ hsafeB
    refine ⟨f', xs, deskolemizeTy σ body, hf', ?_, τ', hτ'⟩
    rw [hty']
    rfl
  · simp only [mapExprTys, LExpr.getOps_replaceUserProvidedType] at ho
    rw [← (hamb.functions_deskol o.name).1]
    exact ha.opsKnown o ho

/-! ## Called procedure signatures fixed by deskolemizing -/

/-- Every procedure named by a command has a signature that deskolemizing by `σ` fixes. -/
def CalledProcedureSignaturesFixed (σ : RigidNames) (P : Program) (c : Command) : Prop :=
  ∀ pname ∈ CmdExt.calledProcedureNames c, ∀ proc,
    Program.Procedure.find? P pname = some proc →
      ∀ ty ∈ proc.header.inputs.values ++ proc.header.outputs.values, deskolemizeTy σ ty = ty

/-- Signatures fixed by deskolemizing stay fixed once resolved against aliases whose bodies and
    heads deskolemizing fixes. -/
theorem CalledProcedureSignaturesFixed.resolveSigs {σ : RigidNames} {A : List TypeAlias}
    (hns : AliasesNoSkolem σ A) {P : Program} {c : Command}
    (h : CalledProcedureSignaturesFixed σ P c) :
    CalledProcedureSignaturesFixed σ (P.resolveSigs A) c := by
  intro pname hp proc hf ty hty
  rw [Program.resolveSigs_find?] at hf
  obtain ⟨proc0, hf0, rfl⟩ := Option.map_eq_some_iff.mp hf
  rw [Procedure.resolveSig_inputs, Procedure.resolveSig_outputs,
    TContext.resolveSig_values, TContext.resolveSig_values,
    ← List.map_append, List.mem_map] at hty
  obtain ⟨ty0, hty0, rfl⟩ := hty
  rw [deskolemizeTy_resolveTy hns, h pname hp proc0 hf0 ty0 hty0]

/-! ## Deskolemization transport for commands -/

/-- Deskolemization keeps a declared type a valid source type, under a variable policy `adm`,
    from the skolemized to the rigid context, when every parameter a rigid constant stands for
    satisfies `adm`. -/
theorem declaredTy_valid_deskolemize (σ : RigidNames) (Csk Crig : LContext CoreLParams)
    {adm : TyVarAdmissibility}
    (Γ Γ' : TContext Unit) (hamb : AmbientDeskol σ Csk Crig) (hsc : DeskolemizesScope σ Γ Γ')
    (h_alias : AliasesNoSkolem σ Γ.aliases)
    (h_rig : ∀ p ∈ σ, adm p.1 = true) (mty₀ : LMonoTy)
    (h : ∃ r, SourceTyWF Csk adm Γ.aliases mty₀ r) :
    ∃ r, SourceTyWF Crig adm Γ'.aliases (deskolemizeTy σ mty₀) r := by
  obtain ⟨r, hr⟩ := h
  rw [hsc.1]
  exact ⟨_, SourceTyWF_deskolemizeTy
    (knownTypes_contains_of_getElem?_addSkolemTypes hamb.knownTypes_eq)
    (fun _ hv => hv) h_rig h_alias hr⟩

/-- Deskolemization keeps written free-variable annotations valid source types under `adm`, when
    every parameter a rigid constant stands for satisfies `adm` and aliases are unaffected. -/
theorem TypeSpec.FVarAnnotsWF.deskolemize (σ : RigidNames) {Csk Crig : LContext CoreLParams}
    {adm : TyVarAdmissibility} {aliases : List TypeAlias} {e : Expression.Expr}
    (h_known : ∀ x : String, Csk.knownTypes[x]? = (addSkolemTypes Crig σ).knownTypes[x]?)
    (h_alias : AliasesNoSkolem σ aliases)
    (h_rig : ∀ p ∈ σ, adm p.1 = true)
    (h : FVarAnnotsWF Csk adm aliases e) :
    FVarAnnotsWF Crig adm aliases (mapExprTys (deskolemizeTy σ) e) := by
  intro t ht
  simp only [mapExprTys, fvarAnnotations_replaceUserProvidedType, List.mem_map] at ht
  obtain ⟨t0, ht0, rfl⟩ := ht
  obtain ⟨r, hr⟩ := h t0 ht0
  exact ⟨_, SourceTyWF_deskolemizeTy (knownTypes_contains_of_getElem?_addSkolemTypes h_known)
    (fun _ hv => hv) h_rig h_alias hr⟩

/-- Deskolemization keeps binder-annotation type variables admissible under `adm`, when every
    parameter a rigid constant stands for is admissible. -/
theorem TypeSpec.BinderAnnotTyVarsAdmissible.deskolemize (σ : RigidNames)
    {adm : TyVarAdmissibility} {e : Expression.Expr}
    (h_rig : ∀ p ∈ σ, adm p.1 = true)
    (h : BinderAnnotTyVarsAdmissible adm e) :
    BinderAnnotTyVarsAdmissible adm (mapExprTys (deskolemizeTy σ) e) := by
  intro t ht
  simp only [mapExprTys, binderAnnotations_replaceUserProvidedType, List.mem_map] at ht
  obtain ⟨t0, ht0, rfl⟩ := ht
  exact freeVars_deskolemizeTy_admissible σ (h t0 ht0) h_rig

/-- The written-annotation requirement survives deskolemizing the expression, scope
    and ambient together, when it admits every parameter a rigid constant stands for. -/
theorem writtenAnnotsOk_deskolemize (σ : RigidNames) (Csk Crig : LContext CoreLParams)
    (Γ Γ' : TContext Unit) (hamb : AmbientDeskol σ Csk Crig) (hsc : DeskolemizesScope σ Γ Γ')
    (h_alias : AliasesNoSkolem σ Γ.aliases)
    (h_rig : ∀ p ∈ σ, TyVarAdmissibility.notGeneratedOrRigid p.1 = true)
    (e : Expression.Expr) (h : WrittenAnnotsOk Csk Γ e) :
    WrittenAnnotsOk Crig Γ' (mapExprTys (deskolemizeTy σ) e) := by
  obtain ⟨hfvar, hbinder⟩ := h
  refine ⟨?_, TypeSpec.BinderAnnotTyVarsAdmissible.deskolemize σ h_rig hbinder⟩
  change FVarAnnotsWF Csk TyVarAdmissibility.notGeneratedOrRigid Γ.aliases e at hfvar
  change FVarAnnotsWF Crig TyVarAdmissibility.notGeneratedOrRigid Γ'.aliases
    (mapExprTys (deskolemizeTy σ) e)
  rw [hsc.1]
  exact TypeSpec.FVarAnnotsWF.deskolemize σ hamb.knownTypes_eq h_alias h_rig hfvar

/-- No type variable in `ps` occurs free in a command's declared type or in a free-variable or
    binder annotation of an expression the command reads. -/
@[expose] def Command.VarsAvoid (ps : List TyIdentifier) : Command → Prop
  | .cmd (.init _ ty e _) =>
    (∀ v ∈ LTy.freeVars ty, v ∉ ps) ∧ ∀ x, e = .det x → LExpr.AnnotsAvoid x ps
  | .cmd (.set _ e _) => ∀ x, e = .det x → LExpr.AnnotsAvoid x ps
  | .cmd (.assert _ b _) | .cmd (.assume _ b _) | .cmd (.cover _ b _) => LExpr.AnnotsAvoid b ps
  | .call _ _ args _ => ∀ e ∈ CallArg.getInputExprs args, LExpr.AnnotsAvoid e ps

/-- No literal in an expression a command reads has a type that deskolemization changes. -/
@[expose] def Command.LitsFixed (σ : RigidNames) (c : Command) : Prop :=
  ∀ e ∈ Statement.cmdExprs c, ConstTysFixed σ e

/-! ## Deskolemization with written type variables in scope -/

/-- `Δ'` binds every variable `Δ` binds, and each binding of `Δ'` is the deskolemization of `Δ`'s
    binding for the same variable. -/
structure EnvDeskol (σ : RigidNames) (Δ Δ' : WrittenEnv) : Prop where
  sub : ∀ v t', Δ' v = some t' → ∃ t, Δ v = some t ∧ deskolemizeTy σ t = t'
  dom : ∀ v, (Δ v).isSome → (Δ' v).isSome

/-- `Δ` binds no type parameter that `σ` renames. -/
def NoParamBinding (σ : RigidNames) (Δ : WrittenEnv) : Prop :=
  ∀ q ∈ σ, Δ q.1 = none

/-- Every type `Δ` binds avoids the parameters `σ` renames. -/
def ReadAvoids (σ : RigidNames) (Δ : WrittenEnv) : Prop :=
  ∀ v t, Δ v = some t → ∀ x ∈ LMonoTy.freeVars t, x ∉ σ.map Prod.fst

/-- A deskolemization of an environment binding no renamed parameter binds none either. -/
private theorem EnvDeskol.noParam {σ : RigidNames} {Δ Δ' : WrittenEnv} (henv : EnvDeskol σ Δ Δ')
    (hnp : NoParamBinding σ Δ) : NoParamBinding σ Δ' := by
  intro q hq
  cases hΔ' : Δ' q.1 with
  | none => rfl
  | some t' =>
    obtain ⟨t, hΔ, -⟩ := henv.sub q.1 t' hΔ'
    rw [hnp q hq] at hΔ
    cases hΔ

/-- Deskolemizing how a type variable is read in `Δ` gives how it is read in a deskolemization
    of `Δ`. -/
private theorem readTyVar_deskolemize {σ : RigidNames} {Δ Δ' : WrittenEnv} (henv : EnvDeskol σ Δ Δ')
    (v : TyIdentifier) : deskolemizeTy σ (readTyVar Δ v) = readTyVar Δ' v := by
  unfold readTyVar
  split
  · cases hΔ : Δ v with
    | none =>
      have hΔ' : Δ' v = none := by
        cases hΔ' : Δ' v with
        | none => rfl
        | some t' =>
          obtain ⟨t, h, -⟩ := henv.sub v t' hΔ'
          rw [hΔ] at h
          cases h
      rw [hΔ', Option.getD_none]
      exact deskolemizeTy_ftvar σ v
    | some u =>
      have hΔsome : (Δ v).isSome = true := by
        rw [hΔ]
        rfl
      obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (henv.dom v hΔsome)
      obtain ⟨u0, h0, hd⟩ := henv.sub v u' hu'
      rw [hΔ, Option.some.injEq] at h0
      subst h0
      rw [hu', Option.getD_some, Option.getD_some]
      exact hd
  · exact deskolemizeTy_ftvar σ v

/-- A renamed parameter that `Δ` does not bind is read as itself. -/
private theorem readTyVar_param {σ : RigidNames} {Δ : WrittenEnv} (hnp : NoParamBinding σ Δ)
    {q : String × String} (hq : q ∈ σ) : readTyVar Δ q.1 = .ftvar q.1 := by
  unfold readTyVar
  split
  · rw [hnp q hq, Option.getD_none]
  · rfl

/-- Deskolemizing after `S` equals applying `S'` after deskolemizing, when `S'` sends each
    remaining variable to its deskolemized `S`-image and fixes every renamed parameter. -/
private theorem deskolemizeTy_subst_comm (σ : RigidNames) (S S' : Subst) (mty : LMonoTy)
    (h_pt : ∀ x ∈ LMonoTy.freeVars (deskolemizeTy σ mty),
      deskolemizeTy σ (LMonoTy.subst S (.ftvar x)) = LMonoTy.subst S' (.ftvar x))
    (h_sk : ∀ q ∈ σ, LMonoTy.subst S' (.ftvar q.1) = .ftvar q.1) :
    deskolemizeTy σ (LMonoTy.subst S mty) = LMonoTy.subst S' (deskolemizeTy σ mty) := by
  induction mty with
  | ftvar x =>
    rw [deskolemizeTy_ftvar] at h_pt ⊢
    exact h_pt x (List.mem_singleton.mpr rfl)
  | bitvec n =>
    rw [LMonoTy.subst_bitvec, deskolemizeTy_bitvec, LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons_map, deskolemizeTy_tcons, deskolemizeTy_tcons]
    cases hfind : σ.find? (fun p => p.2 == name) with
    | some q =>
      exact (h_sk q (List.mem_of_find?_eq_some hfind)).symm
    | none =>
      rw [deskolemizeTy_tcons, hfind] at h_pt
      dsimp only at h_pt ⊢
      rw [LMonoTy.subst_tcons_map, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left ?_
      intro a ha
      refine ih a ha ?_
      intro x hx
      refine h_pt x ?_
      simp only [LMonoTy.freeVars]
      exact LMonoTys.freeVars_mem_subset (List.mem_map_of_mem ha) hx

/-- Deskolemizing a read annotation gives the deskolemized annotation read in a deskolemization
    of the environment, when the environment binds no renamed parameter. -/
private theorem deskolemizeTy_instAnnotTy {σ : RigidNames} {Δ Δ' : WrittenEnv}
    (henv : EnvDeskol σ Δ Δ') (hnp : NoParamBinding σ Δ) (t : LMonoTy) :
    deskolemizeTy σ (instAnnotTy Δ t) = instAnnotTy Δ' (deskolemizeTy σ t) := by
  rw [instAnnotTy_eq, instAnnotTy_eq]
  refine deskolemizeTy_subst_comm σ _ _ t ?_ ?_
  · intro x hx
    rw [restrictTo_ftvar _ _ x hx]
    rcases freeVars_deskolemizeTy_subset σ t x hx with hxt | hxσ
    · rw [restrictTo_ftvar _ t x hxt]
      exact readTyVar_deskolemize henv x
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxσ
      rw [readTyVar_param (henv.noParam hnp) hq]
      by_cases hxt : q.1 ∈ LMonoTy.freeVars t
      · rw [restrictTo_ftvar _ t _ hxt, readTyVar_param hnp hq, deskolemizeTy_ftvar]
      · rw [restrictTo_ftvar_of_not_mem _ t _ hxt, deskolemizeTy_ftvar]
  · intro q hq
    by_cases hx : q.1 ∈ LMonoTy.freeVars (deskolemizeTy σ t)
    · rw [restrictTo_ftvar _ _ _ hx, readTyVar_param (henv.noParam hnp) hq]
    · exact restrictTo_ftvar_of_not_mem _ _ _ hx

/-- Deskolemizing the annotations of an expression read through `Δ` gives the deskolemized
    expression read through a deskolemization of `Δ`, when `Δ` binds no renamed parameter. -/
theorem mapExprTys_deskolemizeTy_instAnnots {σ : RigidNames} {Δ Δ' : WrittenEnv}
    (henv : EnvDeskol σ Δ Δ') (hnp : NoParamBinding σ Δ) (e : Expression.Expr) :
    mapExprTys (deskolemizeTy σ) (instAnnots Δ e) =
      instAnnots Δ' (mapExprTys (deskolemizeTy σ) e) := by
  induction e <;>
    simp_all [mapExprTys, LExpr.replaceUserProvidedType, instAnnots, Option.map_map,
      Function.comp_def, deskolemizeTy_instAnnotTy henv hnp]

/-- Reading the annotations of an expression through a written-variable environment keeps its
    literals. -/
private theorem getConsts_instAnnots (Δ : TyIdentifier → Option LMonoTy) (e : Expression.Expr) :
    LExpr.getConsts (instAnnots Δ e) = LExpr.getConsts e := by
  induction e with
  | const m c => rfl
  | op m o ty => rfl
  | bvar m i => rfl
  | fvar m x ty => rfl
  | abs m name ty body ih =>
    simp only [instAnnots, LExpr.getConsts]
    exact ih
  | quant m qk name ty tr body ihtr ihbody =>
    simp only [instAnnots, LExpr.getConsts]
    rw [ihtr, ihbody]
  | app m e1 e2 ih1 ih2 =>
    simp only [instAnnots, LExpr.getConsts]
    rw [ih1, ih2]
  | ite m c t f ihc iht ihf =>
    simp only [instAnnots, LExpr.getConsts]
    rw [ihc, iht, ihf]
  | eq m e1 e2 ih1 ih2 =>
    simp only [instAnnots, LExpr.getConsts]
    rw [ih1, ih2]

/-- Reading the annotations of an expression through a written-variable environment keeps the
    types of its literals fixed by deskolemization. -/
theorem ConstTysFixed.instAnnots {σ : RigidNames} (Δ : TyIdentifier → Option LMonoTy)
    {e : Expression.Expr} (h : ConstTysFixed σ e) : ConstTysFixed σ (instAnnots Δ e) :=
  ConstTysFixed_of_getConsts_eq (getConsts_instAnnots Δ e) h

/-- Reading an annotation through `Δ` causes no rigid-name clash when the annotation and the types
    `Δ` binds avoid the renamed parameters. -/
private theorem annotNoRigidClash_instAnnotTy {σ : RigidNames} {Δ : WrittenEnv}
    (hΔ : ∀ v u, Δ v = some u → ∀ x ∈ LMonoTy.freeVars u, x ∉ σ.map Prod.fst) (t : LMonoTy)
    (ht : ∀ x ∈ LMonoTy.freeVars t, x ∉ σ.map Prod.fst) :
    annotNoRigidClash σ (instAnnotTy Δ t) = true := by
  refine annotNoRigidClash_of_freeVars_not_mem σ _ ?_
  intro x hx
  rcases freeVars_instAnnotTy Δ t x hx with hxt | ⟨v, u, hvu, hxu⟩
  · exact ht x hxt
  · exact hΔ v u hvu x hxu

/-- Reading an expression through `Δ` keeps all its annotations clash-free, when `Δ`'s types and
    the expression's written annotations avoid the renamed parameters. -/
theorem allExprTys_annotNoRigidClash_instAnnots {σ : RigidNames} {Δ : WrittenEnv}
    (hΔ : ∀ v u, Δ v = some u → ∀ x ∈ LMonoTy.freeVars u, x ∉ σ.map Prod.fst) :
    ∀ e : Expression.Expr, LExpr.AnnotsAvoid e (σ.map Prod.fst) →
      allExprTys (annotNoRigidClash σ) e = true →
      allExprTys (annotNoRigidClash σ) (instAnnots Δ e) = true := by
  have hopt : ∀ (ty : Option LMonoTy),
      (∀ t ∈ ty.toList, ∀ x ∈ LMonoTy.freeVars t, x ∉ σ.map Prod.fst) →
      (ty.map (instAnnotTy Δ)).all (annotNoRigidClash σ) = true := by
    intro ty hty
    cases ty with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Option.all_some]
      exact annotNoRigidClash_instAnnotTy hΔ t (hty t (List.mem_singleton.mpr rfl))
  intro e
  simp only [allExprTys_eq_allUserProvidedTypes]
  induction e with
  | const | op | bvar => intro _ h; exact h
  | fvar md x ty =>
    intro hav _
    have hty : ∀ t ∈ ty.toList, ∀ y ∈ LMonoTy.freeVars t, y ∉ σ.map Prod.fst := by
      intro t ht
      apply hav t
      simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.append_nil]
      exact ht
    simp only [LExpr.allUserProvidedTypes, instAnnots]
    exact hopt ty hty
  | abs md n ty b ih =>
    intro hav h
    simp only [LExpr.allUserProvidedTypes, instAnnots, Bool.and_eq_true] at h ⊢
    refine ⟨hopt ty (fun t ht => hav t ?_), ih (fun t ht => hav t ?_) h.2⟩
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append]
      exact Or.inr (Or.inl ht)
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
  | quant md k n ty tr b iht ihb =>
    intro hav h
    simp only [LExpr.allUserProvidedTypes, instAnnots, Bool.and_eq_true] at h ⊢
    refine ⟨⟨hopt ty (fun t ht => hav t ?_), iht (fun t ht => hav t ?_) h.1.2⟩,
      ihb (fun t ht => hav t ?_) h.2⟩
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append]
      grind
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
  | app md f a ihf iha =>
    intro hav h
    simp only [LExpr.allUserProvidedTypes, instAnnots, Bool.and_eq_true] at h ⊢
    refine ⟨ihf (fun t ht => hav t ?_) h.1, iha (fun t ht => hav t ?_) h.2⟩
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
  | ite md c t f ihc iht ihf =>
    intro hav h
    simp only [LExpr.allUserProvidedTypes, instAnnots, Bool.and_eq_true] at h ⊢
    refine ⟨⟨ihc (fun t ht => hav t ?_) h.1.1, iht (fun t ht => hav t ?_) h.1.2⟩,
      ihf (fun t ht => hav t ?_) h.2⟩
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
  | eq md a b iha ihb =>
    intro hav h
    simp only [LExpr.allUserProvidedTypes, instAnnots, Bool.and_eq_true] at h ⊢
    refine ⟨iha (fun t ht => hav t ?_) h.1, ihb (fun t ht => hav t ?_) h.2⟩
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind
    · simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.mem_append] at ht ⊢
      grind

/-- The empty environment deskolemizes to itself. -/
theorem EnvDeskol.empty (σ : RigidNames) : EnvDeskol σ (fun _ => none) (fun _ => none) where
  sub := fun _ _ h => by cases h
  dom := fun _ h => by simp only [Option.isSome_none, Bool.false_eq_true] at h

/-- The empty environment binds no renamed parameter. -/
theorem NoParamBinding.empty (σ : RigidNames) : NoParamBinding σ (fun _ => none) :=
  fun _ _ => rfl

/-- No type parameter that `σ` renames occurs free in a type `S` binds. -/
@[expose] def NoParamRange (σ : RigidNames) (S : Subst) : Prop :=
  ∀ v ∈ Subst.freeVars S, v ∉ σ.map Prod.fst

/-- The rigid-side counterpart of the instantiation `ρ` of the annotation `ann`. -/
def deskolInst (σ : RigidNames) (ann : LMonoTy) (ρ : SubstOne) : SubstOne :=
  LExpr.buildSubstFromFunction (LMonoTy.freeVars ann)
    (fun v => deskolemizeTy σ (LMonoTy.subst [ρ] (.ftvar v)))

/-- `deskolInst σ ann ρ` sends a free type variable of `ann` to its deskolemized `ρ`-instance. -/
private theorem deskolInst_ftvar (σ : RigidNames) (ann : LMonoTy) (ρ : SubstOne) (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars ann) :
    LMonoTy.subst [deskolInst σ ann ρ] (.ftvar v) =
      deskolemizeTy σ (LMonoTy.subst [ρ] (.ftvar v)) := by
  apply LMonoTy.subst_ftvar_of_some
  rw [Strata.Util.HMaps.find?_single_scope]
  exact LExpr.find?_buildSubstFromFunction _ _ v hv

/-- `deskolInst σ ann ρ` fixes every type variable that is not free in `ann`. -/
private theorem deskolInst_ftvar_of_not_mem (σ : RigidNames) (ann : LMonoTy) (ρ : SubstOne)
    (v : TyIdentifier) (hv : v ∉ LMonoTy.freeVars ann) :
    LMonoTy.subst [deskolInst σ ann ρ] (.ftvar v) = .ftvar v := by
  apply LMonoTy.subst_ftvar_of_none
  rw [Strata.Util.HMaps.find?_single_scope]
  exact LExpr.find?_buildSubstFromFunction_of_not_mem _ _ v hv

/-- Deskolemization through `deskolInst` keeps a substitution fixing the rigid type variables and
    agreeing with the written environment, when `Δ` binds none of the renamed parameters. -/
private theorem substScoped_deskolemize (σ : RigidNames) {rigid : List TyIdentifier}
    {Δ Δ' : WrittenEnv} {ρ : SubstOne} {ann : LMonoTy}
    (hrigid : LExpr.SubstFixesRigid rigid ρ) (hagree : SubstAgreesWith Δ ρ ann)
    (h_env : EnvDeskol σ Δ Δ') (h_np : NoParamBinding σ Δ) :
    LExpr.SubstFixesRigid rigid (deskolInst σ ann ρ) ∧
      SubstAgreesWith Δ' (deskolInst σ ann ρ) (deskolemizeTy σ ann) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    by_cases hfree : v ∈ LMonoTy.freeVars ann
    · rw [deskolInst_ftvar σ ann ρ v hfree, hrigid v hv, deskolemizeTy_ftvar]
    · exact deskolInst_ftvar_of_not_mem σ ann ρ v hfree
  · intro v hv t' hΔ'
    obtain ⟨t, hΔ, hdt⟩ := h_env.sub v t' hΔ'
    rcases freeVars_deskolemizeTy_subset σ ann v hv with hva | hvσ
    · rw [deskolInst_ftvar σ ann ρ v hva, hagree v hva t hΔ, hdt]
    · obtain ⟨q, hq, hqv⟩ := List.mem_map.mp hvσ
      rw [← hqv, h_np q hq] at hΔ
      cases hΔ

/-- Deskolemization preserves scoped declaration instances, through `deskolInst`, when every
    renamed parameter is rigid and `Δ` binds none of them. -/
theorem scopedAnnotInst_deskolemizeTy_of_rigid (σ : RigidNames) {aliases : List TypeAlias}
    {rigid : List TyIdentifier} {Δ Δ' : WrittenEnv} {ρ : SubstOne} {ann mty : LMonoTy}
    (h : ScopedAnnotInst aliases rigid Δ ρ ann mty)
    (h_alias : AliasesNoSkolem σ aliases)
    (hσ : ∀ q ∈ σ, q.1 ∈ rigid)
    (h_env : EnvDeskol σ Δ Δ') (h_np : NoParamBinding σ Δ) :
    ScopedAnnotInst aliases rigid Δ' (deskolInst σ ann ρ)
      (deskolemizeTy σ ann) (deskolemizeTy σ mty) := by
  obtain ⟨hrigid, hagree, hae⟩ := h
  obtain ⟨hrigid', hagree'⟩ := substScoped_deskolemize σ hrigid hagree h_env h_np
  refine ⟨hrigid', hagree', ?_⟩
  have hae' := AliasEquiv_deskolemizeTy hae h_alias
  have hcomm := subst_deskolInst_comm_of_fix σ ρ (LMonoTy.freeVars ann)
    (fun q hq => hrigid q.1 (hσ q hq)) ann (fun v hv => hv)
  change AliasEquiv aliases
    (LMonoTy.subst [LExpr.buildSubstFromFunction (LMonoTy.freeVars ann)
      (fun v => deskolemizeTy σ (LMonoTy.subst [ρ] (.ftvar v)))] (deskolemizeTy σ ann))
    (deskolemizeTy σ mty)
  rw [hcomm]
  exact hae'

/-- Binding a declaration's first uses commutes with deskolemization up to `EnvDeskol`, when every
    renamed parameter is rigid and deskolemization keeps the declared type's non-rigid variables. -/
private theorem bindFirst_deskolemize (σ : RigidNames)
    {rigid : List TyIdentifier} {Δ Δ' : WrittenEnv} {ρ : SubstOne} {ann : LMonoTy}
    (h_env : EnvDeskol σ Δ Δ') (hσ : ∀ q ∈ σ, q.1 ∈ rigid)
    (hkeep : ∀ v ∈ LMonoTy.freeVars ann, v ∉ rigid → v ∈ LMonoTy.freeVars (deskolemizeTy σ ann)) :
    EnvDeskol σ (Δ.bindFirst rigid ann ρ)
      (Δ'.bindFirst rigid (deskolemizeTy σ ann) (deskolInst σ ann ρ)) := by
  refine ⟨?_, ?_⟩
  · intro v t' hb
    simp only [WrittenEnv.bindFirst] at hb ⊢
    cases hΔ' : Δ' v with
    | some t0 =>
      rw [hΔ'] at hb
      have ht : t0 = t' := Option.some.inj hb
      subst ht
      obtain ⟨t, hΔ, hdt⟩ := h_env.sub v t0 hΔ'
      refine ⟨t, ?_, hdt⟩
      rw [hΔ]
    | none =>
      rw [hΔ'] at hb
      simp only at hb
      split at hb
      · rename_i hcond
        cases hb
        have hva : v ∈ LMonoTy.freeVars ann := by
          rcases freeVars_deskolemizeTy_subset σ ann v hcond.1 with hva | hvσ
          · exact hva
          · obtain ⟨q, hq, hqv⟩ := List.mem_map.mp hvσ
            exact absurd (hqv ▸ hσ q hq) hcond.2
        rw [deskolInst_ftvar σ ann ρ v hva]
        cases hΔ : Δ v with
        | none =>
          refine ⟨LMonoTy.subst [ρ] (.ftvar v), ?_, rfl⟩
          simp only [ite_eq_left (And.intro hva hcond.2)]
        | some _ =>
          have hdom := h_env.dom v (by simp only [hΔ, Option.isSome_some])
          simp only [hΔ', Option.isSome_none, Bool.false_eq_true] at hdom
      · cases hb
  · intro v hv
    simp only [WrittenEnv.bindFirst] at hv ⊢
    cases hΔ' : Δ' v with
    | some t0 => rfl
    | none =>
      simp only
      cases hΔ : Δ v with
      | some t =>
        have hdom := h_env.dom v (by simp only [hΔ, Option.isSome_some])
        simp only [hΔ', Option.isSome_none, Bool.false_eq_true] at hdom
      | none =>
        simp only [hΔ] at hv
        split at hv
        · rename_i hcond
          rw [ite_eq_left ⟨hkeep v hcond.1 hcond.2, hcond.2⟩]
          rfl
        · cases hv

/-- The annotation scope condition survives deskolemization when every renamed parameter is
    rigid. -/
theorem annotsInScope_deskolemize (σ : RigidNames) {rigid : List TyIdentifier}
    {Δ Δ' : WrittenEnv} {e : Expression.Expr} (hσ : ∀ q ∈ σ, q.1 ∈ rigid)
    (h_env : EnvDeskol σ Δ Δ') (h : AnnotsInScope rigid Δ e) :
    AnnotsInScope rigid Δ' (mapExprTys (deskolemizeTy σ) e) := by
  intro t ht v hv
  simp only [mapExprTys, fvarAnnotations_replaceUserProvidedType,
    binderAnnotations_replaceUserProvidedType, ← List.map_append] at ht
  obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
  rcases freeVars_deskolemizeTy_subset σ t₀ v hv with hv₀ | hvσ
  · rcases h t₀ ht₀ v hv₀ with hr | hb
    · exact Or.inl hr
    · exact Or.inr (h_env.dom v hb)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hvσ
    exact Or.inl (hσ q hq)

/-- Binding first uses keeps `Δ` free of renamed parameters when they are all rigid. -/
private theorem NoParamBinding.bindFirst {σ : RigidNames} {Δ : WrittenEnv}
    {rigid : List TyIdentifier}
    (ann : LMonoTy) (ρ : SubstOne) (h : NoParamBinding σ Δ) (hσ : ∀ q ∈ σ, q.1 ∈ rigid) :
    NoParamBinding σ (Δ.bindFirst rigid ann ρ) := by
  intro q hq
  simp only [WrittenEnv.bindFirst, h q hq]
  rw [ite_eq_right (fun hc => hc.2 (hσ q hq))]

/-- Typing by the typechecker spec with written type-variable scopes survives deskolemizing the
    command, scope, ambient and written environment; the output environments stay related and the
    skolem-side one binds no renamed parameter. -/
theorem TypeSpec.CmdExtHasType.deskolemize
    (σ : RigidNames) (hpfx : RigidNamesPrefixed σ)
    (P : Program) (Csk Crig : LContext CoreLParams)
    (Γ Γ' Γ_out : TContext Unit) (Δ Δ' Δ_out : WrittenEnv) (c : Command) (A : LMonoTy → Bool)
    (hamb : AmbientDeskol σ Csk Crig) (hsc : DeskolemizesScope σ Γ Γ')
    (h_expr : ∀ (Δ₁ Δ₁' : WrittenEnv) (e : Expression.Expr) (mty : LMonoTy),
      EnvDeskol σ Δ₁ Δ₁' → NoParamBinding σ Δ₁ → ReadAvoids σ Δ₁ →
      LExpr.AnnotsAvoid e (σ.map Prod.fst) →
      allExprTys A e = true → ConstTysFixed σ e →
      LExpr.HasType Csk Γ (instAnnots Δ₁ e) (.forAll [] mty) →
      LExpr.HasType Crig Γ' (instAnnots Δ₁' (mapExprTys (deskolemizeTy σ) e))
        (.forAll [] (deskolemizeTy σ mty)))
    (h_call_expr : ReadAvoids σ Δ →
      ∀ (e : Expression.Expr) (mty : LMonoTy),
      LExpr.AnnotsAvoid e (σ.map Prod.fst) →
      allExprTys A e = true → ConstTysFixed σ e →
      (match e with
       | .fvar _ x none => Γ.types.find? x = some (.forAll [] mty)
       | e => LExpr.HasType Csk Γ (instAnnots Δ e) (.forAll [] mty)) →
      (match mapExprTys (deskolemizeTy σ) e with
       | .fvar _ x none => Γ'.types.find? x = some (.forAll [] (deskolemizeTy σ mty))
       | e => LExpr.HasType Crig Γ' (instAnnots Δ' e) (.forAll [] (deskolemizeTy σ mty))))
    (h_declΔ : ∀ (ρ : SubstOne) (ann mty : LMonoTy), A ann = true →
      (ScopedAnnotInst Γ.aliases Csk.rigidTypeVars Δ ρ ann mty ∧
        ValidDeclaredTy Csk Γ.aliases ann) →
      (ScopedAnnotInst Γ'.aliases Crig.rigidTypeVars Δ' (deskolInst σ ann ρ)
          (deskolemizeTy σ ann) (deskolemizeTy σ mty) ∧
        ValidDeclaredTy Crig Γ'.aliases (deskolemizeTy σ ann)))
    (h_wk : ∀ mty, Csk.WellKindedTy mty →
      Crig.WellKindedTy (deskolemizeTy σ mty))
    (h_alias : AliasesNoSkolem σ Γ.aliases)
    (h_rigAdm : ∀ p ∈ σ, TyVarAdmissibility.notGeneratedOrRigid p.1 = true)
    (h_calls : CalledProcedureSignaturesFixed σ P c)
    (h_ann : allCmdTys A c = true)
    (h_src : Command.VarsAvoid (σ.map Prod.fst) c)
    (h_lit : Command.LitsFixed σ c)
    (h_read : ReadAvoids σ Δ_out)
    (hσ : ∀ q ∈ σ, q.1 ∈ Csk.rigidTypeVars)
    (h_env : EnvDeskol σ Δ Δ') (h_np : NoParamBinding σ Δ)
    (h_keep : ∀ ann, A ann = true →
      ∀ v ∈ LMonoTy.freeVars ann, v ∈ LMonoTy.freeVars (deskolemizeTy σ ann))
    (h : CmdExtHasType Csk P Δ Γ c Γ_out Δ_out) :
    ∃ Γ_out' Δ_out',
      CmdExtHasType Crig P Δ' Γ' (mapCmdTys (deskolemizeTy σ) c) Γ_out' Δ_out' ∧
      DeskolemizesScope σ Γ_out Γ_out' ∧ EnvDeskol σ Δ_out Δ_out' ∧ NoParamBinding σ Δ_out := by
  have hrig : Csk.rigidTypeVars = Crig.rigidTypeVars := hamb.rigidTypeVars_eq
  have h_written : ∀ e : Expression.Expr, WrittenAnnotsOk Csk Γ e →
      WrittenAnnotsOk Crig Γ' (mapExprTys (deskolemizeTy σ) e) :=
    fun e he => writtenAnnotsOk_deskolemize σ Csk Crig Γ Γ' hamb hsc h_alias h_rigAdm e he
  have h_tc : ∀ ty ty', AliasEquiv Γ.aliases ty ty' →
      AliasEquiv Γ'.aliases (deskolemizeTy σ ty) (deskolemizeTy σ ty') := by
    intro ty ty' hae
    rw [hsc.1]
    exact AliasEquiv_deskolemizeTy hae h_alias
  have hσrig : ∀ q ∈ σ, q.1 ∈ Crig.rigidTypeVars := by
    rw [← hrig]
    exact hσ
  have hfresh : ∀ x, Γ.types.find? x = none → Γ'.types.find? x = none := by
    intro x hfind
    rw [hsc.2 x, hfind]
    rfl
  cases h with
  | cmd =>
    rename_i hc
    cases hc with
    | init_det x xty e mty mty₀ ρ md _ hfind hfv hxty hdecl hwk hexpr hann hin heqv =>
      subst hxty
      simp only [allCmdTys, allLTyTys, allExprOrNondetTys, Bool.and_eq_true] at h_ann
      have hdecl' := h_declΔ ρ mty₀ mty h_ann.1 hdecl
      have hout := bindFirst_deskolemize σ (ρ := ρ) h_env hσ
        (fun v hv _ => h_keep mty₀ h_ann.1 v hv)
      have hin' := hin
      rw [hrig] at hin'
      have hscope := annotsInScope_deskolemize σ hσrig (hrig ▸ hout) hin'
      have hnp := NoParamBinding.bindFirst mty₀ ρ h_np hσ
      have hlit := h_lit e (List.mem_singleton.mpr rfl)
      have hexpr' := h_expr _ _ e mty hout hnp h_read (h_src.2 e rfl) h_ann.2 hlit hexpr
      rw [hrig] at hout hnp hexpr' ⊢
      have hfind' := hfresh x hfind
      have hfv' : x ∉ HasFvars.getFvars (P := Expression) (mapExprTys (deskolemizeTy σ) e) := by
        rw [getFvars_mapExprTys]
        exact hfv
      refine ⟨{ Γ' with types := Γ'.types.insert x (.forAll [] (deskolemizeTy σ mty)) }, _,
        ?_,
        DeskolemizesScope.of_equiv_left σ _ _ _ heqv (DeskolemizesScope.insert σ Γ Γ' hsc x mty),
        hout, hnp⟩
      change CmdExtHasType Crig P Δ' Γ'
        (.cmd (.init x (.forAll [] (deskolemizeTy σ mty₀))
          (.det (mapExprTys (deskolemizeTy σ) e)) md)) _ _
      exact .cmd _ _ _ _ _ (.init_det _ _ _ _ _ _ _ _ _ _ hfind' hfv' rfl hdecl'
        (h_wk mty hwk) hexpr' (h_written e hann) hscope
        (TContext.Equiv.refl _))
    | init_nondet x xty mty mty₀ ρ md _ hfind hxty hdecl hwk heqv =>
      subst hxty
      simp only [allCmdTys, Bool.and_eq_true] at h_ann
      have hdecl' := h_declΔ ρ mty₀ mty h_ann.1 hdecl
      have hout := bindFirst_deskolemize σ (ρ := ρ) h_env hσ
        (fun v hv _ => h_keep mty₀ h_ann.1 v hv)
      have hnp := NoParamBinding.bindFirst mty₀ ρ h_np hσ
      rw [hrig] at hout hnp ⊢
      have hfind' := hfresh x hfind
      refine ⟨{ Γ' with types := Γ'.types.insert x (.forAll [] (deskolemizeTy σ mty)) }, _,
        ?_,
        DeskolemizesScope.of_equiv_left σ _ _ _ heqv (DeskolemizesScope.insert σ Γ Γ' hsc x mty),
        hout, hnp⟩
      change CmdExtHasType Crig P Δ' Γ'
        (.cmd (.init x (.forAll [] (deskolemizeTy σ mty₀)) .nondet md)) _ _
      exact .cmd _ _ _ _ _ (.init_nondet _ _ _ _ _ _ _ _ _ hfind' rfl hdecl'
        (h_wk mty hwk) (TContext.Equiv.refl _))
    | set_det x mty e md _ hfind hexpr hann hin heqv =>
      simp only [allCmdTys] at h_ann
      have hin' := hin
      rw [hrig] at hin'
      refine ⟨Γ', Δ', ?_, DeskolemizesScope.of_equiv_left σ Γ_out Γ Γ' heqv hsc, h_env, h_np⟩
      change CmdExtHasType Crig P Δ' Γ'
        (.cmd (.set x (.det (mapExprTys (deskolemizeTy σ) e)) md)) Γ' Δ'
      refine .cmd _ _ _ _ _ (.set_det _ Γ' x (deskolemizeTy σ mty)
        (mapExprTys (deskolemizeTy σ) e) md Γ' ?_ ?_ (h_written e hann)
        (annotsInScope_deskolemize σ hσrig h_env hin') (TContext.Equiv.refl _))
      · rw [hsc.2 x, hfind]
        rfl
      · have hlit := h_lit e (List.mem_singleton.mpr rfl)
        exact h_expr _ _ e mty h_env h_np h_read (h_src e rfl) h_ann hlit hexpr
    | set_nondet x mty md _ hfind heqv =>
      refine ⟨Γ', Δ', ?_, DeskolemizesScope.of_equiv_left σ Γ_out Γ Γ' heqv hsc, h_env, h_np⟩
      change CmdExtHasType Crig P Δ' Γ' (.cmd (.set x .nondet md)) Γ' Δ'
      refine .cmd _ _ _ _ _ (.set_nondet _ Γ' x (deskolemizeTy σ mty) md Γ' ?_
        (TContext.Equiv.refl _))
      rw [hsc.2 x, hfind]
      rfl
    | assert l e md _ hexpr hann hin heqv | assume l e md _ hexpr hann hin heqv
    | cover l e md _ hexpr hann hin heqv =>
      have hin' := hin
      rw [hrig] at hin'
      refine ⟨Γ', Δ', ?_, DeskolemizesScope.of_equiv_left σ Γ_out Γ Γ' heqv hsc, h_env, h_np⟩
      have hlit := h_lit e (List.mem_singleton.mpr rfl)
      have he := h_expr _ _ e .bool h_env h_np h_read h_src h_ann hlit hexpr
      rw [deskolemizeTy_bool hpfx] at he
      have hwr := h_written e hann
      have hsco := annotsInScope_deskolemize σ hσrig h_env hin'
      first
        | exact .cmd _ _ _ _ _ (.assert _ Γ' l (mapExprTys (deskolemizeTy σ) e) md Γ' he hwr
            hsco (TContext.Equiv.refl _))
        | exact .cmd _ _ _ _ _ (.assume _ Γ' l (mapExprTys (deskolemizeTy σ) e) md Γ' he hwr
            hsco (TContext.Equiv.refl _))
        | exact .cmd _ _ _ _ _ (.cover _ Γ' l (mapExprTys (deskolemizeTy σ) e) md Γ' he hwr
            hsco (TContext.Equiv.refl _))
  | call pname tyArgs callArgs proc md callσ Δo hproc hcall hlhs hin hann hscopeIn hout hEqv =>
    let callσ' := callσ.map (fun q => (q.1, deskolemizeTy σ q.2))
    have hinput := CallArg.getInputExprs_map_types (deskolemizeTy σ) callArgs
    have hlhsMap := CallArg.getLhs_map_congr (mapExprTys (deskolemizeTy σ)) callArgs
    have hsubst (formal : LMonoTy) (hfixed : deskolemizeTy σ formal = formal) :
        LMonoTy.subst (Strata.Util.HMaps.ofScopes [callσ']) formal =
          deskolemizeTy σ
            (LMonoTy.subst (Strata.Util.HMaps.ofScopes [callσ]) formal) := by
      symm
      apply deskolemizeTy_subst_eq_subst σ
        (Strata.Util.HMaps.ofScopes [callσ])
        (Strata.Util.HMaps.ofScopes [callσ']) formal
        hfixed
      intro x hx
      cases hfind : Strata.Util.HMap.find? (Strata.Util.HMap.ofList callσ) x with
      | none =>
        have hfind' : Strata.Util.HMap.find? (Strata.Util.HMap.ofList callσ') x = none := by
          simp only [callσ', Strata.Util.HMap.find?_ofList_map_snd, hfind, Option.map_none]
        have hfindS :
            Strata.Util.HMaps.find? (Strata.Util.HMaps.ofScopes [callσ]) x = none := by
          simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
            Strata.Util.HMaps.find?_single_scope, hfind]
        have hfindS' :
            Strata.Util.HMaps.find? (Strata.Util.HMaps.ofScopes [callσ']) x = none := by
          simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
            Strata.Util.HMaps.find?_single_scope, hfind']
        rw [LMonoTy.subst_ftvar_of_none hfindS,
          LMonoTy.subst_ftvar_of_none hfindS']
        exact deskolemizeTy_ftvar σ x
      | some ty =>
        have hfind' :
            Strata.Util.HMap.find? (Strata.Util.HMap.ofList callσ') x =
              some (deskolemizeTy σ ty) := by
          simp only [callσ', Strata.Util.HMap.find?_ofList_map_snd, hfind, Option.map_some]
        have hfindS :
            Strata.Util.HMaps.find? (Strata.Util.HMaps.ofScopes [callσ]) x = some ty := by
          simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
            Strata.Util.HMaps.find?_single_scope, hfind]
        have hfindS' :
            Strata.Util.HMaps.find? (Strata.Util.HMaps.ofScopes [callσ']) x =
              some (deskolemizeTy σ ty) := by
          simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
            Strata.Util.HMaps.find?_single_scope, hfind']
        rw [LMonoTy.subst_ftvar_of_some hfindS,
          LMonoTy.subst_ftvar_of_some hfindS']
    have hsig := h_calls pname (by simp) proc hproc
    refine ⟨Γ', Δ', ?_, DeskolemizesScope.of_equiv_left σ Γ_out Γ Γ' hEqv hsc, h_env, h_np⟩
    change CmdExtHasType Crig P Δ' Γ'
      (.call pname (tyArgs.map (·.map (mapLTyTys (deskolemizeTy σ))))
        (callArgs.map (CallArg.mapInput (mapExprTys (deskolemizeTy σ))))
        md) Γ' Δ'
    refine CmdExtHasType.call Δ' Γ' pname _
      (callArgs.map (CallArg.mapInput (mapExprTys (deskolemizeTy σ))))
      proc md callσ' Γ' hproc ?_ ?_ ?_ ?_ ?_ ?_ (TContext.Equiv.refl _)
    · exact hcall.transfer (.boolConst Core.valueLoc true) hproc hproc rfl rfl
        (CallArg.map_mapInput_const _ _ callArgs)
    · intro v hv
      rw [hlhsMap] at hv
      cases hfind : Γ.types.find? v with
      | none =>
        have hsome := hlhs v hv
        rw [hfind] at hsome
        simp at hsome
      | some ty =>
        rw [hsc.2 v, hfind]
        rfl
    · intro i hi hj
      have hiMap : i < (CallArg.getInputExprs callArgs).length := by
        simpa only [hinput, List.length_map] using hi
      have heq :
          (CallArg.getInputExprs
            (callArgs.map (CallArg.mapInput (mapExprTys (deskolemizeTy σ)))))[i] =
            mapExprTys (deskolemizeTy σ) (CallArg.getInputExprs callArgs)[i] := by
        exact (getElem_congr_coll hinput).trans
          (List.getElem_map (mapExprTys (deskolemizeTy σ)))
      have hi0 : i < (CallArg.getInputExprs callArgs).length := by
        exact hiMap
      obtain ⟨mty, hae, hm⟩ := hin i hi0 hj
      refine ⟨deskolemizeTy σ mty, ?_, ?_⟩
      · have hmemSig : proc.header.inputs.values[i] ∈
            proc.header.inputs.values ++ proc.header.outputs.values := by
          simp only [List.mem_append]
          exact Or.inl (List.getElem_mem hj)
        rw [hsubst proc.header.inputs.values[i] (hsig proc.header.inputs.values[i] hmemSig)]
        exact h_tc _ _ hae
      · rw [heq]
        have hargsAnn := ((Bool.and_eq_true _ _).mp h_ann).2
        have hargAnn := CallArg.getInputExprs_annotations callArgs hargsAnn
          _ (List.getElem_mem hi0)
        rcases hargAnn with ⟨m, x, he⟩ | he
        · have hm' : Γ.types.find? x = some (.forAll [] mty) := by
            simpa only [he] using hm
          have ht := h_call_expr h_read (LExpr.fvar m x none) mty
            (fun _ ht => absurd ht List.not_mem_nil) (by rfl)
            (ConstTysFixed_of_getConsts_nil rfl) hm'
          rw [he]
          exact ht
        · exact h_call_expr h_read _ mty (h_src _ (List.getElem_mem hi0)) he
            (h_lit _ (List.getElem_mem hi0)) hm
    · intro e he
      rw [hinput] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      exact h_written e0 (hann e0 he0)
    · intro e he
      rw [hinput] at he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      have hsc₀ := hscopeIn e0 he0
      rw [hrig] at hsc₀
      exact annotsInScope_deskolemize σ hσrig h_env hsc₀
    · intro i hi hj
      have hi0 : i < (CallArg.getLhs callArgs).length := by
        simpa only [hlhsMap] using hi
      have heq :
          (CallArg.getLhs
            (callArgs.map (CallArg.mapInput (mapExprTys (deskolemizeTy σ)))))[i] =
            (CallArg.getLhs callArgs)[i] := by
        simp only [hlhsMap]
      obtain ⟨mty, hae, hm⟩ := hout i hi0 hj
      refine ⟨deskolemizeTy σ mty, ?_, ?_⟩
      · have hmemSig : proc.header.outputs.values[i] ∈
            proc.header.inputs.values ++ proc.header.outputs.values := by
          simp only [List.mem_append]
          exact Or.inr (List.getElem_mem hj)
        rw [hsubst proc.header.outputs.values[i] (hsig proc.header.outputs.values[i] hmemSig)]
        exact h_tc _ _ hae
      · rw [heq, hsc.2, hm]
        rfl

/-! ## Registering a type name under the ambient deskolemization -/

/-- Registering a user-declared type name succeeds on the rigid side too and preserves the ambient
    deskolemization. -/
theorem addKnownTypeWithError_deskolemize
    (σ : RigidNames) (Csk Crig Cnew : LContext CoreLParams) (tc : TypeConstructor)
    (hamb : AmbientDeskol σ Csk Crig)
    (h : Csk.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok Cnew) :
    ∃ Cnew', Crig.addKnownTypeWithError
        { name := tc.name, metadata := tc.numargs } default = .ok Cnew' ∧
      AmbientDeskol σ Cnew Cnew' := by
  obtain ⟨hknown, hrigid, hfac⟩ := hamb
  simp only [LContext.addKnownTypeWithError, KnownTypes.addWithError, Identifiers.addWithError,
    Std.HashMap.containsThenInsertIfNew_fst, Std.HashMap.containsThenInsertIfNew_snd,
    bind, Except.bind] at h
  elim_err h with m hm
  simp only [Except.ok.injEq] at h
  subst h
  elim_err hm with hcontains
  simp only [Except.ok.injEq] at hm
  subst hm
  have hskNone : Csk.knownTypes[tc.name]? = none := by
    rw [Bool.not_eq_true, Std.HashMap.contains_eq_isSome_getElem?,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hcontains
    exact hcontains
  have hnotσ : tc.name ∉ σ.map Prod.snd := by
    intro hmem
    have hk := hknown tc.name
    rw [hskNone, addSkolemTypes_getElem?, ite_eq_left hmem] at hk
    exact absurd hk (by simp)
  have hrigNone : Crig.knownTypes[tc.name]? = none := by
    have hk := hknown tc.name
    rw [hskNone, addSkolemTypes_getElem?, ite_eq_right hnotσ] at hk
    exact hk.symm
  have hrigContains : Std.HashMap.contains Crig.knownTypes tc.name = false := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, hrigNone]; rfl
  have hmemSk : tc.name ∉ Csk.knownTypes := by
    rw [Std.HashMap.mem_iff_isSome_getElem?, hskNone]; simp
  have hmemRig : tc.name ∉ Crig.knownTypes := by
    rw [Std.HashMap.mem_iff_isSome_getElem?, hrigNone]; simp
  refine ⟨{ Crig with knownTypes := Crig.knownTypes.insertIfNew tc.name tc.numargs }, ?_,
    fun x => ?_, hrigid, hfac⟩
  · simp only [LContext.addKnownTypeWithError, KnownTypes.addWithError,
      Identifiers.addWithError, KnownType.arity, Std.HashMap.containsThenInsertIfNew_fst,
      Std.HashMap.containsThenInsertIfNew_snd, bind, Except.bind, hrigContains,
      Bool.false_eq_true, ite_false]
  · show (Csk.knownTypes.insertIfNew tc.name tc.numargs)[x]?
      = (addSkolemTypes { Crig with
          knownTypes := Crig.knownTypes.insertIfNew tc.name tc.numargs } σ).knownTypes[x]?
    rw [addSkolemTypes_getElem?]
    show (Csk.knownTypes.insertIfNew tc.name tc.numargs)[x]?
      = if x ∈ σ.map Prod.snd then some 0
        else (Crig.knownTypes.insertIfNew tc.name tc.numargs)[x]?
    by_cases hx : x = tc.name
    · subst hx
      have hins : ∀ ks : Lambda.KnownTypes, tc.name ∉ ks →
          (ks.insertIfNew tc.name tc.numargs)[tc.name]? = some tc.numargs := by
        intro ks hks
        rw [Std.HashMap.getElem?_insertIfNew, ite_eq_left ⟨beq_self_eq_true tc.name, hks⟩]
      rw [ite_eq_right hnotσ, hins Csk.knownTypes hmemSk, hins Crig.knownTypes hmemRig]
    · have hcond : ∀ (ks : Lambda.KnownTypes),
          ¬((tc.name == x) = true ∧ tc.name ∉ ks) := by
        intro ks hc
        apply hx
        rw [beq_iff_eq] at hc
        exact hc.1.symm
      rw [Std.HashMap.getElem?_insertIfNew, ite_eq_right (hcond Csk.knownTypes),
        Std.HashMap.getElem?_insertIfNew, ite_eq_right (hcond Crig.knownTypes), hknown x,
        addSkolemTypes_getElem?]

/-! ## Written variables and callees of checked commands -/

/-! ### Checked commands -/

/-- Successful command checking preserves modified and declared variable sets. -/
theorem Statement.typeCheckCmd_vars_eq
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env')) :
    Command.modifiedVars c' = Command.modifiedVars c ∧
    Command.definedVars c' = Command.definedVars c := by
  cases Statement.typeCheckCmd_ok_inv h with
  | cmd run => cases run <;> exact ⟨rfl, rfl⟩
  | call =>
    refine ⟨?_, rfl⟩
    simp only [Command.modifiedVars]
    exact CallArg.getLhs_replaceInArgs _ _

/-- Successful command checking preserves the called procedure names. -/
theorem Statement.typeCheckCmd_calledProcedureNames_eq
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env')) :
    CmdExt.calledProcedureNames c' = CmdExt.calledProcedureNames c := by
  cases Statement.typeCheckCmd_ok_inv h <;> rfl

/-- Inferring the type of an expression keeps its literals. -/
private theorem CmdType.inferType_getConsts_eq {C : LContext CoreLParams} {Env Env' : TEnv Unit}
    {c : Cmd Expression} {e e' : Expression.Expr} {ety : LTy}
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env')) :
    LExpr.getConsts e' = LExpr.getConsts e := by
  unfold CmdType.inferType at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  elim_err h with p hp
  obtain ⟨ea, T⟩ := p
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hr := SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hp)
  rw [Lambda.LExpr.Proofs.getConsts_unresolved]
  exact SourceExpr.resolve_getConsts_eq _ _ _ _ _ hr

/-- Successful command checking keeps the type names of the literals of the expressions the
    command reads. -/
theorem Statement.typeCheckCmd_litTyNames_eq
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env')) :
    (Statement.cmdExprs c').flatMap exprLitTyNames =
      (Statement.cmdExprs c).flatMap exprLitTyNames := by
  have hlit : ∀ {a b : Expression.Expr}, LExpr.getConsts a = LExpr.getConsts b →
      exprLitTyNames a = exprLitTyNames b := by
    intro a b hab
    unfold exprLitTyNames
    rw [hab]
  cases Statement.typeCheckCmd_ok_inv h with
  | cmd run =>
    cases run with
    | initDet hlookup hself hpre hinfer hunify hpost =>
      simp only [Statement.cmdExprs, Cmd.readExprs, ExprOrNondet.toList, List.flatMap_cons,
        List.flatMap_nil]
      exact congrArg (· ++ []) ((hlit (getConsts_applyTypeSubst _ _)).trans
        (hlit (CmdType.inferType_getConsts_eq hinfer)))
    | initNondet => rfl
    | setDet hlookup hinfer hunify =>
      simp only [Statement.cmdExprs, Cmd.readExprs, ExprOrNondet.toList, List.flatMap_cons,
        List.flatMap_nil]
      rw [hlit (CmdType.inferType_getConsts_eq hinfer)]
    | setNondet => rfl
    | assert hinfer hbool =>
      simp only [Statement.cmdExprs, Cmd.readExprs, List.flatMap_cons, List.flatMap_nil]
      rw [hlit (CmdType.inferType_getConsts_eq hinfer)]
    | assume hinfer hbool =>
      simp only [Statement.cmdExprs, Cmd.readExprs, List.flatMap_cons, List.flatMap_nil]
      rw [hlit (CmdType.inferType_getConsts_eq hinfer)]
    | cover hinfer hbool =>
      simp only [Statement.cmdExprs, Cmd.readExprs, List.flatMap_cons, List.flatMap_nil]
      rw [hlit (CmdType.inferType_getConsts_eq hinfer)]
  | call hproc hlhsSome hwf hlhs hsig hres hunify =>
    simp only [Statement.cmdExprs]
    refine CallArg.getInputExprs_replaceInArgs_litTyNames _ _ ?_
    have hrel := SourceExpr.resolves_getConsts_eq _ _ _ _ _ hres
    have hmap : ∀ (ets : List (LExprT CoreLParams.mono)) (es : List Expression.Expr),
        List.Rel₂ (fun t e => LExpr.getConsts t = LExpr.getConsts e) ets es →
        List.Rel₂ (fun l i => exprLitTyNames l = exprLitTyNames i)
          (ets.map LExpr.unresolved) es := by
      intro ets es hr
      induction hr with
      | nil => exact List.Rel₂.nil
      | cons hab _ ih =>
        refine List.Rel₂.cons ?_ ih
        have hunres := (Lambda.LExpr.Proofs.getConsts_unresolved _).trans hab
        exact hlit hunres
    exact hmap _ _ hrel

/-- Inferring the type of an expression keeps its erasure: inference only adds annotations. -/
private theorem CmdType.inferType_eraseTypes_eq {C : LContext CoreLParams} {Env Env' : TEnv Unit}
    {c : Cmd Expression} {e e' : Expression.Expr} {ety : LTy}
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env')) :
    e'.eraseTypes = e.eraseTypes := by
  unfold CmdType.inferType at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  elim_err h with p hp
  obtain ⟨ea, T⟩ := p
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hr := SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hp)
  exact SourceExpr.resolve_unresolved_eraseTypes _ _ _ _ _ hr

/-- Successful command checking keeps the erasure of the command: the checker adds annotations
    to the expressions and replaces the declared type of an `init`, and a call keeps its
    argument expressions up to erasure. -/
theorem Statement.typeCheckCmd_eraseAnnots_eq
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env')) :
    Command.eraseAnnots c' = Command.eraseAnnots c := by
  cases typeCheckCmd_ok_inv h with
  | cmd run =>
    cases run with
    | initDet hlookup hself hpre hinfer hunify hpost =>
      simp only [Command.eraseAnnots, Command.mapExpr, CmdType.substExpr,
        LExpr.eraseTypes_applyTypeSubst, CmdType.inferType_eraseTypes_eq hinfer]
    | initNondet => simp only [Command.eraseAnnots, Command.mapExpr]
    | setDet hlookup hinfer hunify =>
      simp only [Command.eraseAnnots, Command.mapExpr, CmdType.inferType_eraseTypes_eq hinfer]
    | setNondet => rfl
    | assert hinfer hbool =>
      simp only [Command.eraseAnnots, Command.mapExpr, CmdType.inferType_eraseTypes_eq hinfer]
    | assume hinfer hbool =>
      simp only [Command.eraseAnnots, Command.mapExpr, CmdType.inferType_eraseTypes_eq hinfer]
    | cover hinfer hbool =>
      simp only [Command.eraseAnnots, Command.mapExpr, CmdType.inferType_eraseTypes_eq hinfer]
  | call hproc hlhsSome hwf hlhs hsig hres hunify =>
    simp only [Command.eraseAnnots, Command.mapExpr]
    rw [CallArg.replaceInArgs_mapInput_eraseTypes]
    have hmap := SourceExpr.resolves_unresolved_eraseTypes _ _ _ _ _ hres
    simpa only [List.map_map, Function.comp_def] using hmap

/-- Every call of a checked command is well formed: it names a declared procedure, matches its
    signature, and has distinct result variables. -/
theorem Statement.typeCheckCmd_callsWellFormed
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env')) :
    ∀ cs ∈ Command.callSites c', WF.WFcallProp P cs.procName cs.args := by
  cases Statement.typeCheckCmd_ok_inv h with
  | cmd =>
    intro cs hcs
    simp only [Command.callSites, List.not_mem_nil] at hcs
  | call hproc _ hwf =>
    intro cs hcs
    simp only [Command.callSites, List.mem_singleton] at hcs
    subst hcs
    exact WF.WFcallProp.transfer default hwf hproc hproc rfl rfl
      (CallArg.replaceInArgs_map_mapInput_const default _ _)

/-! ## Command checking and the type environment -/

section CmdAbsorbs

open Strata.Util (HMap HMaps)

/-- `typeCheckCmd` keeps the context's scope stack nonempty. -/
theorem Statement.typeCheckCmd_preserves_context_types_ne
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (cmd cmd' : Command)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (h_ne : Env.context.types ≠ []) :
    Env'.context.types ≠ [] := by
  refine CmdRun.rel (fun E E' => E.context.types ≠ [] → E'.context.types ≠ [])
    (Statement.typeCheckCmd_ok_inv h) ?_ ?_ ?_ ?_ ?_ ?_ h_ne
  · intro E1 E2 E3 h12 h23 hne
    exact h23 (h12 hne)
  · intro E E' hg hne
    rw [hg.context]
    exact hne
  · intro E' e et hres _
    exact SourceExpr.resolve_context_types_ne C Env E' e et hres
  · intro E E' es ets _ hres hne
    exact SourceExpr.resolves_context_types_ne C E E' es ets hres hne
  · intro E cs Sx _ hne
    exact hne
  · intro E x ty _ _
    exact CmdType.update_context_types_ne E x ty

/-! ### Generator freshness and well-formedness for the Core `TypeContext` operations -/

/-- No type variable of `vs` is a generated name at or beyond the environment's current
    type-variable counter. -/
private def FreshForGen (vs : List TyIdentifier) (Env : TEnv Unit) : Prop :=
  ∀ v, v ∈ vs → ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n

/-- Generator freshness remains true when the generator counter advances. -/
private theorem FreshForGen.mono {vs : List TyIdentifier} {Env Env' : TEnv Unit}
    (h : FreshForGen vs Env) (hgen : Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen) :
    FreshForGen vs Env' := by
  intro v hv n hn
  exact h v hv n (Nat.le_trans hgen hn)

/-- Applying a well-formed environment's solved substitution preserves generator freshness of a
    monotype. -/
private theorem LMonoTy.subst_fresh (mty : LMonoTy) (Env : TEnv Unit)
    (h_mty : FreshForGen (LMonoTy.freeVars mty) Env)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) :
    FreshForGen (LMonoTy.freeVars (LMonoTy.subst Env.stateSubstInfo.subst mty)) Env := by
  intro v hv n hn
  rcases List.mem_append.mp
      (LMonoTy.freeVars_of_subst_subset Env.stateSubstInfo.subst mty hv) with
    hv_mty | hv_subst
  · exact h_mty v hv_mty n hn
  · exact h_env.substFreshForGen v (Or.inr hv_subst) n hn

/-- Applying a well-formed environment's solved substitution preserves generator freshness of a
    list of monotypes. -/
private theorem LMonoTys.subst_fresh (mtys : LMonoTys) (Env : TEnv Unit)
    (h_mtys : FreshForGen (LMonoTys.freeVars mtys) Env)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) :
    FreshForGen (LMonoTys.freeVars (LMonoTys.subst Env.stateSubstInfo.subst mtys)) Env := by
  intro v hv n hn
  rcases List.mem_append.mp
      (LMonoTys.freeVars_of_subst_subset Env.stateSubstInfo.subst mtys hv) with
    hv_mtys | hv_subst
  · exact h_mtys v hv_mtys n hn
  · exact h_env.substFreshForGen v (Or.inr hv_subst) n hn

/-- Instantiating and substituting a scheme returns a monotype fresh for the output generator. -/
private theorem LTy.instantiateAndSubst_result_fresh
    (ty : LTy) (C : LContext CoreLParams) (Env Env' : TEnv Unit) (mty : LMonoTy)
    (h : LTy.instantiateAndSubst ty C Env = .ok (mty, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) :
    FreshForGen (LMonoTy.freeVars mty) Env' := by
  simp only [LTy.instantiateAndSubst, bind, Except.bind] at h
  elim_err h with result hinst
  obtain ⟨mty0, Env0⟩ := result
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hmty, hEnv⟩ := h
  subst hmty
  subst hEnv
  have h_gen := SourceExpr.instantiateWithCheck_genOnly ty C Env Env0 mty0 hinst
  exact LMonoTy.subst_fresh mty0 Env0
    (LExpr.LTy_instantiateWithCheck_freeVars_fresh ty C Env mty0 Env0 hinst)
    (h_gen.envWF h_env)

/-- Reading one identifier's instantiated type returns a monotype fresh for the output
    generator. -/
private theorem Identifier.instantiateAndSubst_result_fresh
    (x : CoreIdent) (C : LContext CoreLParams) (Env Env' : TEnv Unit) (mty : LMonoTy)
    (h : Lambda.Identifier.instantiateAndSubst x C Env = .ok (some (mty, Env')))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) :
    FreshForGen (LMonoTy.freeVars mty) Env' := by
  simp only [Lambda.Identifier.instantiateAndSubst] at h
  cases hfind : Env.context.types.find? x with
  | none => rw [hfind] at h; exact absurd h (by simp [pure, Except.pure])
  | some ty =>
    rw [hfind] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases hinst : LTy.instantiateAndSubst ty C Env with
    | error e =>
      rw [hinst] at h
      exact absurd h (by simp)
    | ok result =>
      obtain ⟨mty0, Env0⟩ := result
      rw [hinst] at h
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hmty, hEnv⟩ := h
      subst hmty
      subst hEnv
      exact LTy.instantiateAndSubst_result_fresh ty C Env Env0 mty0 hinst h_env

/-- Reading a list of identifiers returns monotypes fresh for the final output generator. -/
private theorem Identifier.instantiateAndSubsts_result_fresh
    (xs : List CoreIdent) (C : LContext CoreLParams) (Env : TEnv Unit)
    (mtys : LMonoTys) (Env' : TEnv Unit)
    (h : Lambda.Identifier.instantiateAndSubsts xs C Env = .ok (some (mtys, Env')))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) :
    FreshForGen (LMonoTys.freeVars mtys) Env' := by
  induction xs generalizing Env mtys with
  | nil =>
    simp only [Lambda.Identifier.instantiateAndSubsts, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hmtys, hEnv⟩ := h
    subst hmtys
    subst hEnv
    intro v hv
    exact absurd hv (by simp [LMonoTys.freeVars])
  | cons x xrest ih =>
    obtain ⟨xty, EnvA, xtys, hhd, htl, rfl⟩ := Lambda.Identifier.instantiateAndSubsts_cons_inv h
    have h_gen_hd :=
      Identifier.instantiateAndSubst_genOnly x C Env EnvA xty hhd
    have h_gen_tl :=
      Identifier.instantiateAndSubsts_genOnly xrest C EnvA xtys Env' htl
    have h_fresh_hd :=
      Identifier.instantiateAndSubst_result_fresh x C Env EnvA xty hhd h_env
    have h_fresh_tl := ih EnvA xtys htl (h_gen_hd.envWF h_env)
    intro v hv
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    rcases hv with hv | hv
    · exact FreshForGen.mono h_fresh_hd h_gen_tl.tyGen v hv
    · exact h_fresh_tl v hv

/-- Signature-instantiation's per-entry loop returns monotypes fresh for its final generator. -/
private theorem LMonoTySignature.instantiate_go_result_fresh
    (C : LContext CoreLParams) (tys : LTys) :
    ∀ (Env EnvR : TEnv Unit) (rtys : LMonoTys),
      LMonoTySignature.instantiate.go (T := CoreLParams) C Env tys = .ok (rtys, EnvR) →
      FreshForGen (LMonoTys.freeVars rtys) EnvR := by
  induction tys with
  | nil =>
    intro Env EnvR rtys h
    simp only [LMonoTySignature.instantiate.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hrtys, hEnv⟩ := h
    subst hrtys
    subst hEnv
    intro v hv
    exact absurd hv (by simp [LMonoTys.freeVars])
  | cons ty trest ih =>
    intro Env EnvR rtys h
    obtain ⟨mty, EnvA, mtys, hhd, htl, rfl⟩ := LMonoTySignature.instantiate_go_cons_inv h
    have h_gen_tl :=
      LMonoTySignature.instantiate_go_genOnly C trest EnvA EnvR mtys htl
    have h_fresh_hd :=
      LExpr.LTy_instantiateWithCheck_freeVars_fresh ty C Env mty EnvA hhd
    have h_fresh_tl := ih EnvA EnvR mtys htl
    intro v hv
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    rcases hv with hv | hv
    · exact FreshForGen.mono h_fresh_hd h_gen_tl.tyGen v hv
    · exact h_fresh_tl v hv

/-- Instantiating a procedure signature returns values fresh for the output generator. -/
private theorem LMonoTySignature.instantiate_result_fresh
    (C : LContext CoreLParams) (Env EnvR : TEnv Unit) (tyArgs : List TyIdentifier)
    (sig sig' : @LMonoTySignature Unit)
    (h : LMonoTySignature.instantiate C Env tyArgs sig = .ok (sig', EnvR)) :
    FreshForGen (LMonoTys.freeVars sig'.values) EnvR := by
  simp only [LMonoTySignature.instantiate, bind, Except.bind] at h
  elim_err h with result hinst
  obtain ⟨mtys, EnvA⟩ := result
  elim_err h with result hgo
  obtain ⟨newtys, EnvB⟩ := result
  obtain ⟨hsig, hEnv⟩ := Prod.mk.inj (Except.ok.inj h)
  subst hsig
  subst hEnv
  have h_fresh :=
    LMonoTySignature.instantiate_go_result_fresh C
      (mtys.map (fun mty => LTy.forAll [] mty)) EnvA EnvB newtys hgo
  intro v hv
  obtain ⟨mty, hmty, hv⟩ := LMonoTys.freeVars_exists hv
  exact h_fresh v
    (LMonoTys.freeVars_mem_subset (ListMap.mem_values_zip sig.keys newtys mty hmty) hv)

/-- Core source resolution returns a type fresh for its final generator. -/
private theorem resolveSource_result_type_fresh
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (h : SourceExpr.resolve C Env e = .ok (et, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    FreshForGen (LMonoTy.freeVars et.toLMonoTy) Env' := by
  change SourceExpr.resolve C Env e = .ok (et, Env') at h
  obtain ⟨EnvR, hresolve, hgen⟩ :=
    SourceExpr.resolve_link_genState_tyGen_mono C Env Env' e et h
  exact FreshForGen.mono
    (resolve_result_type_fresh C Env EnvR e et hresolve h_env h_fac) hgen

/-- Resolving a list of source expressions returns result types fresh for the final generator. -/
private theorem resolveSources_result_types_fresh
    (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (es : List Expression.Expr) (ets : List (LExprT CoreLParams.mono))
    (h : SourceExpr.resolves C Env es = .ok (ets, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    FreshForGen (LMonoTys.freeVars (ets.map LExpr.toLMonoTy)) Env' := by
  change SourceExpr.resolves C Env es = .ok (ets, Env') at h
  induction es generalizing Env ets with
  | nil =>
    rw [SourceExpr.resolves_nil] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hets, hEnv⟩ := h
    subst hets
    subst hEnv
    intro v hv
    exact absurd hv (by simp [LMonoTys.freeVars])
  | cons e rest ih =>
    obtain ⟨et, EnvA, typedRest, hhead, htail, rfl⟩ := SourceExpr.resolves_cons_inv h
    have h_head_fresh :=
      resolveSource_result_type_fresh e et C Env EnvA hhead h_env h_fac
    have h_tail_gen :=
      SourceExpr.resolves_genState_tyGen_mono C EnvA Env' rest typedRest htail
    have h_tail_fresh :=
      ih EnvA typedRest
        (SourceExpr.resolve_TEnvWF C Env EnvA e et hhead h_env h_fac) htail
    intro v hv
    simp only [List.map_cons, LMonoTys.freeVars_of_cons, List.mem_append] at hv
    rcases hv with hv | hv
    · exact FreshForGen.mono h_head_fresh h_tail_gen v hv
    · exact h_tail_fresh v hv

/-- Successful preprocessing returns an unquantified scheme whose free variables are fresh for
    the output generator. -/
private theorem CmdType.preprocess_mono_fresh
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (ty ty' : LTy)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    LTy.boundVars ty' = [] ∧ FreshForGen (LTy.freeVars ty') Env' := by
  obtain ⟨m0, mty, -, rfl, hinst⟩ := preprocess_instantiateWithCheck C Env Env' ty ty' h
  have hfresh : FreshForGen (LTy.freeVars (.forAll [] mty)) Env' := by
    simpa only [FreshForGen, LTy.freeVars, List.removeAll_nil] using
      LExpr.LTy_instantiateWithCheck_freeVars_fresh (LTy.forAll [] m0) C Env mty Env' hinst
  exact ⟨rfl, hfresh⟩

/-- Successful expression inference preserves `TEnvWF`, never decreases the generator, and
    returns an unquantified generator-fresh type. -/
private theorem CmdType.inferType_TEnvWF
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (cmd : Cmd Expression)
    (e e' : Expression.Expr) (ty : LTy)
    (h : CmdType.inferType C Env cmd e = .ok (e', ty, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env' ∧
      Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen ∧
      LTy.boundVars ty = [] ∧ FreshForGen (LTy.freeVars ty) Env' := by
  obtain ⟨et, hresolve, -, rfl⟩ := CmdType.inferType_inv C Env Env' cmd e e' ty h
  have hfresh : FreshForGen (LTy.freeVars (.forAll [] et.toLMonoTy)) Env' := by
    simpa only [FreshForGen, LTy.freeVars, List.removeAll_nil] using
      resolveSource_result_type_fresh e et C Env Env' hresolve h_env h_fac
  exact
    ⟨SourceExpr.resolve_TEnvWF C Env Env' e et hresolve h_env h_fac,
     SourceExpr.resolve_genState_tyGen_mono C Env Env' e et hresolve,
     rfl, hfresh⟩

/-- Successful postprocessing returns an unquantified fresh scheme and the unchanged
    environment. -/
private theorem CmdType.postprocess_mono_fresh
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (ty ty' : LTy)
    (h : CmdType.postprocess C Env ty = .ok (ty', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fresh : FreshForGen (LTy.freeVars ty) Env) :
    Env' = Env ∧ LTy.boundVars ty' = [] ∧ FreshForGen (LTy.freeVars ty') Env' := by
  rcases ty with ⟨vars, mty⟩
  cases vars with
  | cons _ _ =>
    simp only [CmdType.postprocess, LTy.isMonoType, LTy.boundVars, List.isEmpty_cons,
      Bool.false_eq_true, ↓reduceDIte, reduceCtorEq] at h
  | nil =>
    simp only [CmdType.postprocess, LTy.isMonoType, LTy.boundVars, List.isEmpty_nil,
      ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hty, hEnv⟩ := h
    subst hty
    subst hEnv
    refine ⟨rfl, rfl, ?_⟩
    have hfreshM : FreshForGen (LMonoTy.freeVars mty) Env := by
      simpa only [FreshForGen, LTy.freeVars, List.removeAll_nil]
        using h_fresh
    simpa only [FreshForGen, LTy.freeVars, List.removeAll_nil,
      LTy.toMonoType] using
      LMonoTy.subst_fresh mty Env hfreshM h_env

/-- Successful singleton constraint solving preserves `TEnvWF` when both source schemes are
    generator-fresh. -/
private theorem CmdType.unifyTypes_single_TEnvWF
    (Env Env' : TEnv Unit) (ty1 ty2 : LTy)
    (h : CmdType.unifyTypes Env [(ty1, ty2)] = .ok Env')
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fresh1 : FreshForGen (LTy.freeVars ty1) Env)
    (h_fresh2 : FreshForGen (LTy.freeVars ty2) Env) :
    LExpr.TEnvWF (T := CoreLParams) Env' := by
  rcases ty1 with ⟨vars1, mty1⟩
  rcases ty2 with ⟨vars2, mty2⟩
  cases vars1 with
  | cons _ _ =>
    simp only [CmdType.unifyTypes, CmdType.canonicalizeConstraints, LTy.isMonoType,
      LTy.boundVars, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, ↓reduceDIte,
      bind, Except.bind, reduceCtorEq] at h
  | nil =>
    cases vars2 with
    | cons y ys =>
      simp only [CmdType.unifyTypes, CmdType.canonicalizeConstraints, LTy.isMonoType,
        LTy.boundVars, List.isEmpty_nil, List.isEmpty_cons, Bool.true_and,
        Bool.false_eq_true, ↓reduceDIte, bind, Except.bind, reduceCtorEq] at h
    | nil =>
      simp only [CmdType.unifyTypes, CmdType.canonicalizeConstraints, LTy.isMonoType,
        LTy.boundVars, List.isEmpty_nil, Bool.true_and, ↓reduceDIte,
        LTy.toMonoType, bind, Except.bind] at h
      elim_err h with S hunify
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hunify' : Constraints.unify [(mty1, mty2)] Env.stateSubstInfo = .ok S :=
        Except.mapError_ok_h' hunify
      apply LExpr.TEnvWF_updateSubst_of_unify (T := CoreLParams)
        Env [(mty1, mty2)] S h_env hunify'
      intro v hv n hn
      simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
        List.mem_append] at hv
      rcases hv with hv | hv
      · have hv1 : v ∈ LTy.freeVars (.forAll [] mty1) := by
          simpa only [FreshForGen, LTy.freeVars, List.removeAll_nil] using hv
        exact h_fresh1 v hv1 n hn
      · have hv2 : v ∈ LTy.freeVars (.forAll [] mty2) := by
          simpa only [FreshForGen, LTy.freeVars, List.removeAll_nil] using hv
        exact h_fresh2 v hv2 n hn

/-- Constraint solving keeps the generator counter. -/
private theorem CmdType.unifyTypes_tyGen_eq
    (Env Env' : TEnv Unit) (constraints : List (LTy × LTy))
    (h : CmdType.unifyTypes Env constraints = .ok Env') :
    Env'.genEnv.genState.tyGen = Env.genEnv.genState.tyGen := by
  simp only [CmdType.unifyTypes, bind, Except.bind] at h
  elim_err h
  elim_err h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst Env'
  rfl

/-- Adding an unquantified, generator-fresh local type preserves type-environment
    well-formedness. -/
private theorem CmdType.update_TEnvWF
    (Env : TEnv Unit) (x : CoreIdent) (ty : LTy)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_bound : LTy.boundVars ty = [])
    (h_fresh : FreshForGen (LTy.freeVars ty) Env) :
    LExpr.TEnvWF (T := CoreLParams) (CmdType.update Env x ty) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_env.aliasesWF
  · exact h_env.substFreshForGen
  · intro v hv n hn
    simp only [CmdType.update_eq_single, TEnv.addInNewestContext, TEnv.updateContext,
      TEnv.context, TContext.knownTypeVars, List.mem_flatMap] at hv
    obtain ⟨stored, hstored, hv⟩ := hv
    rcases Strata.Util.HMaps.mem_values_addInNewest_single
        Env.context.types x ty stored hstored with hstored | rfl
    · have hknown : v ∈ TContext.knownTypeVars Env.context := by
        simp only [TContext.knownTypeVars, List.mem_flatMap]
        exact ⟨stored, hstored, hv⟩
      exact h_env.ctxFreshForGen v hknown n hn
    · exact h_fresh v hv n hn
  · intro y stored hy
    simp only [CmdType.update_eq_single, TEnv.addInNewestContext, TEnv.updateContext,
      TEnv.context] at hy
    change (Env.context.types.addInNewest (HMap.single x ty)).find? y = some stored at hy
    rcases HMaps.find?_addInNewest_single Env.context.types x ty y with hnew | hold
    · obtain ⟨hnew, -⟩ := hnew
      rw [hnew] at hy
      simp only [Option.some.injEq] at hy
      subst hy
      rw [h_bound]
      exact List.nodup_nil
    · rw [hold] at hy
      exact h_env.boundVarsNodup y stored hy
  · intro y stored hy v hv n hn
    simp only [CmdType.update_eq_single, TEnv.addInNewestContext, TEnv.updateContext,
      TEnv.context] at hy
    change (Env.context.types.addInNewest (HMap.single x ty)).find? y = some stored at hy
    change n ≥ Env.genEnv.genState.tyGen at hn
    rcases HMaps.find?_addInNewest_single Env.context.types x ty y with hnew | hold
    · obtain ⟨hnew, -⟩ := hnew
      rw [hnew] at hy
      simp only [Option.some.injEq] at hy
      subst hy
      rw [h_bound] at hv
      exact absurd hv (by simp)
    · rw [hold] at hy
      exact h_env.boundVarsFresh y stored hy v hv n hn

/-! ### Command checking preserves well-formedness and never decreases the generator -/

/-- An accepting imperative-command run preserves type-environment well-formedness. -/
private theorem imperativeCmd_preserves_TEnvWF
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (cmd cmd' : Cmd Expression)
    (run : ImperativeCmdRun C Env cmd cmd' Env')
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env' := by
  cases run with
  | @initDet x xty xtyP ety xtyQ expr exprA md Env1 Env2 Env3 Env4 hlookup hself hp hi hu hq =>
    have hpre : Env1 = Env := CmdType.preprocess_env_eq C Env Env1 xty xtyP hp
    obtain ⟨hboundP, hfreshP⟩ :=
      CmdType.preprocess_mono_fresh C Env Env1 xty xtyP hp
    rw [hpre] at hi hfreshP
    obtain ⟨hEnv2WF, hgen2, -, hfreshE⟩ :=
      CmdType.inferType_TEnvWF C Env Env2 _ _ exprA ety hi h_env h_fac
    have hfreshP2 : FreshForGen (LTy.freeVars xtyP) Env2 := FreshForGen.mono hfreshP hgen2
    have hEnv3WF :=
      CmdType.unifyTypes_single_TEnvWF Env2 Env3 xtyP ety hu hEnv2WF hfreshP2 hfreshE
    have hgen3 := CmdType.unifyTypes_tyGen_eq Env2 Env3 _ hu
    have hfreshP3 : FreshForGen (LTy.freeVars xtyP) Env3 :=
      FreshForGen.mono hfreshP2 (Nat.le_of_eq hgen3.symm)
    obtain ⟨hpost, hboundQ, hfreshQ⟩ :=
      CmdType.postprocess_mono_fresh C Env3 Env4 xtyP xtyQ hq hEnv3WF hfreshP3
    rw [hpost] at hfreshQ
    rw [hpost]
    exact CmdType.update_TEnvWF Env3 x xtyQ hEnv3WF hboundQ hfreshQ
  | @initNondet x xty xtyP xtyQ md Env1 Env2 hlookup hp hq =>
    have hpre : Env1 = Env := CmdType.preprocess_env_eq C Env Env1 xty xtyP hp
    have hEnv1WF : LExpr.TEnvWF (T := CoreLParams) Env1 := by
      rw [hpre]
      exact h_env
    obtain ⟨-, hfreshP⟩ := CmdType.preprocess_mono_fresh C Env Env1 xty xtyP hp
    obtain ⟨hpost, hboundQ, hfreshQ⟩ :=
      CmdType.postprocess_mono_fresh C Env1 Env2 xtyP xtyQ hq hEnv1WF hfreshP
    rw [hpost] at hfreshQ
    rw [hpost]
    exact CmdType.update_TEnvWF Env1 x xtyQ hEnv1WF hboundQ hfreshQ
  | @setDet x xty ety expr exprA md Env2 _ hlookup hi hu =>
    obtain ⟨hEnv2WF, hgen2, -, hfreshE⟩ :=
      CmdType.inferType_TEnvWF C Env Env2 _ _ exprA ety hi h_env h_fac
    have hfreshX : FreshForGen (LTy.freeVars (Env.context.resolveScheme xty)) Env2 := by
      intro v hv n hn
      exact h_env.ctxFreshForGen v
        (TContext.mem_knownTypeVars_of_find hlookup
          (TContext.resolveScheme_freeVars_subset h_env.aliasesWF xty v hv)) n
        (Nat.le_trans hgen2 hn)
    exact CmdType.unifyTypes_single_TEnvWF Env2 Env' _ ety hu hEnv2WF hfreshX hfreshE
  | setNondet => exact h_env
  | assert hi | assume hi | cover hi =>
    exact (CmdType.inferType_TEnvWF C Env _ _ _ _ _ hi h_env h_fac).1

/-- `typeCheckCmd` never decreases the type-variable generator counter. -/
theorem Statement.typeCheckCmd_genState_tyGen_mono
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (cmd cmd' : Command)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env')) :
    Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen := by
  refine CmdRun.rel (fun E E' => E.genEnv.genState.tyGen ≤ E'.genEnv.genState.tyGen)
    (Statement.typeCheckCmd_ok_inv h) ?_ ?_ ?_ ?_ ?_ ?_
  · intro E1 E2 E3 h12 h23
    exact Nat.le_trans h12 h23
  · intro E E' hg
    exact hg.tyGen
  · intro E' e et hres
    exact SourceExpr.resolve_genState_tyGen_mono C Env E' e et hres
  · intro E E' es ets _ hres
    exact SourceExpr.resolves_genState_tyGen_mono C E E' es ets hres
  · intro E cs Sx _
    exact Nat.le_refl _
  · intro E x ty _
    simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext]
    exact Nat.le_refl _

/-- `typeCheckCmd` preserves `TEnvWF`. -/
theorem Statement.typeCheckCmd_preserves_TEnvWF
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (cmd cmd' : Command)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env' := by
  cases Statement.typeCheckCmd_ok_inv h with
  | cmd run => exact imperativeCmd_preserves_TEnvWF C Env _ _ _ run h_env h_fac
  | @call nm tyArgs callArgs md proc lhs_tys io_sig argsa Env1 Env2 Env3 S
      instTys EnvA hproc hlhsSome hwf hlhs hsig hres hunify hargs =>
    have hg1 : SourceExpr.GenOnly Env Env1 :=
      Identifier.instantiateAndSubsts_genOnly _ C Env lhs_tys Env1 hlhs
    have hg2 : SourceExpr.GenOnly Env1 Env2 :=
      LMonoTySignature.instantiate_genOnly C Env1 Env2 _ _ io_sig hsig
    have hEnv2WF := (hg1.trans hg2).envWF h_env
    have hEnv3WF := SourceExpr.resolves_TEnvWF C Env2 Env3 _ argsa hres hEnv2WF h_fac
    have hgen3 := SourceExpr.resolves_genState_tyGen_mono C Env2 Env3 _ argsa hres
    have hlhsFresh :=
      Identifier.instantiateAndSubsts_result_fresh _ C Env lhs_tys Env1 hlhs h_env
    have hlhsFresh3 := FreshForGen.mono hlhsFresh (Nat.le_trans hg2.tyGen hgen3)
    have hsigFresh :=
      LMonoTySignature.instantiate_result_fresh C Env1 Env2 _ _ io_sig hsig
    have hioFresh := LMonoTys.subst_fresh io_sig.values Env2 hsigFresh hEnv2WF
    have hioFresh3 := FreshForGen.mono hioFresh hgen3
    have hsubFresh : ∀ l : LMonoTys,
        l ⊆ LMonoTys.subst Env2.stateSubstInfo.subst io_sig.values →
          FreshForGen (LMonoTys.freeVars l) Env3 := by
      intro l hl v hv n hn
      obtain ⟨mty, hmty, hvm⟩ := LMonoTys.freeVars_exists hv
      exact hioFresh3 v (LMonoTys.freeVars_mem_subset (hl hmty) hvm) n hn
    have hargsFresh :=
      resolveSources_result_types_fresh C Env2 Env3 _ argsa hres hEnv2WF h_fac
    apply LExpr.TEnvWF_updateSubst_of_unify (T := CoreLParams) Env3 _ S hEnv3WF hunify
    intro v hv n hn
    rw [Constraints.freeVars_append] at hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp (Constraints.freeVars_of_zip_subset hv) with hv | hv
      · exact hargsFresh v hv n hn
      · exact hsubFresh _ (List.take_subset _ _) v hv n hn
    · rcases List.mem_append.mp (Constraints.freeVars_of_zip_subset hv) with hv | hv
      · exact hlhsFresh3 v hv n hn
      · exact hsubFresh _ (List.drop_subset _ _) v hv n hn

/-- Checking a command that is not a variable declaration keeps the typing context
    lookup-equivalent. -/
theorem Statement.typeCheckCmd_noInit_context_equiv
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (cmd cmd' : Command)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (hni : ∀ x xty e md, cmd ≠ .cmd (.init x xty e md))
    (hne : Env.context.types ≠ []) :
    TContext.Equiv (T := CoreLParams) Env'.context Env.context := by
  refine CmdRun.rel (fun E E' => TContext.Equiv (T := CoreLParams) E'.context E.context)
    (Statement.typeCheckCmd_ok_inv h) ?_ ?_ ?_ ?_ ?_ ?_
  · intro E1 E2 E3 h12 h23
    exact h23.trans h12
  · intro E E' hg
    exact TContext.Equiv.of_eq hg.context
  · intro E' e et hres
    exact SourceExpr.resolve_context_equiv_of_ne C Env E' e et hres hne
  · intro E E' es ets hg hres
    change SourceExpr.resolves C E es = .ok (ets, E') at hres
    have hneE : E.context.types ≠ [] := hg.context ▸ hne
    exact (SourceExpr.resolves_preserves C
      (fun X => TContext.Equiv (T := CoreLParams) X.context E.context)
      (fun _ => True)
      (fun X X' e et hrs hX =>
        ⟨(SourceExpr.resolve_context_equiv_of_ne C X X' e et hrs
          (hX.symm.types_ne_nil hneE)).trans hX, trivial⟩)
      E E' es ets hres (TContext.Equiv.refl _)).1
  · intro E cs Sx _
    exact TContext.Equiv.refl _
  · intro E x ty hinit
    obtain ⟨x', xty, e, md, hc⟩ := hinit
    exact absurd hc (hni x' xty e md)

/-- `typeCheckCmd` preserves alias resolution. -/
theorem Statement.typeCheckCmd_preserves_aliasesResolved
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (cmd cmd' : Command)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (h_resolved : TContext.AliasesResolved Env.context) :
    TContext.AliasesResolved Env'.context := by
  have h_aliases :
      Env'.context.aliases = Env.context.aliases :=
    (Statement.typeCheckCmd_preserves_context C Env Env' P cmd cmd' h).2
  unfold TContext.AliasesResolved at h_resolved ⊢
  rw [h_aliases]
  exact h_resolved

/-! ### The Core command checker refines the substitution -/

/-- Checking a Core command only refines the solved substitution: the output one absorbs the
    input one. -/
theorem Statement.typeCheckCmd_absorbs
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (cmd cmd' : Command)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  refine CmdRun.rel (fun E E' => Subst.absorbs E'.stateSubstInfo.subst E.stateSubstInfo.subst)
    (Statement.typeCheckCmd_ok_inv h) ?_ ?_ ?_ ?_ ?_ ?_
  · intro E1 E2 E3 h12 h23
    exact Subst.absorbs_trans _ _ _ h12 h23
  · intro E E' hg
    rw [hg.subst]
    exact Subst.absorbs_refl _ E.stateSubstInfo.isWF
  · intro E' e et hres
    exact resolveSource_absorbs e et C Env E' hres he hf
  · intro E E' es ets hg hres
    exact (SourceExpr.resolves_step C E E' es ets hres (hg.envWF he) hf).2.2.2.1
  · intro E cs Sx hu
    exact Constraints.unify_absorbs cs E.stateSubstInfo Sx hu
  · intro E x ty _
    exact Subst.absorbs_refl _ E.stateSubstInfo.isWF

/-! ### Commands keep the environment free of parameter-named type variables -/

/-- Checking a command whose annotations avoid `ps` keeps the environment avoiding `ps`. -/
theorem Statement.typeCheckCmd_varsAvoid {ps : List TyIdentifier}
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hne : Env.context.types ≠ [])
    (hf : FactorySigWF C.functions) (hgen : NoGenName ps) (hsigs : ProcSigsDeclared P)
    (hc : Command.VarsAvoid ps c) (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Env' ps := by
  have hinfer : ∀ {cmd : Cmd Expression} {e e' : Expression.Expr} {ety : LTy} {E' : TEnv Unit},
      CmdType.inferType C Env cmd e = .ok (e', ety, E') → LExpr.AnnotsAvoid e ps →
      TEnv.VarsAvoid E' ps ∧ ∀ v ∈ LTy.freeVars ety, v ∉ ps := by
    intro cmd e e' ety E' hi hsrc
    obtain ⟨ea, hr, -, rfl⟩ := CmdType.inferType_inv C Env E' cmd e e' ety hi
    obtain ⟨hE', hty⟩ := SourceExpr.resolve_varsAvoid C Env E' e ea hr he hne hf hgen hsrc hE
    refine ⟨hE', ?_⟩
    rw [LTy.freeVars_forAll_nil]
    exact hty
  have hunifyTypes : ∀ {E E' : TEnv Unit} {t1 t2 : LTy}, CmdType.unifyTypes E [(t1, t2)] = .ok E' →
      TEnv.VarsAvoid E ps → (∀ v ∈ LTy.freeVars t1, v ∉ ps) → (∀ v ∈ LTy.freeVars t2, v ∉ ps) →
      TEnv.VarsAvoid E' ps := by
    intro E E' t1 t2 hu hEu h1 h2
    obtain ⟨a, b, Sx, rfl, rfl, hun, rfl⟩ := CmdType.unifyTypes_inv E E' t1 t2 hu
    refine ⟨Constraints.unify_varsAvoid hun hEu.1 (Constraints.freeVars_varsAvoid ?_), hEu.2⟩
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    rw [LTy.freeVars_forAll_nil] at h1 h2
    exact ⟨h1, h2⟩
  have hupdate : ∀ {E : TEnv Unit} {x : CoreIdent} {ty : LTy}, TEnv.VarsAvoid E ps →
      (∀ v ∈ LTy.freeVars ty, v ∉ ps) → TEnv.VarsAvoid (CmdType.update E x ty) ps := by
    intro E x ty hEu hty
    rw [CmdType.update_eq_single]
    refine hEu.addInNewestContext _ ?_
    intro t ht
    rw [(Strata.Util.HMap.mem_values_single_iff x ty t).mp ht]
    exact hty
  have hdecl : ∀ {xty xtyP : LTy} {E1 : TEnv Unit}, CmdType.preprocess C Env xty = .ok (xtyP, E1) →
      (∀ v ∈ LTy.freeVars xty, v ∉ ps) →
      ∃ mtyP, xtyP = .forAll [] mtyP ∧ E1 = Env ∧ ∀ v ∈ LMonoTy.freeVars mtyP, v ∉ ps := by
    intro xty xtyP E1 hpre hty
    obtain ⟨m0, mtyP, rfl, rfl, hE1, hae, -⟩ := CmdType.preprocess_inv C Env E1 xty xtyP hpre
    refine ⟨mtyP, rfl, hE1, fun v hv => hty v ?_⟩
    rw [LTy.freeVars_forAll_nil]
    exact (AliasEquiv.freeVars_iff he.aliasesWF.mem hae v).mpr hv
  cases Statement.typeCheckCmd_ok_inv h with
  | cmd run =>
    cases run with
    | initDet hlookup hself hpre hinf hunif hpost =>
      obtain ⟨hty, hexpr⟩ := hc
      obtain ⟨mtyP, rfl, rfl, hmtyP⟩ := hdecl hpre hty
      obtain ⟨hE2, hety⟩ := hinfer hinf (hexpr _ rfl)
      have hxtyP : ∀ v ∈ LTy.freeVars (.forAll [] mtyP), v ∉ ps := by
        rw [LTy.freeVars_forAll_nil]
        exact hmtyP
      have hE3 := hunifyTypes hunif hE2 hxtyP hety
      obtain ⟨rfl, rfl⟩ := CmdType.postprocess_inv C _ _ mtyP _ hpost
      refine hupdate hE3 ?_
      rw [LTy.freeVars_forAll_nil]
      exact LMonoTy.subst_varsAvoid hE3.1 hmtyP
    | initNondet hlookup hpre hpost =>
      obtain ⟨mtyP, rfl, rfl, hmtyP⟩ := hdecl hpre hc.1
      obtain ⟨rfl, rfl⟩ := CmdType.postprocess_inv C _ _ mtyP _ hpost
      refine hupdate hE ?_
      rw [LTy.freeVars_forAll_nil]
      exact LMonoTy.subst_varsAvoid hE.1 hmtyP
    | setDet hlookup hinf hunif =>
      obtain ⟨hE1, hety⟩ := hinfer hinf (hc _ rfl)
      exact hunifyTypes hunif hE1
        (fun v hv => hE.2 v (TContext.mem_knownTypeVars_of_find (T := CoreLParams) hlookup
          (TContext.resolveScheme_freeVars_subset he.aliasesWF _ v hv)))
        hety
    | setNondet => exact hE
    | assert hinf | assume hinf | cover hinf => exact (hinfer hinf hc).1
  | @call nm tyArgs callArgs md proc lhs_tys io_sig argsa Env1 Env2 Env3 Suni
      instTys EnvA hproc _ _ hlhs hsig hres hunif hargs =>
    obtain ⟨hE1, hlhsTys⟩ :=
      LExpr.Identifier.instantiateAndSubsts_varsAvoid _ C Env _ _ hlhs he.aliasesWF hgen hE
    have hg1 := Identifier.instantiateAndSubsts_genOnly _ C Env _ _ hlhs
    have hg2 := LMonoTySignature.instantiate_genOnly C _ _ _ _ _ hsig
    have hE2 : TEnv.VarsAvoid Env2 ps := ⟨hg2.subst ▸ hE1.1, hg2.context ▸ hE1.2⟩
    have hsigVals : ∀ v ∈ LMonoTys.freeVars io_sig.values, v ∉ ps := by
      intro v hv
      have hclosed : ∀ v ∈ LMonoTys.freeVars (ListMap.values (proc.header.inputs ++
          proc.header.outputs)), v ∈ proc.header.typeArgs := by
        intro w hw
        rw [ListMap.values_append, LExpr.LMonoTys.freeVars_append] at hw
        exact hsigs nm proc hproc w hw
      obtain ⟨k, rfl⟩ := LExpr.LMonoTySignature_instantiate_freeVars_genName C Env1 Env2 _ _ io_sig
        hsig (hg1.context ▸ he.aliasesWF) hclosed v hv
      exact hgen k
    have hg12 := hg1.trans hg2
    have hne2 : Env2.context.types ≠ [] := by
      rw [hg12.context]
      exact hne
    obtain ⟨hE3, hargTys⟩ := SourceExpr.resolves_varsAvoid C Env2 Env3 _ argsa hres
      (hg12.envWF he) hne2 hf hgen hc hE2
    have hsubstVals : ∀ t ∈ LMonoTys.subst Env2.stateSubstInfo.subst io_sig.values,
        ∀ v ∈ LMonoTy.freeVars t, v ∉ ps := by
      intro t ht
      rw [LMonoTys.subst_eq_map] at ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact LMonoTy.subst_varsAvoid hE2.1
        (fun v hv => hsigVals v (LMonoTys.freeVars_mem_subset hu hv))
    refine ⟨Constraints.unify_varsAvoid hunif hE3.1 (Constraints.freeVars_varsAvoid ?_), hE3.2⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨h1, h2⟩ := List.of_mem_zip hp
      obtain ⟨et, het, heq⟩ := List.mem_map.mp h1
      refine ⟨heq ▸ hargTys et het, hsubstVals _ (List.mem_of_mem_take h2)⟩
    · obtain ⟨h1, h2⟩ := List.of_mem_zip hp
      exact ⟨hlhsTys _ h1, hsubstVals _ (List.mem_of_mem_drop h2)⟩

end CmdAbsorbs

end Core

end -- public section
