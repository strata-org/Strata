/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementType
public import Strata.Languages.Core.Typing.Props.StatementTypeProps
public import Strata.Languages.Core.FunctionType
public import Strata.Languages.Core.Typing.Spec.StatementTypeSpec
public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.Languages.Core.Typing.Soundness.Command
public import Strata.Languages.Core.Typing.Soundness.Function
public import Strata.Languages.Core.Typing.Soundness.WrittenTyVarScope
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.Denote.LExprAnnotatedProps
public import Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.Denote.LExprResolveAnnotated
public import Strata.Util.HMapsProps
public import Strata.Util.ListMapProps
public import Strata.Util.ListUtilsProps
import Strata.Languages.Core.StatementProps
import Strata.Languages.Core.WrittenTyVarScope
import Strata.Languages.Core.Typing.Soundness.TypeDecl
import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import Strata.Languages.Core.Typing.Spec.CommandTypeSpec
import Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
import Strata.DL.Lambda.LExprAnnotRel
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.CmdType
import Strata.Languages.Core.CmdType
import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.DL.Imperative.StmtProps
import Strata.Languages.Core.StatementProps
import Strata.DL.Lambda.LTyUnify
import Strata.DL.Lambda.LExprProps
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.Languages.Core.TypeDecl
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LTyProps
import all Strata.Languages.Core.Typing.Spec.NamesWF
public import Strata.Languages.Core.Typing.Soundness.Statement
import all Strata.Languages.Core.Typing.Soundness.Statement

/-! # Output soundness of the executable statement typechecker
Key result: `Statement.typeCheck_sound_output`. -/

namespace Core

open Lambda Imperative
open TypeSpec
open WrittenTyVarScope (ScopeMap ScopeState renameCmd renameExpr renameExprOrNondet
  unboundAnnotVar?)

public section

section OutputSubstStability

open Strata.Util (HMaps)

/-! ## Output soundness of command checking -/

section CommandOutput

/-- Preprocessing a declared type returns the environment unchanged and a bound-variable-free
    scheme whose body is well-kinded. -/
private theorem preprocess_inv (C : LContext CoreLParams) (Env Env1 : TEnv Unit)
    (xty ty1 : LTy) (h : CmdType.preprocess C Env xty = .ok (ty1, Env1)) :
    ∃ mtyP, ty1 = .forAll [] mtyP ∧ Env1 = Env ∧ C.WellKindedTy mtyP := by
  obtain ⟨m0, mtyP, -, rfl, hinst⟩ := preprocess_instantiateWithCheck C Env Env1 xty ty1 h
  obtain ⟨hE1, -, -, hknown⟩ := instantiateWithCheck_forAll_nil_env_eq C Env Env1 m0 mtyP hinst
  exact ⟨mtyP, rfl, hE1, LMonoTy.knownInstance_wellKinded mtyP C.knownTypes hknown⟩

/-- Unifying one pair of bound-variable-free schemes succeeds only by unifying their monotype
    bodies, and the resulting environment records that solution. -/
private theorem unifyTypes_pair_inv (Env Env3 : TEnv Unit) (a b : LMonoTy)
    (h : CmdType.unifyTypes Env [(.forAll [] a, .forAll [] b)] = .ok Env3) :
    ∃ Sx, Constraints.unify [(a, b)] Env.stateSubstInfo = .ok Sx
      ∧ Env3 = Env.updateSubst Sx := by
  obtain ⟨a', b', Sx, ha, hb, hu, hE⟩ :=
    CmdType.unifyTypes_inv Env Env3 (.forAll [] a) (.forAll [] b) h
  injection ha with _ ha2
  injection hb with _ hb2
  subst ha2
  subst hb2
  exact ⟨Sx, hu, hE⟩

/-- Under any substitution `S` absorbing the final one, an expression the checker elaborates, with
    `S` applied to its annotations, agrees with the substituted alias-free input scope, when the
    table's signatures are fixed for the input aliases. -/
private theorem inferType_annotAgree
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (cc : Cmd Expression)
    (e e' : Expression.Expr) (ety : LTy) (S : Subst)
    (hinf : CmdType.inferType C Env cc e = .ok (e', ety, Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (habs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    TypeSpec.ScopesAnnotAgree C (TContext.subst Env.context.dealias S).types
      (LExpr.applyTypeSubst e' S) := by
  obtain ⟨ea, hres, rfl, rfl⟩ := CmdType.inferType_inv C Env Env' cc e e' ety hinf
  exact resolveSource_annotAgree_dealias e ea C Env Env' hres he hf h_mono h_sigsFixed
    (TContext.FindEq.refl _) S habs

/-- The elaboration of a boolean expression the checker accepts has annotated type `bool` under
    any substitution, and the substituted resolved context is unchanged up to lookup. -/
private theorem boolCheck_sound_output
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (cc : Cmd Expression)
    (e e' : Expression.Expr) (ety : LTy) (S : Subst)
    (hinf : CmdType.inferType C Env cc e = .ok (e', ety, Env'))
    (hbool : CmdType.isBoolType ety = true)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context) (h_ne : Env.context.types ≠ []) :
    Lambda.LExpr.HasTypeA (T := CoreLParams) []
        (LExpr.applyTypeSubst e' S) (LMonoTy.tcons "bool" []) ∧
      TContext.FindEq (T := CoreLParams) (TContext.subst Env.context.dealias S)
        (TContext.subst Env'.context.dealias S) := by
  obtain ⟨ea, hres, rfl, rfl⟩ := CmdType.inferType_inv C Env Env' cc e e' ety hinf
  have hb : LExpr.toLMonoTy ea = LMonoTy.tcons "bool" [] :=
    CmdType.isBoolType_inv (LExpr.toLMonoTy ea) hbool
  have hEq2 : TContext.Equiv (T := CoreLParams) Env'.context Env.context :=
    SourceExpr.resolve_context_equiv_of_ne C Env Env' e ea hres h_ne
  have hHT : Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (LExpr.unresolved ea) (LMonoTy.tcons "bool" []) :=
    hb ▸ resolveSource_HasTypeA e ea C Env Env' hres he hf hr
  have h0 := hasTypeA_applyTypeSubst S hHT
  rw [show LMonoTy.subst S (LMonoTy.tcons "bool" []) = LMonoTy.tcons "bool" [] from
    LMonoTy.subst_bool S] at h0
  exact ⟨h0, TContext.FindEq.subst_subst S hEq2.symm.toFindEq.dealias⟩

/-- The conclusion of output soundness for one plain command `c'` checked from `Env` to `Env'`:
    under `S`, it is well typed from the substituted resolved scope to scopes agreeing by lookup
    with the substituted output scope, and the names it introduces are valid. -/
private abbrev CmdOutputSound (C : LContext CoreLParams) (Env Env' : TEnv Unit) (S : Subst)
    (c' : Cmd Expression) : Prop :=
  (∃ ts', CmdWellTyped C (TContext.subst Env.context.dealias S).types
      (Statement.Cmd.subst S c') ts' ∧
    ∀ x, ts'.find? x = (TContext.subst Env'.context.dealias S).types.find? x) ∧
  CmdNamesWF (· ∈ C.functions) (Statement.Cmd.subst S c')

/-- Output soundness of a plain initialization without a value under a substitution absorbing the
    checker's. -/
private theorem imperativeCmd_initNondet_output
    (C : LContext CoreLParams) (Env : TEnv Unit) (S : Subst)
    {x : CoreIdent} {xty ty1 ty2 : LTy} {md : MetaData Expression}
    {E1 E2 : TEnv Unit}
    (hlk' : Env.context.types.find? x = none)
    (hpre : CmdType.preprocess C Env xty = .ok (ty1, E1))
    (hpost : CmdType.postprocess C E1 ty1 = .ok (ty2, E2))
    (hfun : x.name ∉ C.functions)
    (h_aliasNames : ∀ al ∈ Env.context.aliases,
      C.knownTypes.containsName al.name = false)
    (hS : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S (CmdExt.cmd (.init x ty2 .nondet md))) = true) :
    CmdOutputSound C Env (CmdType.update E2 x ty2) S (.init x ty2 .nondet md) := by
  obtain ⟨mtyP, rfl, hE1, -⟩ := preprocess_inv C Env E1 xty ty1 hpre
  subst E1
  obtain ⟨rfl, hE2⟩ := CmdType.postprocess_inv C Env E2 mtyP ty2 hpost
  subst E2
  have hkn := knownInstance_of_stored_init C S x
    (LMonoTy.subst Env.stateSubstInfo.subst mtyP) .nondet md hS
  have hfix : Env.context.resolveTy (LMonoTy.subst Env.stateSubstInfo.subst mtyP)
      = LMonoTy.subst Env.stateSubstInfo.subst mtyP :=
    TContext.resolveTy_of_knownInstance (T := CoreLParams) h_aliasNames
      (knownInstance_of_subst _ S _ hkn)
  have hfe := update_subst_dealias_FindEq Env.context Env S x _ (TContext.FindEq.refl _) hlk'
    hfix
  refine ⟨⟨(TContext.subst Env.context.dealias S).types.insert x
      (.forAll [] (LMonoTy.subst S (LMonoTy.subst Env.stateSubstInfo.subst mtyP))), ?_, hfe.1⟩,
    hfun⟩
  show CmdWellTyped C (TContext.subst Env.context.dealias S).types
    (.init x (LTy.subst S (.forAll [] (LMonoTy.subst Env.stateSubstInfo.subst mtyP)))
      (Statement.substExprOrNondet S .nondet) md) _
  simp only [Statement.substExprOrNondet, Imperative.ExprOrNondet.map]
  refine CmdWellTyped.init_nondet _ x _
    (LMonoTy.subst S (LMonoTy.subst Env.stateSubstInfo.subst mtyP)) md _ ?_ rfl
    (LMonoTy.knownInstance_wellKinded _ C.knownTypes hkn) (HMaps.Equiv.refl _)
  rw [TContext.subst_dealias_find?, hlk', Option.map_none]

/-- Output soundness of a plain initialization with a value under a substitution absorbing the
    checker's. -/
private theorem imperativeCmd_initDet_output
    (C : LContext CoreLParams) (Env : TEnv Unit) (S : Subst)
    {x : CoreIdent} {xty ty1 ety ty3 : LTy} {expr e1 : Expression.Expr}
    {md : MetaData Expression} {E1 E2 E3 E4 : TEnv Unit}
    (hlk' : Env.context.types.find? x = none)
    (hpre : CmdType.preprocess C Env xty = .ok (ty1, E1))
    (hinf : CmdType.inferType C E1 (.init x xty (.det expr) md) expr = .ok (e1, ety, E2))
    (hunif : CmdType.unifyTypes E2 [(ty1, ety)] = .ok E3)
    (hpost : CmdType.postprocess C E3 ty1 = .ok (ty3, E4))
    (hfun : x.name ∉ C.functions)
    (he : LExpr.TEnvWF (T := CoreLParams) Env)
    (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context)
    (h_ne : Env.context.types ≠ [])
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases,
      C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (hS : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S (CmdExt.cmd (.init x ty3 (.det (CmdType.substExpr C E4 e1)) md)))
          = true)
    (habs : Subst.absorbs S (CmdType.update E4 x ty3).stateSubstInfo.subst) :
    CmdOutputSound C Env (CmdType.update E4 x ty3) S (.init x ty3 (.det (CmdType.substExpr C E4
        e1)) md) := by
  have hnotkey : x ∉ TContext.knownVars Env.context := by
    intro hmem
    have hmem' : x ∈ Env.context.types.keys := hmem
    obtain ⟨w, hw⟩ := HMaps.find?_of_mem_keys Env.context.types x hmem'
    rw [hlk'] at hw
    exact absurd hw (by simp)
  obtain ⟨mtyP, rfl, hE1, -⟩ := preprocess_inv C Env E1 xty ty1 hpre
  subst E1
  obtain ⟨ea, hres, rfl, rfl⟩ :=
    CmdType.inferType_inv C Env E2 (.init x xty (.det expr) md) expr e1 ety hinf
  obtain ⟨Sx, hu, rfl⟩ := unifyTypes_pair_inv E2 E3 mtyP (LExpr.toLMonoTy ea) hunif
  obtain ⟨rfl, hE4⟩ := CmdType.postprocess_inv C (E2.updateSubst Sx) E4 mtyP ty3 hpost
  subst E4
  have habsSx : Subst.absorbs S Sx.subst := habs
  have habsE3 :
      Subst.absorbs S (E2.updateSubst Sx).stateSubstInfo.subst := habs
  have hsub : LMonoTy.subst S
      (LMonoTy.subst (E2.updateSubst Sx).stateSubstInfo.subst mtyP)
      = LMonoTy.subst S mtyP :=
    LMonoTy.subst_absorbs S Sx.subst mtyP habsSx
  have hEq2 : TContext.Equiv (T := CoreLParams) E2.context Env.context :=
    SourceExpr.resolve_context_equiv_of_ne C Env E2 expr ea hres h_ne
  have hfresh2 : E2.context.types.find? x = none := by
    rw [hEq2.toFindEq.find? x, hlk']
  have hHT : Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (LExpr.unresolved ea) (LExpr.toLMonoTy ea) :=
    resolveSource_HasTypeA expr ea C Env E2 hres he hf hr
  have hunifS : LMonoTy.subst S mtyP = LMonoTy.subst S (LExpr.toLMonoTy ea) :=
    LMonoTy.subst_eq_of_absorbs S Sx.subst mtyP (LExpr.toLMonoTy ea) habsSx
      (Constraints.unify_sound _ _ _ hu (mtyP, LExpr.toLMonoTy ea)
        List.mem_cons_self)
  have hexpr : Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (LExpr.applyTypeSubst (LExpr.unresolved ea) S) (LMonoTy.subst S mtyP) := by
    rw [hunifS]
    exact hasTypeA_applyTypeSubst S hHT
  have hagree : TypeSpec.ScopesAnnotAgree C (TContext.subst Env.context.dealias S).types
      (LExpr.applyTypeSubst (LExpr.unresolved ea) S) :=
    resolveSource_annotAgree_dealias expr ea C Env E2 hres he hf h_mono h_sigsFixed
      (TContext.FindEq.refl _) S
      (Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ hu) habsSx)
  have hfvx : x ∉ HasFvars.getFvars (P := Expression)
      (LExpr.applyTypeSubst (LExpr.unresolved ea) S) := by
    show x ∉ LExpr.LExpr.getVars (LExpr.applyTypeSubst (LExpr.unresolved ea) S)
    rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType, Lambda.getVars_replaceUserProvidedType,
      Lambda.LExpr.Proofs.getVars_unresolved]
    intro hmem
    exact hnotkey (resolveSource_getVars_mem_knownVars expr ea C Env E2 hres x hmem)
  refine ⟨⟨(TContext.subst Env.context.dealias S).types.insert x
        (LTy.subst S (.forAll []
          (LMonoTy.subst (E2.updateSubst Sx).stateSubstInfo.subst mtyP))), ?_, ?_⟩,
    hfun⟩
  · show CmdWellTyped C (TContext.subst Env.context.dealias S).types
      (.init x (LTy.subst S (.forAll []
          (LMonoTy.subst (E2.updateSubst Sx).stateSubstInfo.subst mtyP)))
        (Statement.substExprOrNondet S
          (.det (CmdType.substExpr C (E2.updateSubst Sx)
            (LExpr.unresolved ea)))) md) _
    simp only [Statement.substExprOrNondet, Imperative.ExprOrNondet.map,
      CmdType.substExpr]
    rw [LExpr.applyTypeSubst_absorbs S (E2.updateSubst Sx).stateSubstInfo.subst habsE3,
      show LTy.subst S (.forAll [] (LMonoTy.subst (E2.updateSubst Sx).stateSubstInfo.subst mtyP))
        = .forAll [] (LMonoTy.subst S (LMonoTy.subst (E2.updateSubst Sx).stateSubstInfo.subst
          mtyP)) from rfl, hsub]
    have hB0 := binderAnnotsKnown_of_stored_cmd C S _ _ (List.mem_singleton.mpr rfl) hS
    have hB : BinderAnnotsKnown C
        (LExpr.applyTypeSubst (LExpr.unresolved ea) S) := by
      change BinderAnnotsKnown C (LExpr.applyTypeSubst
        (CmdType.substExpr C (E2.updateSubst Sx) (LExpr.unresolved ea)) S) at hB0
      simp only [CmdType.substExpr] at hB0
      rwa [LExpr.applyTypeSubst_absorbs S (E2.updateSubst Sx).stateSubstInfo.subst
        habsE3] at hB0
    have hknS : LMonoTy.knownInstance (LMonoTy.subst S mtyP) C.knownTypes = true := by
      rw [← hsub]
      exact knownInstance_of_stored_init C S x
        (LMonoTy.subst (E2.updateSubst Sx).stateSubstInfo.subst mtyP) _ md hS
    refine CmdWellTyped.init_det _ x (.forAll [] (LMonoTy.subst S mtyP))
      (LExpr.applyTypeSubst (LExpr.unresolved ea) S) (LMonoTy.subst S mtyP) md _ ?_ hfvx rfl
      (LMonoTy.knownInstance_wellKinded _ C.knownTypes hknS) ⟨hexpr, hB, hagree⟩
      (HMaps.Equiv.refl _)
    rw [TContext.subst_dealias_find?, hlk', Option.map_none]
  · have hkn2 := knownInstance_of_stored_init C S x
      (LMonoTy.subst (E2.updateSubst Sx).stateSubstInfo.subst mtyP) _ md hS
    exact (update_subst_dealias_FindEq Env.context E2 S x _ hEq2.toFindEq hfresh2
      (TContext.resolveTy_of_knownInstance (T := CoreLParams) h_aliasNames
        (knownInstance_of_subst _ S _ hkn2))).1

/-- Output soundness of a plain assignment of an unspecified value under a substitution absorbing
    the checker's. -/
private theorem imperativeCmd_setNondet_output
    (C : LContext CoreLParams) (Env : TEnv Unit) (S : Subst)
    {x : CoreIdent} {xty0 : LTy} {md : MetaData Expression}
    (hlk' : Env.context.types.find? x = some xty0) (hmono : xty0.isMonoType = true) :
    CmdOutputSound C Env Env S (.set x .nondet md) := by
  obtain ⟨a, rfl⟩ : ∃ a, xty0 = .forAll [] a := by
    cases xty0 with
    | forAll vars mty =>
      cases vars with
      | nil => exact ⟨mty, rfl⟩
      | cons v vars =>
        change LTy.isMonoType (.forAll (v :: vars) mty) = true at hmono
        simp [LTy.isMonoType, LTy.boundVars] at hmono
  refine ⟨⟨(TContext.subst Env.context.dealias S).types, ?_, fun _ => rfl⟩, trivial⟩
  show CmdWellTyped C (TContext.subst Env.context.dealias S).types
    (.set x (Statement.substExprOrNondet S .nondet) md) _
  simp only [Statement.substExprOrNondet, Imperative.ExprOrNondet.map]
  refine CmdWellTyped.set_nondet _ x (LMonoTy.subst S (Env.context.resolveTy a)) md _ ?_
    (HMaps.Equiv.refl _)
  rw [TContext.subst_dealias_find?, hlk', Option.map_some, TContext.resolveScheme_forAll]
  rfl

/-- Output soundness of a plain assignment of a value under a substitution absorbing the
    checker's. -/
private theorem imperativeCmd_setDet_output
    (C : LContext CoreLParams) (Env : TEnv Unit) (S : Subst)
    {x : CoreIdent} {xty0 ety : LTy} {expr e1 : Expression.Expr}
    {md : MetaData Expression} {E2 Env' : TEnv Unit}
    (hlk' : Env.context.types.find? x = some xty0)
    (hinf : CmdType.inferType C Env (.set x (.det expr) md) expr = .ok (e1, ety, E2))
    (hunif : CmdType.unifyTypes E2 [(Env.context.resolveScheme xty0, ety)] = .ok Env')
    (he : LExpr.TEnvWF (T := CoreLParams) Env)
    (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context)
    (h_ne : Env.context.types ≠ [])
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (hS : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S (CmdExt.cmd (.set x (.det e1) md))) = true)
    (habs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    CmdOutputSound C Env Env' S (.set x (.det e1) md) := by
  obtain ⟨ea, hres, rfl, rfl⟩ :=
    CmdType.inferType_inv C Env E2 (.set x (.det expr) md) expr e1 ety hinf
  obtain ⟨a, b, Sx, ha, hbb, hu, rfl⟩ :=
    CmdType.unifyTypes_inv E2 Env' (Env.context.resolveScheme xty0)
      (.forAll [] (LExpr.toLMonoTy ea)) hunif
  injection hbb with _ hbb2
  subst hbb2
  obtain ⟨a0, rfl, rfl⟩ := TContext.resolveScheme_eq_forAll_nil ha
  have habsSx : Subst.absorbs S Sx.subst := habs
  have hEq2 : TContext.Equiv (T := CoreLParams) E2.context Env.context :=
    SourceExpr.resolve_context_equiv_of_ne C Env E2 expr ea hres h_ne
  have hHT : Lambda.LExpr.HasTypeA (T := CoreLParams) []
      (LExpr.unresolved ea) (LExpr.toLMonoTy ea) :=
    resolveSource_HasTypeA expr ea C Env E2 hres he hf hr
  have hunifS : LMonoTy.subst S (Env.context.resolveTy a0)
      = LMonoTy.subst S (LExpr.toLMonoTy ea) :=
    LMonoTy.subst_eq_of_absorbs S Sx.subst _ (LExpr.toLMonoTy ea) habsSx
      (Constraints.unify_sound _ _ _ hu (_, LExpr.toLMonoTy ea) List.mem_cons_self)
  refine ⟨⟨(TContext.subst Env.context.dealias S).types, ?_, ?_⟩, trivial⟩
  · show CmdWellTyped C (TContext.subst Env.context.dealias S).types
      (.set x (Statement.substExprOrNondet S (.det (LExpr.unresolved ea))) md) _
    simp only [Statement.substExprOrNondet, Imperative.ExprOrNondet.map]
    refine CmdWellTyped.set_det _ x (LMonoTy.subst S (Env.context.resolveTy a0))
      (LExpr.applyTypeSubst (LExpr.unresolved ea) S) md _ ?_ ?_ (HMaps.Equiv.refl _)
    · rw [TContext.subst_dealias_find?, hlk', Option.map_some, TContext.resolveScheme_forAll]
      rfl
    · refine ⟨?_, binderAnnotsKnown_of_stored_cmd C S _ _
        (List.mem_singleton.mpr rfl) hS, ?_⟩
      · show Lambda.LExpr.HasTypeA (T := CoreLParams) []
          (LExpr.applyTypeSubst (LExpr.unresolved ea) S)
          (LMonoTy.subst S (Env.context.resolveTy a0))
        rw [hunifS]
        exact hasTypeA_applyTypeSubst S hHT
      · exact resolveSource_annotAgree_dealias expr ea C Env E2 hres he hf h_mono h_sigsFixed
          (TContext.FindEq.refl _) S
          (Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ hu) habsSx)
  · exact (TContext.FindEq.subst_subst S hEq2.symm.toFindEq.dealias).1

/-- Output soundness of one plain command under a substitution absorbing the checker's: the
    substituted command is well typed from the substituted resolved scope to scopes agreeing by
    lookup with the substituted output scope, and the names it introduces are valid. -/
private theorem imperativeCmd_sound_output_subst
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (cc c' : Cmd Expression) (S : Subst)
    (run : ImperativeCmdRun C Env cc c' Env')
    (hfun : ∀ x xty e md, cc = .init x xty e md → x.name ∉ C.functions)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context) (h_ne : Env.context.types ≠ [])
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (hS : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S (CmdExt.cmd c')) = true)
    (habs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    CmdOutputSound C Env Env' S c' := by
  cases run with
  | @initNondet x xty ty1 ty2 md E1 E2 hlk' hpre hpost =>
    exact imperativeCmd_initNondet_output C Env S hlk' hpre hpost (hfun x xty .nondet md rfl)
        h_aliasNames hS
  | @initDet x xty ty1 ety ty3 expr e1 md E1 E2 E3 E4 hlk' _ hpre hinf hunif hpost =>
    exact imperativeCmd_initDet_output C Env S hlk' hpre hinf hunif hpost (hfun x xty (.det expr)
        md rfl) he hf hr h_ne h_mono h_aliasNames h_sigsFixed hS habs
  | @setNondet x xty0 md hlk' hmono =>
    exact imperativeCmd_setNondet_output C Env S hlk' hmono
  | @setDet x xty0 ety expr e1 md E2 Env' hlk' hinf hunif =>
    exact imperativeCmd_setDet_output C Env S hlk' hinf hunif he hf hr h_ne h_mono h_sigsFixed hS
        habs
  | @assert l e e1 ety md _ hinf hbool | @assume l e e1 ety md _ hinf hbool
  | @cover l e e1 ety md _ hinf hbool =>
    obtain ⟨hty, hfind⟩ :=
      boolCheck_sound_output C Env Env' _ e e1 ety S hinf hbool he hf hr h_ne
    have hB := binderAnnotsKnown_of_stored_cmd C S _ e1 (List.mem_singleton.mpr rfl) hS
    have hagree := inferType_annotAgree C Env Env' _ e e1 ety S hinf he hf h_mono h_sigsFixed
      habs
    refine ⟨⟨(TContext.subst Env.context.dealias S).types, ?_, hfind.1⟩, trivial⟩
    constructor
    · exact ⟨hty, hB, hagree⟩
    · exact HMaps.Equiv.refl _

/-- Output soundness of plain-command checking under an absorbing substitution: the emitted
    command is well typed to scopes agreeing by lookup with the substituted output scope, and its
    names are valid. -/
private theorem typeCheckCmd_cmd_sound_output_subst
    (P : Program) (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (cc : Cmd Expression) (c' : Command) (S : Subst)
    (h : Statement.typeCheckCmd C Env P (.cmd cc) = .ok (c', Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context) (h_ne : Env.context.types ≠ [])
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (hS : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S c') = true)
    (habs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    (∃ ts', CmdExtWellTyped C (P.resolveSigs Env.context.aliases)
        (TContext.subst Env.context.dealias S).types (Statement.Command.subst S c') ts' ∧
      ∀ x, ts'.find? x = (TContext.subst Env'.context.dealias S).types.find? x) ∧
    StatementNamesWF (P.resolveSigs Env.context.aliases) (· ∈ C.functions)
      (.cmd (Statement.Command.subst S c')) := by
  cases Statement.typeCheckCmd_ok_inv h with
  | cmd run hfun =>
    obtain ⟨⟨ts', hcmd, hfe⟩, hnames⟩ :=
      imperativeCmd_sound_output_subst C Env Env' cc _ S run hfun he hf hr h_ne h_mono
        h_aliasNames h_sigsFixed hS habs
    exact ⟨⟨ts', CmdExtWellTyped.cmd _ _ _ hcmd, hfe⟩, hnames⟩

section CallOutput

attribute [local simp] CallArg.getInputExprs_cons_inArg CallArg.getInputExprs_cons_inoutArg
  CallArg.getInputExprs_cons_outArg CallArg.getLhs_cons_inArg CallArg.getLhs_cons_inoutArg
  CallArg.getLhs_cons_outArg

/-- An annotated typing of the resolver's output with its annotations erased, at the inferred
    monotype, satisfies the `call` rule's input premise. -/
private theorem inputMatch_of_unresolved (Γ : TContext Unit)
    (et : LExprT CoreLParams.mono)
    (h : Lambda.LExpr.HasTypeA (T := CoreLParams) [] (LExpr.unresolved et) et.toLMonoTy) :
    match (LExpr.unresolved et : Expression.Expr) with
    | .fvar _ x none => Γ.types.find? x = some (.forAll [] et.toLMonoTy)
    | e => Lambda.LExpr.HasTypeA (T := CoreLParams) [] e et.toLMonoTy := by
  cases et
  case abs mm n ty b =>
    cases hty : mm.type.isArrow with
    | none => simp only [LExpr.unresolved, hty] at h ⊢; exact h
    | some pr => simp only [LExpr.unresolved, hty] at h ⊢; exact h
  all_goals exact h

/-! ### The checker's argument rewrite and variable resolution -/

/-- `replaceInArgs` keeps the number of input positions. -/
private theorem getInputExprs_replaceInArgs_length (args : List (CallArg Expression))
    (newExprs : List Expression.Expr) :
    (CallArg.getInputExprs (CallArg.replaceInArgs args newExprs)).length
      = (CallArg.getInputExprs args).length := by
  simp only [CallArg.replaceInArgs]
  induction args generalizing newExprs with
  | nil => rfl
  | cons a rest ih =>
    match a, newExprs with
    | .inArg _, e :: rest2 => simp [CallArg.replaceInArgs.go, ih]
    | .inArg _, [] => simp [CallArg.replaceInArgs.go, ih]
    | .inoutArg _, e :: rest2 => simp [CallArg.replaceInArgs.go, ih]
    | .inoutArg _, [] => simp [CallArg.replaceInArgs.go, ih]
    | .outArg _, rest2 => simp [CallArg.replaceInArgs.go, ih]

/-! ### Output soundness of the `call` branch -/

/-- Output soundness for a checked procedure call under any substitution absorbing the checker's
    solution, when the substituted argument annotations are registered types: the call is well
    typed in the substituted resolved scope against the program with resolved signatures. -/
private theorem typeCheckCmd_call_sound_output_subst
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (nm : String) (tyArgs : Option (List Expression.Ty))
    (callArgs : List (CallArg Expression)) (md : MetaData Expression)
    (c' : Command) (S : Subst)
    (h : Statement.typeCheckCmd C Env P (.call nm tyArgs callArgs md) = .ok (c', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_types_ne : Env.context.types ≠ [])
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (hS : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S c') = true) :
    ∃ ts', CmdExtWellTyped C (P.resolveSigs Env.context.aliases)
        (TContext.subst Env.context.dealias S).types (Statement.Command.subst S c') ts' ∧
      ∀ x, ts'.find? x = (TContext.subst Env'.context.dealias S).types.find? x := by
  cases Statement.typeCheckCmd_ok_inv h with
  | @call _ _ _ _ proc lhs_tys io_sig argsa EnvLhs Env_sig Env_res Suni
      instTys EnvA hpf hlhsSome hwf hlhs hsig hres huni hargs =>
    have hargsLen := (hwf.argsMatch hpf).inputCount
    obtain ⟨hEnvLhs, hlhsTysLen, hlhsStep⟩ :=
      Identifier.instantiateAndSubsts_inv C _ Env EnvLhs lhs_tys hlhs h_mono
    subst EnvLhs
    obtain ⟨hsigCtx, hsigSub, hsigGen, Sren, hsigAE, hren, hsigEq, EnvJ, hself⟩ :=
      LMonoTySignature.instantiate_inv C Env Env_sig proc.header.typeArgs
        (proc.header.inputs ++ proc.header.outputs) io_sig hsig
    have hsigWF : LExpr.TEnvWF (T := CoreLParams) Env_sig :=
      TEnvWF.of_sig_step Env Env_sig hsigCtx hsigSub hsigGen h_env
    have hsigNe : Env_sig.context.types ≠ [] := by rw [hsigCtx]; exact h_types_ne
    obtain ⟨-, -, hresEqNe, hresAbs, hresLen, hresStep⟩ :=
      SourceExpr.resolves_step C Env_sig Env_res (CallArg.getInputExprs callArgs) argsa hres
        hsigWF h_fac
    have hresEq := hresEqNe hsigNe
    have habsRes : Subst.absorbs S Env_res.stateSubstInfo.subst :=
      Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ huni) h_absorbs
    have hargsaLen : argsa.length = proc.header.inputs.length := by rw [hresLen, hargsLen]
    obtain ⟨hkill, hiolen, hinpEq, hretEq⟩ :=
      call_sig_unify_facts Env Env_sig Env_res Suni S Sren proc io_sig argsa lhs_tys hsigSub
        hsigAE hresAbs huni h_absorbs
    have hinLen : proc.header.inputs.values.length = proc.header.inputs.length :=
      ListMap.values_length _
    have houtLen : proc.header.outputs.values.length = proc.header.outputs.length :=
      ListMap.values_length _
    have hkey := LMonoTy.subst_ofScopes_rename_eq S Sren
    have hnewLen : (argsa.map LExpr.unresolved).length
        = (CallArg.getInputExprs callArgs).length := by rw [List.length_map, hresLen]
    have hrepLen : (CallArg.getInputExprs
        (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved))).length
        = (CallArg.getInputExprs callArgs).length :=
      getInputExprs_replaceInArgs_length _ _
    have hgetIn : CallArg.getInputExprs
        ((CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)).map
          (Statement.CallArg.subst S))
        = (CallArg.getInputExprs
            (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved))).map
          (fun e => LExpr.applyTypeSubst e S) := getInputExprs_map_subst S _
    have hgetLhs : CallArg.getLhs
        ((CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)).map
          (Statement.CallArg.subst S))
        = CallArg.getLhs callArgs := by
      rw [getLhs_map_subst, CallArg.getLhs_replaceInArgs]
    -- The callee with its parameter types resolved, as the resolved program stores it.
    let ΓA : TContext Unit := { aliases := Env.context.aliases }
    let procR := proc.resolveSig ΓA
    have hpfR : Program.Procedure.find? (P.resolveSigs Env.context.aliases) nm = some procR := by
      rw [Program.resolveSigs_find?, hpf]
      rfl
    have hΓA : ΓA.resolveTy = Env.context.resolveTy :=
      TContext.resolveTy_congr (T := CoreLParams) rfl
    have hinValsR : procR.header.inputs.values
        = proc.header.inputs.values.map Env.context.resolveTy := by
      rw [Procedure.resolveSig_inputs, TContext.resolveSig_values, hΓA]
    have houtValsR : procR.header.outputs.values
        = proc.header.outputs.values.map Env.context.resolveTy := by
      rw [Procedure.resolveSig_outputs, TContext.resolveSig_values, hΓA]
    -- The checker's instantiated signature is the renamed resolved signature.
    have hvals : (proc.header.inputs ++ proc.header.outputs).values
        = proc.header.inputs.values ++ proc.header.outputs.values :=
      ListMap.values_append _ _
    have hioR : ∀ k (hk : k < (proc.header.inputs.values ++ proc.header.outputs.values).length)
        (hk2 : k < io_sig.values.length),
        io_sig.values[k] = LMonoTy.subst Sren
          (Env.context.resolveTy (proc.header.inputs.values ++ proc.header.outputs.values)[k]) := by
      intro k hk hk2
      have hk3 : k < ((proc.header.inputs ++ proc.header.outputs).values.map
          (fun t => Env.context.resolveTy (LMonoTy.subst Sren t))).length := by
        rw [List.length_map, hvals]; exact hk
      rw [getElem_congr_coll hsigEq, List.getElem_map, getElem_congr_coll hvals]
      exact TContext.resolveTy_subst_renaming (T := CoreLParams) h_env.aliasesWF Sren hren _
    -- The call's instantiation sends a resolved parameter type to its renamed solved image.
    have hkeyR : ∀ ty ∈ proc.header.inputs.values ++ proc.header.outputs.values,
        LMonoTy.subst (HMaps.ofScopes
            [(proc.header.typeArgs ++
              LMonoTys.freeVars (proc.header.inputs.values ++ proc.header.outputs.values)).map
              (fun v => (v, LMonoTy.subst S (LMonoTy.subst Sren (LMonoTy.ftvar v))))])
            (Env.context.resolveTy ty)
          = LMonoTy.subst S (LMonoTy.subst Sren (Env.context.resolveTy ty)) :=
      fun ty hty => hkey _ _ (fun _ hv => List.mem_append_right _
        (LMonoTys.freeVars_mem_subset hty
          (TContext.resolveTy_freeVars_subset (T := CoreLParams) h_env.aliasesWF ty _ hv)))
    refine ⟨(TContext.subst Env.context.dealias S).types, ?_, ?_⟩
    · refine CmdExtWellTyped.call (TContext.subst Env.context.dealias S).types nm _
        ((CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)).map
          (Statement.CallArg.subst S))
        procR md
        ((proc.header.typeArgs ++
          LMonoTys.freeVars (proc.header.inputs.values ++ proc.header.outputs.values)).map
          (fun v => (v, LMonoTy.subst S (LMonoTy.subst Sren (LMonoTy.ftvar v)))))
        _ hpfR ?_ ?_ ?_ ?_ ?_ ?_ (HMaps.Equiv.refl _)
      · have hshape :
            ((CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)).map
              (Statement.CallArg.subst S)).map
                (CallArg.mapInput (P := Expression) fun _ => .boolConst Core.valueLoc true)
            = callArgs.map (CallArg.mapInput (P := Expression) fun _ => .boolConst Core.valueLoc
                            true) := by
          rw [show Statement.CallArg.subst S =
              CallArg.mapInput (P := Expression) (·.applyTypeSubst S) from rfl,
            CallArg.map_mapInput_const, CallArg.replaceInArgs_map_mapInput_const]
        refine hwf.transfer (.boolConst Core.valueLoc true) hpf hpfR ?_ ?_ hshape
        · rw [Procedure.resolveSig_inputs, TContext.resolveSig_keys]
        · rw [Procedure.resolveSig_outputs, TContext.resolveSig_keys]
      · intro v hv
        rw [hgetLhs] at hv
        rw [TContext.subst_dealias_find?, Option.isSome_map]
        exact hlhsSome v hv
      · intro i hi hjR
        have hj : i < proc.header.inputs.values.length := by
          rw [hinValsR, List.length_map] at hjR; exact hjR
        have hRi : procR.header.inputs.values[i]
            = Env.context.resolveTy proc.header.inputs.values[i] := by
          rw [getElem_congr_coll hinValsR, List.getElem_map]
        have hic : i < (CallArg.getInputExprs callArgs).length := by
          have h2 := hi
          rw [hgetIn, List.length_map, hrepLen] at h2
          exact h2
        have hjIn : i < proc.header.inputs.length := by rw [← hinLen]; exact hj
        have hav : i < argsa.length := by omega
        have hiv : i < io_sig.values.length := by omega
        have hrv : i < (CallArg.getInputExprs
            (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved))).length := by omega
        have happ : i < (proc.header.inputs.values ++ proc.header.outputs.values).length := by
          rw [List.length_append]; omega
        have hgetL : (proc.header.inputs.values ++ proc.header.outputs.values)[i]?
            = some proc.header.inputs.values[i] := by
          rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
        have happL : (proc.header.inputs.values ++ proc.header.outputs.values)[i]
            = proc.header.inputs.values[i] :=
          (List.getElem_eq_iff happ).mpr hgetL
        have hinGet : (CallArg.getInputExprs
            ((CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)).map
              (Statement.CallArg.subst S)))[i]
            = LExpr.applyTypeSubst ((CallArg.getInputExprs
                (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)))[i]) S := by
          refine (List.getElem_eq_iff hi).mpr ?_
          rw [hgetIn, List.getElem?_map, List.getElem?_eq_getElem hrv, Option.map_some]
        have hkeyIn : LMonoTy.subst (HMaps.ofScopes
            [(proc.header.typeArgs ++
              LMonoTys.freeVars (proc.header.inputs.values ++ proc.header.outputs.values)).map
              (fun v => (v, LMonoTy.subst S (LMonoTy.subst Sren (LMonoTy.ftvar v))))])
              procR.header.inputs.values[i]
            = LMonoTy.subst S io_sig.values[i] := by
          rw [hRi, hkeyR _ (List.mem_append_left _ (List.getElem_mem hj)), hioR i happ hiv,
            happL]
        have hgetA : (argsa.map LExpr.toLMonoTy)[i]? = some argsa[i].toLMonoTy := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hav, Option.map_some]
        have hsame : LMonoTy.subst S argsa[i].toLMonoTy = LMonoTy.subst S io_sig.values[i] :=
          hinpEq i _ _ hjIn hgetA (List.getElem?_eq_getElem hiv)
        obtain ⟨Ei, Ei', hri, hwfi, -, heqNe, habsi⟩ := hresStep i hic hav
        obtain ⟨heqi, hnei⟩ := heqNe hsigNe
        have heqiE : TContext.Equiv (T := CoreLParams) Ei.context Env.context := by
          rw [← hsigCtx]; exact heqi
        have hresolvedEi : TContext.AliasesResolved Ei.context := by
          intro a ha
          rw [heqiE.2] at ha ⊢
          exact h_resolved a ha
        rw [hinGet]
        rcases CallArg.getInputExprs_replaceInArgs_getElem? callArgs
            (argsa.map LExpr.unresolved) hnewLen i with hA | ⟨idb, hB1, hB2⟩
        · have hgi : (CallArg.getInputExprs
              (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)))[i]
              = LExpr.unresolved argsa[i] := by
            refine (List.getElem_eq_iff hrv).mpr ?_
            rw [hA, List.getElem?_map, List.getElem?_eq_getElem hav, Option.map_some]
          rw [hkeyIn, ← hsame]
          have hBi :
              BinderAnnotsKnown C (LExpr.applyTypeSubst (LExpr.unresolved argsa[i]) S) := by
            have hmem : (CallArg.getInputExprs
                (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)))[i] ∈
                CallArg.getInputExprs
                  (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)) :=
              List.getElem_mem _
            have hk := binderAnnotsKnown_of_call_inputs C S nm _ _ md hS _ hmem
            rwa [hgi] at hk
          rw [hgi]
          have hag : TypeSpec.ScopesAnnotAgree C (TContext.subst Env.context.dealias S).types
              (LExpr.applyTypeSubst (LExpr.unresolved argsa[i]) S) := by
            refine resolveSource_annotAgree_dealias _ _ C Ei Ei' hri hwfi h_fac
              (MonoScope_of_findEq heqiE.toFindEq h_mono) ?_
              heqiE.symm.toFindEq S (Subst.absorbs_trans _ _ _ habsi habsRes)
            rw [heqiE.2]
            exact h_sigsFixed
          exact inputMatch_subst C Env.context.dealias S _ _
            (inputMatch_of_unresolved Env.context.dealias argsa[i]
              (resolveSource_HasTypeA _ _ C Ei Ei' hri hwfi h_fac hresolvedEi)) hBi hag
        · have hgiOrig : (CallArg.getInputExprs callArgs)[i] = LExpr.fvar Core.coreLoc idb none :=
            (List.getElem_eq_iff hic).mpr hB1
          have hgi : (CallArg.getInputExprs
              (CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)))[i]
              = LExpr.fvar Core.coreLoc idb none := (List.getElem_eq_iff hrv).mpr hB2
          have hidMem : idb ∈ CallArg.getLhs callArgs := by
            have hmemAny := CallArg.mem_getInputExprs_replaceInArgs callArgs
              (argsa.map LExpr.unresolved) (Nat.le_of_eq hnewLen.symm) _
              (hgi ▸ List.getElem_mem hrv)
            rcases hmemAny with hmem | ⟨idc, hidc, heqc⟩
            · obtain ⟨et, -, het⟩ := List.mem_map.mp hmem
              exact absurd het (LExpr.Proofs.unresolved_ne_fvar_none et Core.coreLoc idb)
            · rw [LExpr.fvar.injEq] at heqc
              obtain ⟨-, rfl, -⟩ := heqc
              exact hidc
          obtain ⟨tyb, hfindb⟩ := Option.isSome_iff_exists.mp (hlhsSome idb hidMem)
          obtain ⟨m0, rfl⟩ := MonoScope.find?_forAll h_mono hfindb
          rw [hgiOrig] at hri
          have hfindEi : Ei.context.types.find? idb = some (LTy.forAll [] m0) := by
            rw [heqiE.find? idb]; exact hfindb
          obtain ⟨hEiEq, r, -, hrres, htyr⟩ :=
            SourceExpr.resolve_fvar_none_inv C Ei Ei' Core.coreLoc idb argsa[i] m0 hri hfindEi hnei
          rw [hEiEq] at habsi
          have habsEi : Subst.absorbs S Ei.stateSubstInfo.subst :=
            Subst.absorbs_trans _ _ _ habsi habsRes
          have hrEnv : r = Env.context.resolveTy m0 := by
            rw [hrres, TContext.resolveTy_congr (T := CoreLParams) heqiE.2]
          rw [hkeyIn, ← hsame, htyr, LMonoTy.subst_absorbs S _ r habsEi, hrEnv, hgi,
            LExpr.applyTypeSubst_fvar_none]
          show (TContext.subst Env.context.dealias S).types.find? idb
            = some (LTy.forAll [] (LMonoTy.subst S (Env.context.resolveTy m0)))
          rw [TContext.subst_dealias_find?, hfindb, Option.map_some,
            TContext.resolveScheme_forAll]
          rfl
      · intro j hj hj2R
        have hj2 : j < proc.header.outputs.values.length := by
          rw [houtValsR, List.length_map] at hj2R; exact hj2R
        have hRj : procR.header.outputs.values[j]
            = Env.context.resolveTy proc.header.outputs.values[j] := by
          rw [getElem_congr_coll houtValsR, List.getElem_map]
        have hjc : j < (CallArg.getLhs callArgs).length := by
          have h2 := hj
          rw [hgetLhs] at h2
          exact h2
        have hjOut : j < proc.header.outputs.length := by rw [← houtLen]; exact hj2
        have hlv : j < lhs_tys.length := by rw [hlhsTysLen]; exact hjc
        have hiv : proc.header.inputs.length + j < io_sig.values.length := by omega
        have happ : proc.header.inputs.length + j
            < (proc.header.inputs.values ++ proc.header.outputs.values).length := by
          rw [List.length_append]; omega
        have happR : (proc.header.inputs.values ++ proc.header.outputs.values)[
            proc.header.inputs.length + j] = proc.header.outputs.values[j] := by
          refine (List.getElem_eq_iff happ).mpr ?_
          rw [List.getElem?_append_right (by omega),
            show proc.header.inputs.length + j - proc.header.inputs.values.length = j from
              by omega,
            List.getElem?_eq_getElem hj2]
        have hlhsGet : (CallArg.getLhs
            ((CallArg.replaceInArgs callArgs (argsa.map LExpr.unresolved)).map
              (Statement.CallArg.subst S)))[j]
            = (CallArg.getLhs callArgs)[j] := by
          refine (List.getElem_eq_iff hj).mpr ?_
          rw [hgetLhs, List.getElem?_eq_getElem hjc]
        obtain ⟨m0, r, hfind0, -, hres0, hval0⟩ := hlhsStep j hjc hlv
        have hkeyOut : LMonoTy.subst (HMaps.ofScopes
            [(proc.header.typeArgs ++
              LMonoTys.freeVars (proc.header.inputs.values ++ proc.header.outputs.values)).map
              (fun v => (v, LMonoTy.subst S (LMonoTy.subst Sren (LMonoTy.ftvar v))))])
              procR.header.outputs.values[j]
            = LMonoTy.subst S io_sig.values[proc.header.inputs.length + j] := by
          rw [hRj, hkeyR _ (List.mem_append_right _ (List.getElem_mem hj2)),
            hioR _ happ hiv, happR]
        have hsame : LMonoTy.subst S lhs_tys[j]
            = LMonoTy.subst S io_sig.values[proc.header.inputs.length + j] :=
          hretEq j _ _ hjOut (List.getElem?_eq_getElem hlv) (List.getElem?_eq_getElem hiv)
        rw [hlhsGet, hkeyOut, ← hsame, hval0, hkill, hres0, TContext.subst_dealias_find?, hfind0,
          Option.map_some, TContext.resolveScheme_forAll]
        rfl
      · have hinstArgs : instTys
            = proc.header.typeArgs.map (fun a => LMonoTy.subst Sren (.ftvar a)) := by
          simp only [hself, Except.ok.injEq, Prod.mk.injEq] at hargs
          exact hargs.1.symm
        rw [hinstArgs, Option.map_some, List.map_map, List.map_map]
        refine congrArg some (List.map_congr_left fun a ha => ?_)
        have hmemA : ∀ v, v ∈ LMonoTy.freeVars (.ftvar a) →
            v ∈ proc.header.typeArgs ++
              LMonoTys.freeVars (proc.header.inputs.values ++ proc.header.outputs.values) := by
          intro v hv
          simp only [LMonoTy.freeVars, List.mem_singleton] at hv
          subst hv
          exact List.mem_append_left _ ha
        have hkeyA : LMonoTy.subst (HMaps.ofScopes
            [(proc.header.typeArgs ++
              LMonoTys.freeVars (proc.header.inputs.values ++ proc.header.outputs.values)).map
              (fun v => (v, LMonoTy.subst S (LMonoTy.subst Sren (LMonoTy.ftvar v))))])
              (.ftvar a) = LMonoTy.subst S (LMonoTy.subst Sren (.ftvar a)) :=
          hkey _ _ hmemA
        simp only [Function.comp_apply]
        rw [hkeyA]
        rfl
      · intro tys htys ty hty
        exact LMonoTy.knownInstance_wellKinded _ C.knownTypes
          (Statement.allCmdTys_call_tyArgs hS tys htys ty hty)
    · have hresCtx : TContext.Equiv (T := CoreLParams) Env_res.context Env.context := by
        rw [← hsigCtx]; exact hresEq
      exact (TContext.FindEq.symm (hresCtx.dealias.subst S).toFindEq).1

end CallOutput

/-! ### Output soundness of every command -/

/-- Output soundness of command checking: under any substitution `S` absorbing the checker's, the
    emitted command is well typed against the alias-resolved factory table and procedure
    signatures, in the `S`-applied, alias-resolved input scope, and its names are valid. The
    hypotheses mean: the input environment and function table are well formed; the aliases are
    fully resolved (`h_resolved`); the scope is a nonempty stack of monotypes (`h_types_ne`,
    `h_mono`); no alias is named after a registered type (`h_aliasNames`); the factory
    signatures are unchanged by alias resolution (`h_sigsFixed`); and the emitted command, after
    applying `S`, uses only registered types (`hS`). -/
theorem Statement.typeCheckCmd_sound_output
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command) (S : Subst)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_types_ne : Env.context.types ≠ [])
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (hS : allCmdTys (fun mty => LMonoTy.knownInstance mty C.knownTypes)
      (Statement.Command.subst S c') = true)
    (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    (∃ ts', CmdExtWellTyped (C.resolveTable Env.context.aliases)
        (P.resolveSigs Env.context.aliases)
        (TContext.subst Env.context.dealias S).types
        (Statement.Command.subst S c') ts' ∧
      ∀ x, Strata.Util.HMaps.find? ts' x =
        (TContext.subst Env'.context.dealias S).types.find? x) ∧
    StatementNamesWF (P.resolveSigs Env.context.aliases) (· ∈ C.functions)
      (.cmd (Statement.Command.subst S c')) := by
  rw [LContext.resolveTable_eq_self h_sigsFixed]
  cases c with
  | cmd cc =>
    exact typeCheckCmd_cmd_sound_output_subst P C Env Env' cc c' S h h_env h_fac
      h_resolved h_types_ne h_mono h_aliasNames h_sigsFixed hS h_absorbs
  | call nm tyArgs callArgs md =>
    obtain ⟨tys', args', hc'⟩ : ∃ tys' args', c' = CmdExt.call nm tys' args' md := by
      cases Statement.typeCheckCmd_ok_inv h; exact ⟨_, _, rfl⟩
    subst c'
    exact ⟨typeCheckCmd_call_sound_output_subst C Env Env' P nm tyArgs callArgs md
      (.call nm tys' args' md) S h h_env h_fac h_resolved h_types_ne h_mono h_sigsFixed
      h_absorbs hS,
      trivial⟩

end CommandOutput

/-! ## Output soundness of the statement walk -/

section DirectSoundness

/-- A block's walk produces a substitution absorbing the one it was given. -/
private theorem goBlock_absorbs
    (P : Program) (op : Option Procedure)
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit)
    (bss acc bss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.goBlock P op C Env bss acc labels m st
      = .ok (bss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  rcases goBlock_ok_inv h with ⟨-, Ego, Cgo, hg, rfl, -⟩ | ⟨-, -, -, Cgo, hg, -⟩
  · exact go_absorbs P op C (Env.pushEmptyContext) bss acc labels bss' Ego Cgo hg
      (Lambda.pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he) hf
  · exact go_absorbs P op C Env bss acc labels bss' Env' Cgo hg he hf

/-- `Γ` has the aliases `A`, no name of them is a registered type of `C`, and the signatures of
    `C` are fixed for `A`. -/
private def AliasesAt (A : List TypeAlias) (C : LContext CoreLParams) (Γ : TContext Unit) :
    Prop :=
  Γ.aliases = A ∧ (∀ al ∈ A, C.knownTypes.containsName al.name = false) ∧
    FactorySigsFixed A C.functions

/-- Applying `S` to a `block` statement applies it to the body. -/
private theorem Statement_subst_block (S : Subst) (label : String) (bss : List Statement)
    (md : MetaData Expression) :
    Statement.Statement.subst S (Stmt.block label bss md)
      = Stmt.block label (bss.map (Statement.Statement.subst S)) md := by
  simp only [Statement.Statement.subst, Statement_subst_go_eq, List.reverse_nil, List.nil_append]

/-- Applying `S` to an `ite` statement applies it to the condition and both branches. -/
private theorem Statement_subst_ite (S : Subst) (cond : ExprOrNondet Expression)
    (tss ess : List Statement) (md : MetaData Expression) :
    Statement.Statement.subst S (Stmt.ite cond tss ess md)
      = Stmt.ite (cond.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
          (tss.map (Statement.Statement.subst S)) (ess.map (Statement.Statement.subst S)) md := by
  simp only [Statement.Statement.subst, Statement_subst_go_eq, List.reverse_nil, List.nil_append]

/-- Applying `S` to a `loop` statement applies it to the guard, measure, invariants and body. -/
private theorem Statement_subst_loop (S : Subst) (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr) (invariant : List (String × Expression.Expr))
    (bss : List Statement) (md : MetaData Expression) :
    Statement.Statement.subst S (Stmt.loop guard measure invariant bss md)
      = Stmt.loop (guard.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
          (measure.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
          (invariant.map (fun p => (p.1, LExpr.applyTypeSubst p.2 S)))
          (bss.map (Statement.Statement.subst S)) md := by
  simp only [Statement.Statement.subst, Statement_subst_go_eq, List.reverse_nil, List.nil_append]

/-- `R` under the premises of the output-soundness induction at one walk position: well-formedness,
    scope and alias facts about the start state, and the annotation sweep under `S`. -/
private abbrev GoOutputPre (S : Subst) (A : List TypeAlias)
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (acc ss' : List Statement)
    (R : Prop) : Prop :=
  Subst.absorbs S Env'.stateSubstInfo.subst →
    LExpr.TEnvWF (T := CoreLParams) Env → FactorySigWF C.functions →
    TContext.AliasesResolved Env.context →
    Env.context.types ≠ [] →
    MonoScope (IDMeta := Unit) Env.context →
    AliasesAt A C Env.context →
    (∀ ss_proc, ss' = acc.reverse ++ ss_proc → SweepAt C S ss_proc) →
    R

/-- The conclusion of output soundness at one walk position: the emitted statements, after
    applying `S`, are well typed from the substituted resolved input scope and their names are
    valid. -/
private abbrev GoOutputMotive (P : Program) (A : List TypeAlias) (S : Subst)
    (C : LContext CoreLParams) (Env : TEnv Unit) (_ : List Statement) (acc : List Statement)
    (labels : List String) (_ : ScopeMap) (_ : ScopeState) (ss' : List Statement)
    (Env' : TEnv Unit) (C' : LContext CoreLParams) (_ : ScopeState) : Prop :=
  GoOutputPre S A C Env Env' acc ss'
    (∃ ss_proc tsOut, ss' = acc.reverse ++ ss_proc ∧
      StatementsWellTyped (P.resolveSigs A) C (TContext.subst Env.context.dealias S).types
        labels (ss_proc.map (Statement.Statement.subst S)) C' tsOut ∧
      (∀ x, tsOut.find? x = (TContext.subst Env'.context.dealias S).types.find? x) ∧
      StatementsNamesWF (P.resolveSigs A) (· ∈ C.functions)
        (ss_proc.map (Statement.Statement.subst S)))

/-- The conclusion of output soundness for a block check: the emitted statements, after applying
    `S`, are well typed and their names are valid. -/
private abbrev GoOutputMotiveB (P : Program) (A : List TypeAlias) (S : Subst)
    (C : LContext CoreLParams) (Env : TEnv Unit) (_ : List Statement) (acc : List Statement)
    (labels : List String) (_ : ScopeMap) (_ : ScopeState) (bss' : List Statement)
    (Env' : TEnv Unit) (_ : LContext CoreLParams) (_ : ScopeState) : Prop :=
  GoOutputPre S A C Env Env' acc bss'
    (∃ ss_proc C_body ts_body, bss' = acc.reverse ++ ss_proc ∧
      StatementsWellTyped (P.resolveSigs A) C (TContext.subst Env.context.dealias S).types
        labels (ss_proc.map (Statement.Statement.subst S)) C_body ts_body ∧
      StatementsNamesWF (P.resolveSigs A) (· ∈ C.functions)
        (ss_proc.map (Statement.Statement.subst S)))

/-- A scope with the same lookups as one with resolved aliases, a nonempty stack of monotypes and
    the aliases `A` again has all of these properties. -/
private theorem goOutputScope_of_equiv {A : List TypeAlias} {C : LContext CoreLParams}
    {Env E : TEnv Unit} :
    TContext.Equiv (T := CoreLParams) E.context Env.context →
    TContext.AliasesResolved Env.context →
    Env.context.types ≠ [] → MonoScope (IDMeta := Unit) Env.context →
    AliasesAt A C Env.context →
    TContext.AliasesResolved E.context ∧
      E.context.types ≠ [] ∧ MonoScope (IDMeta := Unit) E.context ∧
      AliasesAt A C E.context :=
  fun heq hr hne hmono hAN =>
    ⟨heq.symm.aliasesResolved hr, heq.symm.types_ne_nil hne,
      MonoScope_of_findEq heq.toFindEq hmono, ⟨heq.2.trans hAN.1, hAN.2⟩⟩

/-- Moving a statement from the reversed accumulator onto the front of the remaining list leaves
    the concatenation unchanged. -/
private theorem reverse_cons_append_eq (s : Statement) (acc tp : List Statement) :
    (s :: acc).reverse ++ tp = acc.reverse ++ (s :: tp) := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Output soundness of the walk at a statement `cmd`, given the induction hypotheses for its
    sub-runs. -/
private theorem go_output_cmd {P : Program} {op : Option Procedure} {S : Subst}
    {A : List TypeAlias} :
    ∀ C Env acc labels m st srest cmd c' Env1 ss' Env' C' st',
      Statement.typeCheckCmd C Env P (renameCmd C.rigidTypeVars m st cmd).1 = .ok (c', Env1) →
      (∀ e ∈ Statement.cmdExprs cmd,
        unboundAnnotVar? false C.rigidTypeVars (renameCmd C.rigidTypeVars m st cmd).2.1 e
          = none) →
      @Core.Statement.typeCheckAux.go P op C Env1 srest (Stmt.cmd c' :: acc) labels
        (renameCmd C.rigidTypeVars m st cmd).2.1 (renameCmd C.rigidTypeVars m st cmd).2.2
        = .ok (ss', Env', C', st') →
      GoOutputMotive P A S C Env1 srest (Stmt.cmd c' :: acc) labels (renameCmd C.rigidTypeVars m
          st cmd).2.1
        (renameCmd C.rigidTypeVars m st cmd).2.2 ss' Env' C' st' →
      GoOutputMotive P A S C Env (Stmt.cmd cmd :: srest) acc labels m st ss' Env' C' st' := by
  intro Cx Env acc labels m st srest cmd c' Envm ss' Env' C' _ htc _ hgo2 ih1 habs he hf hr
    h_ne h_mono hAN hS
  have hwf' : LExpr.TEnvWF (T := CoreLParams) Envm :=
    Statement.typeCheckCmd_preserves_TEnvWF Cx Env Envm P _ c' htc he hf
  have hr' : TContext.AliasesResolved Envm.context :=
    Statement.typeCheckCmd_preserves_aliasesResolved Cx Env Envm P _ c' htc hr
  have h_ne' : Envm.context.types ≠ [] :=
    Statement.typeCheckCmd_preserves_context_types_ne Cx Env Envm P _ c' htc h_ne
  have habsm : Subst.absorbs S Envm.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      (go_absorbs P op Cx Envm srest (Stmt.cmd c' :: acc) labels
        ss' Env' C' hgo2 hwf' hf) habs
  have hpeel : ∀ tp, ss' = (Stmt.cmd c' :: acc).reverse ++ tp →
      allCmdTys (fun mty => LMonoTy.knownInstance mty Cx.knownTypes)
          (Statement.Command.subst S c') = true ∧ SweepAt Cx S tp :=
    fun tp htp => SweepAt.cmd_peel Cx S _ _ (hS _ (acc_cons_shift htp))
  obtain ⟨tp0, htp0⟩ :=
    (go_vars_eq Cx C' Envm Env' P op srest (Stmt.cmd c' :: acc) ss' labels hgo2).2.2
  have hsigs : FactorySigsFixed Env.context.aliases Cx.functions := hAN.1 ▸ hAN.2.2
  obtain ⟨⟨tsc, hcmd', hfe⟩, hnames⟩ :=
    Statement.typeCheckCmd_sound_output Cx Env Envm P _ c' S htc he hf hr h_ne h_mono
      (fun al hal => hAN.2.1 al (hAN.1 ▸ hal)) hsigs (hpeel tp0 htp0).1 habsm
  rw [LContext.resolveTable_eq_self hsigs, hAN.1] at hcmd'
  rw [hAN.1] at hnames
  have hmonoIn : MonoScope (IDMeta := Unit) (TContext.subst Env.context.dealias S) :=
    (MonoScope_subst_iff _ S).mpr ((MonoScope_dealias_iff Env.context).mpr h_mono)
  have hmonoC := TypeSpec.CmdExtWellTyped.monoScope hcmd' hmonoIn
  have hmonoM : MonoScope (IDMeta := Unit) (TContext.subst Envm.context.dealias S) := by
    intro z tz hz
    exact hmonoC z tz ((hfe z).trans hz)
  have h_mono' : MonoScope (IDMeta := Unit) Envm.context :=
    (MonoScope_dealias_iff Envm.context).mp ((MonoScope_subst_iff _ S).mp hmonoM)
  obtain ⟨tail_proc, tsTail, htail_eq, htail_ty, htail_fe, htail_names⟩ :=
    ih1 habs hwf' hf hr' h_ne' h_mono'
      ⟨(Statement.typeCheckCmd_preserves_context Cx Env Envm P _ c' htc).2.trans hAN.1, hAN.2⟩
      (fun tp htp => (hpeel tp htp).2)
  obtain ⟨ts2, htail2, hfe2⟩ := htail_ty.of_findEq hfe
  refine ⟨Stmt.cmd c' :: tail_proc, ts2, htail_eq.trans (reverse_cons_append_eq _ _ _), ?_⟩
  rw [List.map_cons]
  have hstmt : StatementWellTyped (P.resolveSigs A) Cx
      (TContext.subst Env.context.dealias S).types labels
      (Statement.Statement.subst S (Stmt.cmd c')) Cx tsc :=
    .cmd _ _ _ _ _ hcmd'
  exact ⟨.cons _ _ _ _ _ _ _ _ _ hstmt htail2, fun x => (hfe2 x).trans (htail_fe x), hnames,
    htail_names⟩

/-- Output soundness of the walk at a statement `block`, given the induction hypotheses for its
    sub-runs. -/
private theorem go_output_block {P : Program} {op : Option Procedure} {S : Subst}
    {A : List TypeAlias} :
    ∀ C Env acc labels m st srest label bss md bss' Eb stb ss' Env' C' st',
      ¬ labels.contains label = true →
      @Core.Statement.typeCheckAux.goBlock P op C Env bss [] (label :: labels) m st
        = .ok (bss', Eb, C, stb) →
      GoOutputMotiveB P A S C Env bss [] (label :: labels) m st bss' Eb C stb →
      @Core.Statement.typeCheckAux.go P op C Eb srest
        (Stmt.block label bss' md :: acc) labels m stb = .ok (ss', Env', C', st') →
      GoOutputMotive P A S C Eb srest (Stmt.block label bss' md :: acc) labels m stb ss' Env' C'
          st' →
      GoOutputMotive P A S C Env (Stmt.block label bss md :: srest) acc labels m st ss' Env' C'
          st' := by
  intro Cgb Env acc labels _ _ srest label bss md bss' Egb _ ss' Env' C' _ hcon hgb ih1
    hgo2 ih2 habs he hf hr h_ne h_mono hAN hS
  obtain ⟨-, hEqctx⟩ :=
    goBlock_scoping Cgb Cgb Env Egb P op bss [] bss' (label :: labels) hgb he hf
  have hWFgb : LExpr.TEnvWF (T := CoreLParams) Egb :=
    goBlock_preserves_TEnvWF Cgb Cgb Env Egb P op bss [] bss' (label :: labels) hgb he hf
  obtain ⟨hARgb, hNEgb, hMonogb, hANgb⟩ := goOutputScope_of_equiv hEqctx hr h_ne h_mono hAN
  have habsgb : Subst.absorbs S Egb.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      (go_absorbs P op Cgb Egb srest (Stmt.block label bss' md :: acc)
        labels ss' Env' C' hgo2 hWFgb hf) habs
  have hpeel : ∀ tp, ss' = (Stmt.block label bss' md :: acc).reverse ++ tp →
      SweepAt Cgb S bss' ∧ SweepAt Cgb S tp :=
    fun tp htp => SweepAt.block_peel Cgb S _ _ _ _ (hS _ (acc_cons_shift htp))
  obtain ⟨tp0, htp0⟩ :=
    (go_vars_eq Cgb C' Egb Env' P op srest (Stmt.block label bss' md :: acc) ss' labels hgo2).2.2
  obtain ⟨body_proc, C_body, ts_body, hbeq, hbty, hbnames⟩ :=
    ih1 habsgb he hf hr h_ne h_mono hAN (nil_acc_splits (hpeel tp0 htp0).1)
  simp only [List.reverse_nil, List.nil_append] at hbeq
  subst hbeq
  have hnotmem : label ∉ labels := fun hmem => hcon (List.elem_eq_true_of_mem hmem)
  obtain ⟨tp, tsTail, hteq, htty, htfe, htnames⟩ :=
    ih2 habs hWFgb hf hARgb hNEgb hMonogb hANgb (fun tp htp => (hpeel tp htp).2)
  refine ⟨Stmt.block label bss' md :: tp, tsTail,
    hteq.trans (reverse_cons_append_eq _ _ _), ?_⟩
  rw [List.map_cons]
  have hstmt0 : StatementWellTyped (P.resolveSigs A) Cgb
      (TContext.subst Env.context.dealias S).types labels
      (.block label (bss'.map (Statement.Statement.subst S)) md) Cgb
      (TContext.subst Egb.context.dealias S).types :=
    .block _ _ _ _ _ _ _ _ _ hnotmem hbty (hEqctx.dealias.subst S).1
  have hstmt : StatementWellTyped (P.resolveSigs A) Cgb
      (TContext.subst Env.context.dealias S).types labels
      (Statement.Statement.subst S (Stmt.block label bss' md)) Cgb
      (TContext.subst Egb.context.dealias S).types := by
    rw [Statement_subst_block]
    exact hstmt0
  have hstmtNames : StatementNamesWF (P.resolveSigs A) (· ∈ Cgb.functions)
      (Statement.Statement.subst S (Stmt.block label bss' md)) := by
    have hn0 : StatementNamesWF (P.resolveSigs A) (· ∈ Cgb.functions)
        (.block label (bss'.map (Statement.Statement.subst S)) md) := hbnames
    rw [Statement_subst_block]
    exact hn0
  exact ⟨.cons _ _ _ _ _ _ _ _ _ hstmt htty, htfe, hstmtNames, htnames⟩

/-- Output soundness of the walk at a statement `ite`, given the induction hypotheses for its
    sub-runs. -/
private theorem go_output_ite {P : Program} {op : Option Procedure} {S : Subst}
    {A : List TypeAlias} :
    ∀ C Env acc labels m st srest cond tss ess md condElab Ec tss' Et stt ess' Ee ste ss'
        Env' C' st',
      CondChecked C Env (renameExprOrNondet m cond) condElab Ec →
      (∀ e ∈ cond.toList, unboundAnnotVar? false C.rigidTypeVars m e = none) →
      @Core.Statement.typeCheckAux.goBlock P op C Ec tss [] labels m st
        = .ok (tss', Et, C, stt) →
      GoOutputMotiveB P A S C Ec tss [] labels m st tss' Et C stt →
      @Core.Statement.typeCheckAux.goBlock P op C Et ess [] labels m stt
        = .ok (ess', Ee, C, ste) →
      GoOutputMotiveB P A S C Et ess [] labels m stt ess' Ee C ste →
      @Core.Statement.typeCheckAux.go P op C Ee srest
        (Stmt.ite condElab tss' ess' md :: acc) labels m ste = .ok (ss', Env', C', st') →
      GoOutputMotive P A S C Ee srest (Stmt.ite condElab tss' ess' md :: acc) labels m ste ss'
          Env' C' st' →
      GoOutputMotive P A S C Env (Stmt.ite cond tss ess md :: srest) acc labels m st ss' Env' C'
          st' := by
  intro Ce Env acc labels _ _ srest cond tss ess md condElab Ec tss' Et _ ess' Ee _ ss' Env' C' _
    hcond _ hgt ih_t hge ih_e hgo ih2 habs he hf hr h_ne h_mono hAN hS
  obtain ⟨hEc_env, hEcWF, -⟩ := (hcond.chain.scope hf).facts he h_ne
  obtain ⟨hAREc, hNEEc, hMonoEc, hANEc⟩ := goOutputScope_of_equiv hEc_env hr h_ne h_mono hAN
  obtain ⟨-, hEt_eq⟩ := goBlock_scoping Ce Ce Ec Et P op tss [] tss' labels hgt hEcWF hf
  have hEt_env : TContext.Equiv (T := CoreLParams) Et.context Env.context :=
    hEt_eq.trans hEc_env
  have hEtWF : LExpr.TEnvWF (T := CoreLParams) Et :=
    goBlock_preserves_TEnvWF Ce Ce Ec Et P op tss [] tss' labels hgt hEcWF hf
  obtain ⟨hAREt, hNEEt, hMonoEt, hANEt⟩ := goOutputScope_of_equiv hEt_env hr h_ne h_mono hAN
  obtain ⟨-, hEe_eq⟩ := goBlock_scoping Ce Ce Et Ee P op ess [] ess' labels hge hEtWF hf
  have hEe_env : TContext.Equiv (T := CoreLParams) Ee.context Env.context :=
    hEe_eq.trans hEt_env
  have hEeWF : LExpr.TEnvWF (T := CoreLParams) Ee :=
    goBlock_preserves_TEnvWF Ce Ce Et Ee P op ess [] ess' labels hge hEtWF hf
  obtain ⟨hAREe, hNEEe, hMonoEe, hANEe⟩ := goOutputScope_of_equiv hEe_env hr h_ne h_mono hAN
  have habsEe : Subst.absorbs S Ee.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      (go_absorbs P op Ce Ee srest (Stmt.ite condElab tss' ess' md :: acc)
        labels ss' Env' C' hgo hEeWF hf) habs
  have habsEt : Subst.absorbs S Et.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      (goBlock_absorbs P op Ce Ce Et Ee ess [] ess' labels hge hEtWF hf) habsEe
  have habsEc : Subst.absorbs S Ec.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      (goBlock_absorbs P op Ce Ce Ec Et tss [] tss' labels hgt hEcWF hf) habsEt
  have hpeel : ∀ tp, ss' = (Stmt.ite condElab tss' ess' md :: acc).reverse ++ tp →
      SweepAt Ce S tss' ∧ SweepAt Ce S ess' ∧ SweepAt Ce S tp :=
    fun tp htp => SweepAt.ite_peel Ce S _ _ _ _ _ (hS _ (acc_cons_shift htp))
  obtain ⟨tp0, htp0⟩ :=
    (go_vars_eq Ce C' Ee Env' P op srest (Stmt.ite condElab tss' ess' md :: acc) ss' labels hgo).2.2
  obtain ⟨tp_t, Cbt, tsbt, htt_eq, htt_ty, htt_names⟩ :=
    ih_t habsEt hEcWF hf hAREc hNEEc hMonoEc hANEc
      (nil_acc_splits (hpeel tp0 htp0).1)
  obtain ⟨tsbt', htt_ty', -⟩ :=
    htt_ty.of_findEq (TContext.FindEq.subst_subst S hEc_env.symm.toFindEq.dealias).1
  obtain ⟨tp_e, Cbe, tsbe, hte_eq, hte_ty, hte_names⟩ :=
    ih_e habsEe hEtWF hf hAREt hNEEt hMonoEt hANEt
      (nil_acc_splits (hpeel tp0 htp0).2.1)
  obtain ⟨tsbe', hte_ty', -⟩ :=
    hte_ty.of_findEq (TContext.FindEq.subst_subst S hEt_env.symm.toFindEq.dealias).1
  obtain ⟨tp, tsTail, ht_eq, ht_ty, ht_fe, ht_names⟩ :=
    ih2 habs hEeWF hf hAREe hNEEe hMonoEe hANEe
      (fun tp htp => (hpeel tp htp).2.2)
  simp only [List.reverse_nil, List.nil_append] at htt_eq hte_eq
  subst htt_eq; subst hte_eq
  refine ⟨Stmt.ite condElab tss' ess' md :: tp, tsTail,
    ht_eq.trans (reverse_cons_append_eq _ _ _), ?_⟩
  rw [List.map_cons]
  -- Only the typing rule for the statement itself depends on the condition's form.
  have hstmt0 : StatementWellTyped (P.resolveSigs A) Ce
      (TContext.subst Env.context.dealias S).types labels
      (Stmt.ite (condElab.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
        (tss'.map (Statement.Statement.subst S)) (ess'.map (Statement.Statement.subst S)) md)
      Ce (TContext.subst Ee.context.dealias S).types := by
    cases cond with
    | det c =>
      obtain ⟨conda, hrs, hbool, rfl⟩ := hcond
      have hguard : Lambda.LExpr.HasTypeA (T := CoreLParams) []
          (conda.unresolved) (.tcons "bool" []) :=
        hbool ▸ resolveSource_HasTypeA _ conda Ce Env Ec hrs he hf hr
      have hguard' : Lambda.LExpr.HasTypeA (T := CoreLParams) []
          (LExpr.applyTypeSubst (LExpr.unresolved conda) S)
          (LMonoTy.tcons "bool" []) := by
        have h0 := hasTypeA_applyTypeSubst S hguard
        rwa [show LMonoTy.subst S (LMonoTy.tcons "bool" []) = LMonoTy.tcons "bool" [] from
          LMonoTy.subst_bool S] at h0
      have hguardB : BinderAnnotsKnown Ce
          (LExpr.applyTypeSubst (LExpr.unresolved conda) S) :=
        SweepAt.ite_condKnown Ce S _ _ _ md tp (hS _ (acc_cons_shift ht_eq))
      have hguardA : ExprWellTyped Ce (TContext.subst Env.context.dealias S).types
          (LExpr.applyTypeSubst (LExpr.unresolved conda) S) LMonoTy.bool :=
        ⟨hguard', hguardB, resolveSource_annotAgree_dealias _ conda Ce Env Ec hrs he hf
          h_mono (hAN.1 ▸ hAN.2.2) (TContext.FindEq.refl _) S habsEc⟩
      exact .ite_det _ _ _ _ _ _ _ _ _ _ _ _ hguardA htt_ty' hte_ty'
        (hEe_env.dealias.subst S).1
    | nondet =>
      obtain ⟨rfl, -⟩ := hcond
      exact .ite_nondet _ _ _ _ _ _ _ _ _ _ _ htt_ty' hte_ty' (hEe_env.dealias.subst S).1
  have hstmt : StatementWellTyped (P.resolveSigs A) Ce
      (TContext.subst Env.context.dealias S).types labels
      (Statement.Statement.subst S (Stmt.ite condElab tss' ess' md))
      Ce (TContext.subst Ee.context.dealias S).types := by
    rw [Statement_subst_ite]
    exact hstmt0
  have hstmtNames : StatementNamesWF (P.resolveSigs A) (· ∈ Ce.functions)
      (Statement.Statement.subst S (Stmt.ite condElab tss' ess' md)) := by
    have hn0 : StatementNamesWF (P.resolveSigs A) (· ∈ Ce.functions)
        (Stmt.ite (condElab.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
          (tss'.map (Statement.Statement.subst S)) (ess'.map (Statement.Statement.subst S))
          md) := ⟨htt_names, hte_names⟩
    rw [Statement_subst_ite]
    exact hn0
  exact ⟨.cons _ _ _ _ _ _ _ _ _ hstmt ht_ty, ht_fe, hstmtNames, ht_names⟩

/-- Output soundness of the walk at a statement `loop`, given the induction hypotheses for its
    sub-runs. -/
private theorem go_output_loop {P : Program} {op : Option Procedure} {S : Subst}
    {A : List TypeAlias} :
    ∀ C Env acc labels m st srest guard measure invariant bss md guardElab Eg measureElab
        Em invElab Efold bss' Eb stb ss' Env' C' st',
      CondChecked C Env (renameExprOrNondet m guard) guardElab Eg →
      MeasureChecked C Eg (measure.map (renameExpr m)) measureElab Em →
      InvariantsChecked C Em (invariant.map (fun (l, i) => (l, renameExpr m i))) invElab Efold →
      (∀ e ∈ Statement.loopExprs guard measure invariant,
        unboundAnnotVar? false C.rigidTypeVars m e = none) →
      @Core.Statement.typeCheckAux.goBlock P op C Efold bss [] labels m st
        = .ok (bss', Eb, C, stb) →
      GoOutputMotiveB P A S C Efold bss [] labels m st bss' Eb C stb →
      @Core.Statement.typeCheckAux.go P op C Eb srest
        (Stmt.loop guardElab measureElab invElab bss' md :: acc) labels m stb
        = .ok (ss', Env', C', st') →
      GoOutputMotive P A S C Eb srest (Stmt.loop guardElab measureElab invElab bss' md :: acc)
          labels m stb
        ss' Env' C' st' →
      GoOutputMotive P A S C Env (Stmt.loop guard measure invariant bss md :: srest) acc labels m
          st ss' Env'
        C' st' := by
  intro Cx Env acc labels _ _ srest guard measure invariant bss md guardElab Eg measureElab Em
    invElab Efold bss' Ebody _ ss' Env' C' _ hgc hmc hic _ hbody ih1 htail ih2 habs he hf hr
    h_ne h_mono hAN hS
  obtain ⟨hg, hm, hi, hEfoldCtx, hEfoldWF, hEfoldAR⟩ :=
    loopHead_annotated hgc hmc hic he hf hr h_ne
  have hEbodyWF : LExpr.TEnvWF (T := CoreLParams) Ebody :=
    goBlock_preserves_TEnvWF Cx Cx Efold Ebody P op bss [] bss' labels hbody hEfoldWF hf
  have habsEbody : Subst.absorbs S Ebody.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      (go_absorbs P op Cx Ebody srest
        (Stmt.loop guardElab measureElab invElab bss' md :: acc) labels ss' Env' C' htail
        hEbodyWF hf) habs
  have habsEfold : Subst.absorbs S Efold.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      (goBlock_absorbs P op Cx Cx Efold Ebody bss [] bss' labels hbody
        hEfoldWF hf) habsEbody
  have hpeel : ∀ tp, ss' = (Stmt.loop guardElab measureElab invElab bss' md
        :: acc).reverse ++ tp →
      SweepAt Cx S bss' ∧ SweepAt Cx S tp :=
    fun tp htp => SweepAt.loop_peel Cx S _ _ _ _ _ _ (hS _ (acc_cons_shift htp))
  obtain ⟨tp0, htp0⟩ :=
    (go_vars_eq Cx C' Ebody Env' P op srest (Stmt.loop guardElab measureElab invElab bss' md ::
        acc) ss' labels htail).2.2
  obtain ⟨body_proc, C_body, ts_body, hbeq, hbty, hbnames⟩ :=
    ih1 habsEbody hEfoldWF hf hEfoldAR
      (hEfoldCtx.symm.types_ne_nil h_ne)
      (MonoScope_of_findEq hEfoldCtx.toFindEq h_mono)
      ⟨hEfoldCtx.2.trans hAN.1, hAN.2⟩
      (nil_acc_splits (hpeel tp0 htp0).1)
  simp only [List.reverse_nil, List.nil_append] at hbeq
  subst body_proc
  obtain ⟨ts_body', hbty', -⟩ :=
    hbty.of_findEq (TContext.FindEq.subst_subst S hEfoldCtx.symm.toFindEq.dealias).1
  obtain ⟨-, hEbody_eq⟩ :=
    goBlock_scoping Cx Cx Efold Ebody P op bss [] bss' labels hbody hEfoldWF hf
  have hEbody_env : TContext.Equiv (T := CoreLParams) Ebody.context Env.context :=
    hEbody_eq.trans hEfoldCtx
  have hEbodyAR : TContext.AliasesResolved Ebody.context :=
    goBlock_preserves_aliasesResolved Cx Cx Efold Ebody P op bss [] bss' labels hbody hEfoldWF hf
      hEfoldAR
  obtain ⟨tp, tsTail, ht_eq, ht_ty, ht_fe, ht_names⟩ :=
    ih2 habs
      hEbodyWF hf hEbodyAR
      (hEbody_env.symm.types_ne_nil h_ne)
      (MonoScope_of_findEq hEbody_env.toFindEq h_mono)
      ⟨hEbody_env.2.trans hAN.1, hAN.2⟩
      (fun tp htp => (hpeel tp htp).2)
  refine ⟨Stmt.loop guardElab measureElab invElab bss' md :: tp, tsTail,
    ht_eq.trans (reverse_cons_append_eq _ _ _), ?_⟩
  rw [List.map_cons]
  have hm' : ∀ m, measureElab.map (·.applyTypeSubst S) = some m →
      Lambda.LExpr.HasTypeA (T := CoreLParams) [] m (.tcons "int" []) := by
    intro m hms
    cases measureElab with
    | none => simp only [Option.map_none, reduceCtorEq] at hms
    | some m0 =>
      simp only [Option.map_some, Option.some.injEq] at hms
      subst hms
      have h0 := hasTypeA_applyTypeSubst S (hm m0 rfl)
      rwa [LMonoTy.subst_tcons, LMonoTys.subst_nil] at h0
  have hi' : ∀ p,
      p ∈ invElab.map (fun p => (p.1, p.2.applyTypeSubst S)) →
        Lambda.LExpr.HasTypeA (T := CoreLParams) [] p.2 (.tcons "bool" []) := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, hqe⟩ := hp
    subst hqe
    have h0 := hasTypeA_applyTypeSubst S (hi q hq)
    rwa [show LMonoTy.subst S (LMonoTy.tcons "bool" []) = LMonoTy.tcons "bool" [] from
      LMonoTy.subst_bool S] at h0
  obtain ⟨hgAg0, hmAg0, hiAg0⟩ := loopHead_annotAgree hgc hmc hic he hf h_mono h_ne
    (hAN.1 ▸ hAN.2.2) S habsEfold
  have hgFacts : ∀ g,
      (guardElab.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S) :
        ExprOrNondet Expression) = .det g →
        Lambda.LExpr.HasTypeA (T := CoreLParams) [] g (.tcons "bool" [])
          ∧ TypeSpec.ScopesAnnotAgree Cx (TContext.subst Env.context.dealias S).types g := by
    intro g hgd
    cases guardElab with
    | nondet => simp only [Imperative.ExprOrNondet.map, reduceCtorEq] at hgd
    | det g0 =>
      simp only [Imperative.ExprOrNondet.map, Imperative.ExprOrNondet.det.injEq] at hgd
      subst g
      have h0 := hasTypeA_applyTypeSubst S (hg g0 rfl)
      rw [show LMonoTy.subst S (LMonoTy.tcons "bool" []) = LMonoTy.tcons "bool" [] from
        LMonoTy.subst_bool S] at h0
      exact ⟨h0, hgAg0 g0 rfl⟩
  have hmAg : ∀ m, measureElab.map (·.applyTypeSubst S) = some m →
      TypeSpec.ScopesAnnotAgree Cx (TContext.subst Env.context.dealias S).types m := by
    intro m hms
    cases measureElab with
    | none => simp only [Option.map_none, reduceCtorEq] at hms
    | some m0 =>
      simp only [Option.map_some, Option.some.injEq] at hms
      subst hms
      exact hmAg0 m0 rfl
  have hiAg : ∀ p,
      p ∈ invElab.map (fun p => (p.1, p.2.applyTypeSubst S)) →
        TypeSpec.ScopesAnnotAgree Cx (TContext.subst Env.context.dealias S).types p.2 := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, hqe⟩ := hp
    subst hqe
    exact hiAg0 q hq
  obtain ⟨hgK, hmK, hiK⟩ :=
    SweepAt.loop_known Cx S guardElab measureElab invElab bss' md tp (hS _ (acc_cons_shift ht_eq))
  have hgA : ∀ g,
      (guardElab.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S) :
        ExprOrNondet Expression) = .det g →
        ExprWellTyped Cx (TContext.subst Env.context.dealias S).types g LMonoTy.bool := by
    intro g hgd
    obtain ⟨hty, hag⟩ := hgFacts g hgd
    exact ⟨hty, hgK g hgd, hag⟩
  have hmA : ∀ m, measureElab.map (·.applyTypeSubst S) = some m →
      ExprWellTyped Cx (TContext.subst Env.context.dealias S).types m LMonoTy.int := by
    intro m hms
    exact ⟨hm' m hms, hmK m hms, hmAg m hms⟩
  have hiA : ∀ p,
      p ∈ invElab.map (fun p => (p.1, p.2.applyTypeSubst S)) →
        ExprWellTyped Cx (TContext.subst Env.context.dealias S).types p.2 LMonoTy.bool := by
    intro p hp
    exact ⟨hi' p hp, hiK p hp, hiAg p hp⟩
  have hstmt0 : StatementWellTyped (P.resolveSigs A) Cx
      (TContext.subst Env.context.dealias S).types labels
      (Stmt.loop (guardElab.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
        (measureElab.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
        (invElab.map (fun p => (p.1, LExpr.applyTypeSubst p.2 S)))
        (bss'.map (Statement.Statement.subst S)) md)
      Cx (TContext.subst Ebody.context.dealias S).types :=
    .loop _ _ _ _ _ _ _ _ _ _ _ hgA hmA hiA hbty' (hEbody_env.dealias.subst S).1
  have hstmt : StatementWellTyped (P.resolveSigs A) Cx
      (TContext.subst Env.context.dealias S).types labels
      (Statement.Statement.subst S (Stmt.loop guardElab measureElab invElab bss' md))
      Cx (TContext.subst Ebody.context.dealias S).types := by
    rw [Statement_subst_loop]
    exact hstmt0
  have hstmtNames : StatementNamesWF (P.resolveSigs A) (· ∈ Cx.functions)
      (Statement.Statement.subst S (Stmt.loop guardElab measureElab invElab bss' md)) := by
    have hn0 : StatementNamesWF (P.resolveSigs A) (· ∈ Cx.functions)
        (Stmt.loop (guardElab.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
          (measureElab.map (fun e : Expression.Expr => LExpr.applyTypeSubst e S))
          (invElab.map (fun p => (p.1, LExpr.applyTypeSubst p.2 S)))
          (bss'.map (Statement.Statement.subst S)) md) := hbnames
    rw [Statement_subst_loop]
    exact hn0
  exact ⟨.cons _ _ _ _ _ _ _ _ _ hstmt ht_ty, ht_fe, hstmtNames, ht_names⟩

/-- Output soundness of the walk: under any `S` absorbing its substitution, the emitted
    statements with `S` applied are well typed from the `S`-applied resolved input scope to scopes
    agreeing by lookup with the `S`-applied resolved output scope, and their names are valid. -/
private theorem go_output_sound_subst
    (P : Program) (op : Option Procedure) (S : Subst) (A : List TypeAlias)
    (C : LContext CoreLParams) (Env : TEnv Unit) (ss acc : List Statement)
    (labels : List String)
    (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st'))
    (habs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hr : TContext.AliasesResolved Env.context)
    (h_ne : Env.context.types ≠ [])
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliases : AliasesAt A C Env.context)
    (hS : ∀ ss_proc, ss' = acc.reverse ++ ss_proc → SweepAt C S ss_proc) :
    ∃ ss_proc tsOut, ss' = acc.reverse ++ ss_proc ∧
      StatementsWellTyped (P.resolveSigs A) C (TContext.subst Env.context.dealias S).types
        labels (ss_proc.map (Statement.Statement.subst S)) C' tsOut ∧
      (∀ x, tsOut.find? x = (TContext.subst Env'.context.dealias S).types.find? x) ∧
      StatementsNamesWF (P.resolveSigs A) (· ∈ C.functions)
        (ss_proc.map (Statement.Statement.subst S)) := by
  refine go_ok_induct
    (motive := GoOutputMotive P A S)
    (motiveB := GoOutputMotiveB P A S)
    ?nil go_output_cmd go_output_block go_output_ite go_output_loop ?exit ?typeDecl ?blockScope
        ?blockFlat C Env ss acc labels ss'
    Env' C' h habs he hf hr h_ne h_mono h_aliases hS
  case nil =>
    intro Cx Env acc labels _ _ _ _ _ _ _ _ _ _
    exact ⟨[], (TContext.subst Env.context.dealias S).types, by simp,
      .nil _ _ _ _ (HMaps.Equiv.refl _), fun _ => rfl, trivial⟩
  case exit =>
    intro Cx Env acc labels _ _ srest l md ss' Env' C' _ _ hc _ ih1
      habs he hf hr h_ne h_mono hAN hS
    obtain ⟨tp, tsTail, heq, hty, hfe, hnames⟩ :=
      ih1 habs he hf hr h_ne h_mono hAN
        (fun tp htp => sweepAt_tail_of_keeps Cx S (Stmt.exit l md) tp
          (tysDeclaredStmt_exit Cx.knownTypes l md) (hS _ (acc_cons_shift htp)))
    refine ⟨Stmt.exit l md :: tp, tsTail, heq.trans (reverse_cons_append_eq _ _ _), ?_⟩
    rw [List.map_cons]
    have hstmt : StatementWellTyped (P.resolveSigs A) Cx
        (TContext.subst Env.context.dealias S).types labels
        (Statement.Statement.subst S (Stmt.exit l md)) Cx
        (TContext.subst Env.context.dealias S).types :=
      .exit _ _ _ _ _ _ (List.mem_of_elem_eq_true hc) (HMaps.Equiv.refl _)
    exact ⟨.cons _ _ _ _ _ _ _ _ _ hstmt hty, hfe, trivial, hnames⟩
  case typeDecl =>
    intro Cx Env acc labels _ _ srest tc md Cnew ss' Env' C' _ htc _ ih1
      habs he hf hr h_ne h_mono hAN hS
    obtain ⟨hprogP, hnotAliasLocal, hktAll⟩ :=
      TypeConstructor.typeCheck_decompose tc (.bodyLocal P.getNames) Cx Cnew Env htc
    have hnotAlias := hnotAliasLocal rfl
    have hprog : ∀ n ∈ (P.resolveSigs A).getNames, n.name ≠ tc.name := by
      rw [Program.resolveSigs_getNames]
      exact hprogP
    have hkt := hktAll (default : Strata.Message)
    have hfun := TypeConstructor.typeCheck_functions_eq htc
    have hfCnew : FactorySigWF Cnew.functions := hfun ▸ hf
    have hANnew : AliasesAt A Cnew Env.context := by
      refine ⟨hAN.1, fun al hal => ?_, ?_⟩
      · have hne : tc.name ≠ al.name := fun heq => hnotAlias al (hAN.1 ▸ hal) heq.symm
        exact knownTypes_addKnownTypeWithError_notContains_of_ne Cx Cnew _ _ al.name hkt hne
          (hAN.2.1 al hal)
      · rw [hfun]
        exact hAN.2.2
    obtain ⟨tp, tsTail, heq, hty, hfe, hnames⟩ :=
      ih1 habs he hfCnew hr h_ne h_mono hANnew
        (fun tp htp => SweepAt.typeDecl_peel Cx Cnew S tc md tp _ hkt (hS _ (acc_cons_shift htp)))
    refine ⟨Stmt.typeDecl tc md :: tp, tsTail,
      heq.trans (reverse_cons_append_eq _ _ _), ?_⟩
    rw [List.map_cons]
    have hprogKind : ∀ n ∈ programNamesOfKind (P.resolveSigs A) .type, n.name ≠ tc.name :=
      fun n hn => hprog n ((List.filter_sublist.flatMap_of_sublist _).subset hn)
    have hstmt : StatementWellTyped (P.resolveSigs A) Cx
        (TContext.subst Env.context.dealias S).types labels
        (Statement.Statement.subst S (Stmt.typeDecl tc md)) Cnew
        (TContext.subst Env.context.dealias S).types :=
      .typeDecl _ _ _ _ _ _ _ hprogKind hkt (HMaps.Equiv.refl _)
    have htailNames : StatementsNamesWF (P.resolveSigs A) (· ∈ Cx.functions)
        (tp.map (Statement.Statement.subst S)) := by
      rw [← hfun]
      exact hnames
    exact ⟨.cons _ _ _ _ _ _ _ _ _ hstmt hty, hfe, hprog, htailNames⟩
  case blockFlat =>
    intro _ _ _ _ _ _ _ _ _ Cgo _ _ _ _ ih1 habs he hf hr h_ne h_mono hAN hS
    obtain ⟨ss_proc, tsOut, hproc_eq, hproc_ty, -, hnames⟩ :=
      ih1 habs he hf hr h_ne h_mono hAN hS
    exact ⟨ss_proc, Cgo, tsOut, hproc_eq, hproc_ty, hnames⟩
  case blockScope =>
    intro Cx Envpre bss acc labels _ _ bss2 Ego Cgo _ hg ih1 habs he hf hr h_ne h_mono hAN hS
    obtain ⟨ss_proc, tsOut, hproc_eq, hproc_ty, -, hnames⟩ :=
      ih1 habs
        (Lambda.pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Envpre he) hf
        (Lambda.TEnv.pushEmptyContext_preserves_aliasesResolved Envpre hr)
        (Lambda.TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Envpre)
        (MonoScope_of_findEq
          (Lambda.pushEmptyContext_context_FindEq (T := CoreLParams) Envpre) h_mono)
        hAN hS
    obtain ⟨tsOut', hty', -⟩ :=
      hproc_ty.of_findEq (TContext.FindEq.subst_subst S
        (Lambda.pushEmptyContext_context_FindEq (T := CoreLParams) Envpre).symm.dealias).1
    exact ⟨ss_proc, Cgo, tsOut', hproc_eq, hty', hnames⟩

end DirectSoundness

/-! ### Output soundness of `Statement.typeCheck` -/

/-- Statement checking keeps the type names of the literals of its input. -/
theorem Statement.typeCheck_litTyNames_eq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env')) :
    stmtsLitTyNames ss' = stmtsLitTyNames ss := by
  obtain ⟨ssA, EnvA, CA, hAux, hssGo, -, -⟩ := Statement.typeCheck_ok_inv C Env Env' P op ss ss' h
  obtain ⟨st', hgo⟩ := typeCheckAux_ok_inv hAux
  have hwalk := go_litTyNames_eq C CA _ EnvA P op ss [] ssA _ hgo
  rw [hssGo, Statement_subst_go_eq, List.reverse_nil, List.nil_append,
    stmtsLitTyNames_map_subst]
  exact GoPreserves.of_nil_acc hwalk

/-- Output soundness of statement checking: the emitted list, outside any labeled block, is well
    typed against the alias-resolved factory table and procedure signatures, in the input scope
    with the checker's final substitution applied and aliases resolved, and its names are valid.
    The hypotheses mean: the input environment and function table are well formed; the aliases
    are fully resolved (`h_resolved`); the scope is a nonempty stack of monotypes (`h_types_ne`,
    `h_mono`); no alias is named after a registered type (`h_aliasNames`); and the factory
    signatures are unchanged by alias resolution (`h_sigsFixed`). -/
theorem Statement.typeCheck_sound_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_types_ne : Env.context.types ≠ [])
    (h_mono : MonoScope (IDMeta := Unit) Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions) :
    (∃ C' ts', StatementsWellTyped (P.resolveSigs Env.context.aliases)
      (C.resolveTable Env.context.aliases)
      (TContext.subst Env.context.dealias Env'.stateSubstInfo.subst).types [] ss' C' ts') ∧
    StatementsNamesWF (P.resolveSigs Env.context.aliases) (· ∈ C.functions) ss' := by
  obtain ⟨ssA, EnvA, CA, hAux, hssGo, hEnv, -⟩ :=
    Statement.typeCheck_ok_inv C Env Env' P op ss ss' h
  have hss' : ss' = ssA.map (Statement.Statement.subst
      (Statement.finalSubstInfo Env.genEnv.genState EnvA).subst) := by
    rw [hssGo, Statement_subst_go_eq]
    simp only [List.reverse_nil, List.nil_append]
  have hSubst : Env'.stateSubstInfo =
      Statement.finalSubstInfo Env.genEnv.genState EnvA := by rw [hEnv]; rfl
  obtain ⟨_, hgo⟩ := typeCheckAux_ok_inv hAux
  have hsweep := typeCheck_sweepAt C Env Env' P op ss ss' h _ _ _ hAux
  obtain ⟨ss_proc, tsOut, hproc_eq, hproc_ty, -, hnames⟩ :=
    go_output_sound_subst P op
      (Statement.finalSubstInfo Env.genEnv.genState EnvA).subst Env.context.aliases
      C Env ss [] [] ssA EnvA CA hgo
      (Statement.finalSubstInfo_absorbs Env.genEnv.genState EnvA) h_env h_fac h_resolved
      h_types_ne h_mono ⟨rfl, h_aliasNames, h_sigsFixed⟩
      (nil_acc_splits hsweep)
  simp only [List.reverse_nil, List.nil_append] at hproc_eq
  subst hproc_eq
  subst hss'
  rw [hSubst, LContext.resolveTable_eq_self h_sigsFixed]
  exact ⟨⟨CA, tsOut, hproc_ty⟩, hnames⟩

end OutputSubstStability

/-! ## Call sites of a checked statement list -/

section CallDescent

/-- `n` is one of the program's declared names. -/
abbrev DeclaredProgramName (program : Program) (n : String) : Prop :=
  ∃ m ∈ Program.getNames program, m.name = n

/-- The command checker accepts a call of `nm` at some context and environment with `Env`'s
    aliases, registering no program-declared name that `C` lacks. -/
def CallSiteAgreeing (P : Program) (nm : String)
    (C : LContext CoreLParams) (Env : TEnv Unit) : Prop :=
  ∃ (Ccall : LContext CoreLParams) (Envcall : TEnv Unit)
    (callArgs : List (CallArg Expression)) (mdc : MetaData Expression)
    (tyArgs : Option (List Expression.Ty)) (rc : Command × TEnv Unit),
    Statement.typeCheckCmd Ccall Envcall P (.call nm tyArgs callArgs mdc) = .ok rc ∧
    Envcall.context.aliases = Env.context.aliases ∧
    ∀ x, DeclaredProgramName P x →
      C.knownTypes.containsName x = false → Ccall.knownTypes.containsName x = false

/-- Call-site agreement transfers from `C2`/`Env2` to `C`/`Env` when they share aliases and `C2`
    registers no program-declared name that `C` lacks. -/
theorem CallSiteAgreeing.compose {P : Program} {nm : String} {C C2 : LContext CoreLParams}
    {Env Env2 : TEnv Unit}
    (h : CallSiteAgreeing P nm C2 Env2)
    (halias : Env2.context.aliases = Env.context.aliases)
    (hkt : ∀ x, DeclaredProgramName P x →
      C.knownTypes.containsName x = false → C2.knownTypes.containsName x = false) :
    CallSiteAgreeing P nm C Env := by
  obtain ⟨Ccall, Envcall, callArgs, mdc, tyArgs, rc, hcall, hal, hkt2⟩ := h
  exact ⟨Ccall, Envcall, callArgs, mdc, tyArgs, rc, hcall, hal.trans halias,
    fun x hx hxC => hkt2 x hx (hkt x hx hxC)⟩

/-- Every procedure name a checked statement list can call has a call site agreeing with `C` and
    `Env`. -/
private theorem go_call_descent
    (P : Program) (op : Option Procedure) (nm : String)
    (C : LContext CoreLParams) (Env : TEnv Unit) (ss acc : List Statement)
    (labels : List String) (ss' : List Statement) (Env' : TEnv Unit)
    (C' : LContext CoreLParams)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (hmem : nm ∈ Statements.calledProcedureNames ss) :
    CallSiteAgreeing P nm C Env := by
  -- A call site reached from a later environment of the same context is reached from `Env`.
  have hstep : ∀ C (Env Eb : TEnv Unit) (bs : List Statement), EnvScopeStep Env Eb →
      LExpr.TEnvWF (T := CoreLParams) Env → Env.context.types ≠ [] →
      (LExpr.TEnvWF (T := CoreLParams) Eb → Eb.context.types ≠ [] →
        nm ∈ Statements.calledProcedureNames bs → CallSiteAgreeing P nm C Eb) →
      nm ∈ Statements.calledProcedureNames bs → CallSiteAgreeing P nm C Env := by
    intro C Env Eb bs hR he hne ih hin
    obtain ⟨heq, hwf, hne'⟩ := hR.facts he hne
    exact (ih hwf hne' hin).compose heq.2 (fun _ _ hx => hx)
  refine go_ok_induct
    (motive := fun C Env ss _ _ _ _ _ _ _ _ => LExpr.TEnvWF (T := CoreLParams) Env →
      FactorySigWF C.functions → Env.context.types ≠ [] →
      nm ∈ Statements.calledProcedureNames ss → CallSiteAgreeing P nm C Env)
    (motiveB := fun C Env ss _ _ _ _ _ _ _ _ => LExpr.TEnvWF (T := CoreLParams) Env →
      FactorySigWF C.functions → Env.context.types ≠ [] →
      nm ∈ Statements.calledProcedureNames ss → CallSiteAgreeing P nm C Env)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h he hf h_ne hmem
  case nil =>
    intro _ _ _ _ _ _ _ _ _ hmem
    simp at hmem
  case cmd =>
    intro C Env _ _ _ _ srest cmd c' Env1 _ _ _ _ htc _ _ ih he hf h_ne hmem
    simp only [Statements.calledProcedureNames_cons, Statement.calledProcedureNames_cmd,
      List.mem_append] at hmem
    rcases hmem with hin | hin
    · cases cmd with
      | cmd c => simp only [CmdExt.calledProcedureNames_cmd, List.not_mem_nil] at hin
      | call pname tyArgs callArgs mdc =>
        simp only [CmdExt.calledProcedureNames_call, List.mem_singleton] at hin
        subst hin
        exact ⟨_, _, _, _, _, _, htc, rfl, fun _ _ hx => hx⟩
    · exact (ih (Statement.typeCheckCmd_preserves_TEnvWF C Env Env1 P _ c' htc he hf) hf
        (Statement.typeCheckCmd_preserves_context_types_ne C Env Env1 P _ c' htc h_ne) hin).compose
        (Statement.typeCheckCmd_preserves_context C Env Env1 P _ c' htc).2 (fun _ _ hx => hx)
  case block =>
    intro C Env _ _ _ _ srest _ _ _ _ Eb _ _ _ _ _ _ hgb ihb _ ih he hf h_ne hmem
    simp only [Statements.calledProcedureNames_cons, Statement.calledProcedureNames_block,
      List.mem_append] at hmem
    rcases hmem with hin | hin
    · exact ihb he hf h_ne hin
    · exact hstep C Env Eb srest (EnvScopeStep.of_goBlock hgb hf) he h_ne
        (fun hwf hne => ih hwf hf hne) hin
  case ite =>
    intro C Env _ _ _ _ srest _ tss ess _ _ Ec _ Et _ _ Ee _ _ _ _ _ hcond _ hgt iht hge ihe _ ih
      he hf h_ne hmem
    simp only [Statements.calledProcedureNames_cons, Statement.calledProcedureNames_ite,
      List.mem_append] at hmem
    have hEc : EnvScopeStep Env Ec := hcond.chain.scope hf
    have hEt : EnvScopeStep Env Et := hEc.trans (EnvScopeStep.of_goBlock hgt hf)
    rcases hmem with (hin | hin) | hin
    · exact hstep C Env Ec tss hEc he h_ne (fun hwf hne => iht hwf hf hne) hin
    · exact hstep C Env Et ess hEt he h_ne (fun hwf hne => ihe hwf hf hne) hin
    · exact hstep C Env Ee srest (hEt.trans (EnvScopeStep.of_goBlock hge hf)) he h_ne
        (fun hwf hne => ih hwf hf hne) hin
  case loop =>
    intro C Env _ _ _ _ srest _ _ _ bss _ _ _ _ _ _ Efold _ Eb _ _ _ _ _ hg hm hi _ hgb ihb _ ih he
      hf h_ne hmem
    simp only [Statements.calledProcedureNames_cons, Statement.calledProcedureNames_loop,
      List.mem_append] at hmem
    have hEfold : EnvScopeStep Env Efold := (loopHead_chain hg hm hi).scope hf
    rcases hmem with hin | hin
    · exact hstep C Env Efold bss hEfold he h_ne (fun hwf hne => ihb hwf hf hne) hin
    · exact hstep C Env Eb srest (hEfold.trans (EnvScopeStep.of_goBlock hgb hf)) he h_ne
        (fun hwf hne => ih hwf hf hne) hin
  case exit =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih he hf h_ne hmem
    simp only [Statements.calledProcedureNames_cons, Statement.calledProcedureNames_exit,
      List.nil_append] at hmem
    exact ih he hf h_ne hmem
  case typeDecl =>
    intro C Env _ _ _ _ _ tc _ Cnew _ _ _ _ htc _ ih he hf h_ne hmem
    simp only [Statements.calledProcedureNames_cons, Statement.calledProcedureNames_typeDecl,
      List.nil_append] at hmem
    obtain ⟨hpname, -, hktAll⟩ :=
      TypeConstructor.typeCheck_decompose tc (.bodyLocal P.getNames) C Cnew Env htc
    have hkt := hktAll (default : Strata.Message)
    refine (ih he (TypeConstructor.typeCheck_functions_eq htc ▸ hf) h_ne
      hmem).compose rfl ?_
    intro x hdeclx hx
    have hne : tc.name ≠ x := by
      intro heq
      obtain ⟨m, hmemx, hmname⟩ := hdeclx
      exact hpname m hmemx (hmname.trans heq.symm)
    exact knownTypes_addKnownTypeWithError_notContains_of_ne C Cnew _ _ x hkt hne hx
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih
  case blockScope =>
    intro _ Env _ _ _ _ _ _ _ _ _ _ ih he hf _ hmem
    refine (ih (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he) hf
      (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Env) hmem).compose
      ?_ (fun _ _ hx => hx)
    simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]

end CallDescent

end -- public section

end Core
