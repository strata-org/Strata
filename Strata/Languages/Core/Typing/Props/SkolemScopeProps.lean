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
public import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
import all Strata.Languages.Core.Typing.Props.SourceExprResolveProps
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps

/-! # Skolem-scope elimination

A polymorphic typing derivation over the skolemized scope transfers to the parameter scope.
Also here: rigid constants chosen against the type names in scope change nothing in scope.

Key theorems:
* `HasType_of_skolemScope_general`: a typing over the skolem scope gives one for the
  deskolemized expression.
* `ScopeRigid.of_cover`, `NoSkolemAmbient.of_not_scopeTyNames`: rigid constants chosen against
  the names in scope satisfy the rigid-renaming conditions.
* `knownInstance_skolemizeTy`: skolemizing a registered type gives a registered type. -/

public section

namespace Core

open Lambda Imperative

open Strata.Util (HMap HMaps)

/-- A user-declarable name registered with the rigid constants added is registered without them. -/
private theorem containsName_of_addSkolemTypes (C : Expression.TyContext) {σ : RigidNames}
    (hpfx : RigidNamesPrefixed σ)
    (x : String) (hallowed : isAllowedName x = true)
    (h : (addSkolemTypes C σ).knownTypes.containsName x = true) :
    C.knownTypes.containsName x = true := by
  by_cases hx : C.knownTypes.containsName x = true
  · exact hx
  · rw [addSkolemTypes_notContains_of_isAllowedName C σ hpfx x hallowed
      (by simpa using hx)] at h
    exact absurd h (by simp)

/-- If deskolemization fixes a constructor application, its head is not a rigid constant and
    deskolemization fixes its arguments. -/
private theorem deskolemizeTy_tcons_fixed_inv {σ : RigidNames} {nm : String} {args : LMonoTys}
    (h : deskolemizeTy σ (.tcons nm args) = .tcons nm args) :
    σ.find? (fun q => q.2 == nm) = none ∧ ∀ t ∈ args, deskolemizeTy σ t = t := by
  rw [deskolemizeTy_tcons] at h
  cases hfind : σ.find? (fun q => q.2 == nm) with
  | some a =>
    rw [hfind] at h
    exact absurd h (by simp)
  | none =>
    rw [hfind] at h
    simp only [LMonoTy.tcons.injEq, true_and] at h
    exact ⟨rfl, List.forall_eq_self_of_map_eq_self h⟩

/-- On a type deskolemization fixes, deskolemizing after substituting by `S` is substituting by
    any `S'` that matches deskolemized `S` on each free variable. -/
theorem deskolemizeTy_subst_eq_subst (σ : RigidNames) (S S' : Subst) (mty : LMonoTy)
    (h_fix : deskolemizeTy σ mty = mty)
    (h_pt : ∀ x ∈ LMonoTy.freeVars mty,
      deskolemizeTy σ (LMonoTy.subst S (.ftvar x)) = LMonoTy.subst S' (.ftvar x)) :
    deskolemizeTy σ (LMonoTy.subst S mty) = LMonoTy.subst S' mty := by
  induction mty with
  | ftvar x => exact h_pt x (by simp [LMonoTy.freeVars])
  | bitvec n =>
    rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
    exact rfl
  | tcons nm args ih =>
    obtain ⟨hfind, hpt_args⟩ := deskolemizeTy_tcons_fixed_inv h_fix
    have hmap : List.map (deskolemizeTy σ) (List.map (LMonoTy.subst S) args)
        = List.map (LMonoTy.subst S') args := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro t ht
      simp only [Function.comp_apply]
      refine ih t ht (hpt_args t ht) ?_
      intro v hv
      have hv_tcons : v ∈ (LMonoTy.tcons nm args).freeVars := by
        simp only [LMonoTy.freeVars]
        exact LMonoTys.freeVars_mem_subset ht hv
      exact h_pt v hv_tcons
    rw [LMonoTy.subst_tcons_map, LMonoTy.subst_tcons_map, deskolemizeTy_tcons]
    simp only [hfind, hmap]

/-! ### Deskolemization commutes with alias-argument substitution -/

/-- Deskolemization commutes with substituting alias arguments at a type variable. -/
private theorem deskolemizeTy_openVars_ftvar (σ : RigidNames) (vars : List TyIdentifier)
    (vals : LMonoTys) (x : TyIdentifier) :
    deskolemizeTy σ (LMonoTy.openVars vars vals (.ftvar x))
      = LMonoTy.openVars vars (vals.map (deskolemizeTy σ)) (.ftvar x) := by
  rw [LMonoTy.openVars_ftvar, LMonoTy.openVars_ftvar,
    List.find?_zip_map_right (deskolemizeTy σ) vars vals x]
  cases hfind : (List.zip vars vals).find? (fun p => p.1 == x) with
  | none => simp only [Option.map_none]; exact deskolemizeTy_ftvar σ x
  | some pr => obtain ⟨k, v⟩ := pr; simp

/-- On a body deskolemization fixes, deskolemization commutes with substituting for its type
    variables. -/
private theorem deskolemizeTy_openVars (σ : RigidNames) (vars : List TyIdentifier)
    (vals : LMonoTys) (t : LMonoTy) :
    deskolemizeTy σ t = t →
    deskolemizeTy σ (LMonoTy.openVars vars vals t)
      = LMonoTy.openVars vars (vals.map (deskolemizeTy σ)) t := by
  induction t with
  | ftvar x => intro _; exact deskolemizeTy_openVars_ftvar σ vars vals x
  | bitvec n =>
    intro _
    rw [LMonoTy.openVars_bitvec, LMonoTy.openVars_bitvec]
    rfl
  | tcons nm args ih =>
    intro ht
    obtain ⟨hfind, hargs⟩ := deskolemizeTy_tcons_fixed_inv ht
    have hmaps : (args.map (LMonoTy.openVars vars vals)).map (deskolemizeTy σ)
        = args.map (LMonoTy.openVars vars (vals.map (deskolemizeTy σ))) := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro b hb
      simp only [Function.comp_apply]
      exact ih b hb (hargs b hb)
    rw [LMonoTy.openVars_tcons, LMonoTy.openVars_tcons, LMonoTys.openVars_eq_map,
      LMonoTys.openVars_eq_map, deskolemizeTy_tcons, hfind, hmaps]

/-! ### Alias-equivalence survives deskolemization -/

mutual
/-- Deskolemization preserves alias-equivalence when it fixes every alias body and does not
    rewrite an alias name. -/
theorem AliasEquiv_deskolemizeTy {σ : RigidNames} {aliases : List TypeAlias}
    {m1 m2 : LMonoTy} (h : AliasEquiv aliases m1 m2)
    (h_ns : AliasesNoSkolem σ aliases) :
    AliasEquiv aliases (deskolemizeTy σ m1) (deskolemizeTy σ m2) := by
  match h with
  | .refl => exact .refl
  | @AliasEquiv.expand _ name args _ h_exp =>
    obtain ⟨al, h_mem, h_name, h_len, h_expand⟩ := h_exp
    subst h_expand
    subst h_name
    obtain ⟨h_body, h_head⟩ := h_ns al h_mem
    rw [h_head args]
    refine .expand ⟨al, h_mem, rfl, ?_, ?_⟩
    · rw [List.length_map]; exact h_len
    · simp only [TypeAlias.expand]
      exact deskolemizeTy_openVars σ al.typeArgs args al.type h_body
  | @AliasEquiv.collapse _ name args _ h_exp =>
    obtain ⟨al, h_mem, h_name, h_len, h_expand⟩ := h_exp
    subst h_expand
    subst h_name
    obtain ⟨h_body, h_head⟩ := h_ns al h_mem
    rw [h_head args]
    refine .collapse ⟨al, h_mem, rfl, ?_, ?_⟩
    · rw [List.length_map]; exact h_len
    · simp only [TypeAlias.expand]
      exact deskolemizeTy_openVars σ al.typeArgs args al.type h_body
  | @AliasEquiv.cong_tcons _ args args' name h_args =>
    rw [deskolemizeTy_tcons, deskolemizeTy_tcons]
    cases σ.find? (fun q => q.2 == name) with
    | some q => exact .refl
    | none => exact .cong_tcons (AliasEquivList_deskolemizeTy h_args h_ns)
  | .trans h1 h2 =>
    exact .trans (AliasEquiv_deskolemizeTy h1 h_ns) (AliasEquiv_deskolemizeTy h2 h_ns)

/-- Deskolemization preserves pointwise alias-equivalence of type lists when it fixes every alias
    body and does not rewrite an alias name. -/
private theorem AliasEquivList_deskolemizeTy {σ : RigidNames} {aliases : List TypeAlias}
    {as bs : LMonoTys} (h : AliasEquivList aliases as bs)
    (h_ns : AliasesNoSkolem σ aliases) :
    AliasEquivList aliases (as.map (deskolemizeTy σ)) (bs.map (deskolemizeTy σ)) := by
  match h with
  | .nil => exact .nil
  | .cons h_hd h_tl =>
    rw [List.map_cons, List.map_cons]
    exact .cons (AliasEquiv_deskolemizeTy h_hd h_ns) (AliasEquivList_deskolemizeTy h_tl h_ns)
end

/-! ### Source-type validity and registered types survive deskolemization -/

mutual
/-- Deskolemization preserves alias resolution when it fixes every alias body and does not
    rewrite an alias name. -/
private theorem SourceTyResolves_deskolemizeTy {σ : RigidNames} {aliases : List TypeAlias}
    (hns : AliasesNoSkolem σ aliases)
    {t r : LMonoTy} (h : SourceTyResolves aliases t r) :
    SourceTyResolves aliases (deskolemizeTy σ t) (deskolemizeTy σ r) := by
  match h with
  | .ftvar (v := v) =>
    rw [deskolemizeTy_ftvar]
    exact SourceTyResolves.ftvar
  | .bitvec (n := n) =>
    rw [deskolemizeTy_bitvec]
    exact SourceTyResolves.bitvec
  | .tcons (name := name) (args := args) (resolvedArgs := resolvedArgs) hargs hfind =>
    rw [deskolemizeTy_tcons, deskolemizeTy_tcons]
    cases σ.find? (fun p => p.2 == name) with
    | some p => exact SourceTyResolves.ftvar
    | none =>
      refine SourceTyResolves.tcons (SourceTysResolve_deskolemizeTy hns hargs) ?_
      rw [List.length_map]
      exact hfind
  | .alias (name := name) (args := args) (resolvedArgs := resolvedArgs) (alias := al)
      hargs hfind =>
    have hmem : al ∈ aliases := List.mem_of_find?_eq_some hfind
    have hsel := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at hsel
    obtain ⟨hbody, hhead⟩ := hns al hmem
    have hexpand : deskolemizeTy σ (al.expand resolvedArgs) =
        al.expand (resolvedArgs.map (deskolemizeTy σ)) := by
      simp only [TypeAlias.expand]
      exact deskolemizeTy_openVars σ al.typeArgs resolvedArgs al.type hbody
    rw [← hsel.1, hhead args, hexpand]
    refine SourceTyResolves.alias (SourceTysResolve_deskolemizeTy hns hargs) ?_
    rw [List.length_map, hsel.1]
    exact hfind

/-- Deskolemization preserves alias resolution of type lists when it fixes every alias body and
    does not rewrite an alias name. -/
private theorem SourceTysResolve_deskolemizeTy {σ : RigidNames} {aliases : List TypeAlias}
    (hns : AliasesNoSkolem σ aliases)
    {ts rs : LMonoTys} (h : SourceTysResolve aliases ts rs) :
    SourceTysResolve aliases (ts.map (deskolemizeTy σ)) (rs.map (deskolemizeTy σ)) := by
  match h with
  | .nil => exact SourceTysResolve.nil
  | .cons hhead htail =>
    exact SourceTysResolve.cons (SourceTyResolves_deskolemizeTy hns hhead)
      (SourceTysResolve_deskolemizeTy hns htail)
end

/-- Deskolemization commutes with alias resolution against a context whose alias bodies and heads
    it fixes. -/
theorem deskolemizeTy_resolveTy {σ : RigidNames} {Γ : TContext Unit}
    (hns : AliasesNoSkolem σ Γ.aliases)
    (t : LMonoTy) :
    deskolemizeTy σ (Γ.resolveTy t) = Γ.resolveTy (deskolemizeTy σ t) :=
  SourceTyResolves.unique
    (SourceTyResolves_deskolemizeTy hns
      (TContext.resolveTy_sourceTyResolves (T := CoreLParams) Γ t))
    (TContext.resolveTy_sourceTyResolves (T := CoreLParams) Γ (deskolemizeTy σ t))

mutual
/-- A resolved type valid in `Csk` stays valid after deskolemization in `Crig`, when `Crig`
    registers every non-rigid name `Csk` does and `adm'` admits every variable `adm` admits and
    every rigid parameter. -/
private theorem ResolvedTyWF_deskolemizeTy {T : LExprParams} {Csk Crig : LContext T}
    {σ : RigidNames} {adm adm' : TyVarAdmissibility}
    (hknown : KnownTypesTransfer σ Csk Crig)
    (hadm : ∀ v, adm v = true → adm' v = true) (hrig : ∀ p ∈ σ, adm' p.1 = true)
    {t : LMonoTy} (h : ResolvedTyWF Csk adm t) :
    ResolvedTyWF Crig adm' (deskolemizeTy σ t) := by
  match h with
  | .ftvar (v := v) hv =>
    rw [deskolemizeTy_ftvar]
    exact ResolvedTyWF.ftvar (hadm v hv)
  | .bitvec (n := n) =>
    rw [deskolemizeTy_bitvec]
    exact ResolvedTyWF.bitvec
  | .tcons (name := name) (args := args) hk hargs =>
    rw [deskolemizeTy_tcons]
    cases hfind : σ.find? (fun p => p.2 == name) with
    | some p => exact ResolvedTyWF.ftvar (hrig p (List.mem_of_find?_eq_some hfind))
    | none =>
      refine ResolvedTyWF.tcons ?_ (ResolvedTysWF_deskolemizeTy hknown hadm hrig hargs)
      rw [List.length_map]
      exact hknown name args.length hfind hk

/-- Resolved types valid in `Csk` stay valid after deskolemization in `Crig`, when `Crig`
    registers every non-rigid name `Csk` does and `adm'` admits every variable `adm` admits and
    every rigid parameter. -/
private theorem ResolvedTysWF_deskolemizeTy {T : LExprParams} {Csk Crig : LContext T}
    {σ : RigidNames} {adm adm' : TyVarAdmissibility}
    (hknown : KnownTypesTransfer σ Csk Crig)
    (hadm : ∀ v, adm v = true → adm' v = true) (hrig : ∀ p ∈ σ, adm' p.1 = true)
    {ts : LMonoTys} (h : ResolvedTysWF Csk adm ts) :
    ResolvedTysWF Crig adm' (ts.map (deskolemizeTy σ)) := by
  match h with
  | .nil => exact ResolvedTysWF.nil
  | .cons hhead htail =>
    exact ResolvedTysWF.cons (ResolvedTyWF_deskolemizeTy hknown hadm hrig hhead)
      (ResolvedTysWF_deskolemizeTy hknown hadm hrig htail)
end

/-- A source type valid in `Csk` stays valid with its resolution after deskolemization in `Crig`,
    when `Crig` registers every non-rigid name `Csk` does, `adm'` admits every variable `adm`
    admits and every rigid parameter, and deskolemization fixes each alias body and name. -/
theorem SourceTyWF_deskolemizeTy {T : LExprParams} {Csk Crig : LContext T}
    {σ : RigidNames} {adm adm' : TyVarAdmissibility} {aliases : List TypeAlias}
    (hknown : KnownTypesTransfer σ Csk Crig)
    (hadm : ∀ v, adm v = true → adm' v = true) (hrig : ∀ p ∈ σ, adm' p.1 = true)
    (hns : AliasesNoSkolem σ aliases)
    {t r : LMonoTy} (h : SourceTyWF Csk adm aliases t r) :
    SourceTyWF Crig adm' aliases (deskolemizeTy σ t) (deskolemizeTy σ r) := by
  obtain ⟨hres, htype⟩ := h
  exact ⟨SourceTyResolves_deskolemizeTy hns hres,
    ResolvedTyWF_deskolemizeTy hknown hadm hrig htype⟩

/-- If `Csk`'s registered types are those of `Crig` plus the rigid constants, `Crig` registers
    every non-rigid name `Csk` does, at the same arity. -/
theorem knownTypes_contains_of_getElem?_addSkolemTypes {Csk Crig : Expression.TyContext}
    {σ : RigidNames}
    (h_known : ∀ x : String, Csk.knownTypes[x]? = (addSkolemTypes Crig σ).knownTypes[x]?) :
    KnownTypesTransfer σ Csk Crig := by
  intro name n hfind h
  simp only [KnownTypes.contains, Identifiers.contains] at h ⊢
  rwa [h_known, addSkolemTypes_getElem?_of_find?_none Crig σ name hfind] at h

/-- A written annotation naming no constant of `σ` is a valid source type when its skolemized
    form is valid in the context extended with the rigid constants. -/
private theorem SourceTyWF_of_skolemizeTy
    (C : Expression.TyContext) (Γ : TContext Unit)
    (σ : RigidNames) (h_nd : (σ.map Prod.snd).Nodup)
    (h_aliases : AliasesNoSkolem σ Γ.aliases)
    {adm : TyVarAdmissibility} (h_rig : ∀ p ∈ σ, adm p.1 = true) {t r : LMonoTy}
    (h_allowed : mtyAllTyConsNames (notRigidConst σ) t = true)
    (hr : SourceTyWF (addSkolemTypes C σ) adm Γ.aliases (skolemizeTy σ t) r) :
    ∃ r', SourceTyWF C adm Γ.aliases t r' := by
  have hround : deskolemizeTy σ (skolemizeTy σ t) = t := by
    rw [deskolemizeTy_skolemizeTy_eq_deskolemizeTy h_nd,
      deskolemizeTy_eq_self_of_notRigidConst t h_allowed]
  have hdesk := SourceTyWF_deskolemizeTy (Csk := addSkolemTypes C σ) (Crig := C)
    (knownTypes_contains_of_getElem?_addSkolemTypes (fun _ => rfl)) (fun _ hv => hv)
    h_rig h_aliases hr
  rw [hround] at hdesk
  exact ⟨_, hdesk⟩

/-- Deskolemizing a type registered in `Csk` gives one registered in `Crig`, when `Crig`
    registers every non-rigid name `Csk` does. -/
private theorem knownInstance_deskolemizeTy {Csk Crig : Expression.TyContext} {σ : RigidNames}
    (hknown : KnownTypesTransfer σ Csk Crig)
    {t : LMonoTy} (h : t.knownInstance Csk.knownTypes = true) :
    (deskolemizeTy σ t).knownInstance Crig.knownTypes = true := by
  exact (ResolvedTyWF_deskolemizeTy hknown (fun _ hv => hv) (fun _ _ => rfl)
    (ResolvedTyWF.of_knownInstance h)).knownInstance

/-- If an expression's binder annotations are registered in `Csk`, after deskolemization they are
    registered in any `Crig` that registers every non-rigid name `Csk` does. -/
theorem binderAnnotations_known_deskolemize {Csk Crig : Expression.TyContext} {σ : RigidNames}
    (hknown : KnownTypesTransfer σ Csk Crig)
    (e : Expression.Expr)
    (h : ∀ t ∈ LExpr.binderAnnotations e, t.knownInstance Csk.knownTypes = true) :
    ∀ t ∈ LExpr.binderAnnotations (LExpr.replaceUserProvidedType e (deskolemizeTy σ)),
      t.knownInstance Crig.knownTypes = true := by
  intro t ht
  rw [binderAnnotations_replaceUserProvidedType] at ht
  obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
  exact knownInstance_deskolemizeTy hknown (h t0 ht0)

/-- No alias names a registered type after adding a renaming's constants, if none did before and
    deskolemization does not rewrite an alias name. -/
theorem aliasNames_unregistered_addSkolemTypes {C : Expression.TyContext} {σ : RigidNames}
    {aliases : List TypeAlias}
    (hns : AliasesNoSkolem σ aliases)
    (hfresh : ∀ al ∈ aliases, C.knownTypes.containsName al.name = false) :
    ∀ al ∈ aliases, (addSkolemTypes C σ).knownTypes.containsName al.name = false := by
  intro al hal
  have hfind : σ.find? (fun p => p.2 == al.name) = none := by
    have hhead := (hns al hal).2 []
    rw [deskolemizeTy_tcons] at hhead
    cases hf : σ.find? (fun p => p.2 == al.name) with
    | none => rfl
    | some p =>
      rw [hf] at hhead
      exact absurd hhead (by simp)
  have hC := hfresh al hal
  simp only [KnownTypes.containsName, Std.HashMap.contains_eq_isSome_getElem?] at hC ⊢
  rw [addSkolemTypes_getElem?_of_find?_none C σ al.name hfind]
  exact hC

/-- A binder annotation valid in `Csk` with every type variable allowed stays valid after
    deskolemization in `Crig`, when `Crig` registers every non-rigid name `Csk` does and
    deskolemization fixes every alias body and name. -/
private theorem binderAnnot_sourceTyWF_deskolemizeTy {T : LExprParams} {Csk Crig : LContext T}
    {σ : RigidNames} {aliases aliases' : List TypeAlias}
    (hknown : KnownTypesTransfer σ Csk Crig)
    (halias : aliases' = aliases)
    (hns : AliasesNoSkolem σ aliases)
    {o : Option LMonoTy}
    (h : ∀ t, o = some t → ∃ r, SourceTyWF Csk TyVarAdmissibility.all aliases t r) :
    ∀ t, o.map (deskolemizeTy σ) = some t →
      ∃ r, SourceTyWF Crig TyVarAdmissibility.all aliases' t r := by
  intro t ht
  cases o with
  | none => exact absurd ht (by simp)
  | some t0 =>
    simp only [Option.map_some, Option.some.injEq] at ht
    subst ht
    subst halias
    obtain ⟨r, hr⟩ := h t0 rfl
    exact ⟨_, SourceTyWF_deskolemizeTy hknown (fun _ hv => hv) (fun _ _ => rfl) hns hr⟩

/-! ### Transporting an annotation's compatibility across deskolemization -/

/-- `annotNoRigidClashIn` passes from a type-constructor application to its arguments. -/
private theorem annotNoRigidClashIn_of_mem_args {σ : RigidNames} {l : List TyIdentifier}
    {nm : String} {args : LMonoTys} (h : annotNoRigidClashIn σ l (.tcons nm args) = true) :
    ∀ t ∈ args, annotNoRigidClashIn σ l t = true := by
  simp only [annotNoRigidClashIn, mtyAllTyConsNames_tcons, Bool.and_eq_true] at h
  exact mtyAllTyConsNames_of_mem _ args h.2

/-- If a rigid constant heads a type passing `annotNoRigidClashIn σ l`, its parameter is not in
    `l`. -/
private theorem not_mem_of_annotNoRigidClashIn {σ : RigidNames} {l : List TyIdentifier}
    {nm : String} {args : LMonoTys} {q : String × String}
    (h : annotNoRigidClashIn σ l (.tcons nm args) = true)
    (hq : q ∈ σ) (hnm : (q.2 == nm) = true) :
    q.1 ∉ l := by
  simp only [annotNoRigidClashIn, mtyAllTyConsNames_tcons, Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.1 q hq
  rw [hnm] at hall
  simp only [Bool.not_true, Bool.false_or, Bool.not_eq_eq_eq_not] at hall
  intro hm
  rw [List.contains_iff_mem.mpr hm] at hall
  exact Bool.noConfusion hall

/-- Deskolemizing after substituting by `ρ` then `S` is substituting the deskolemized images on
    `l` after deskolemizing, for a type whose free variables lie in `l` and with no rigid head
    whose parameter is in `l`. -/
private theorem subst_buildSubstFromFunction_deskolemizeTy_gen (σ : RigidNames) (S : Subst)
    (ρ : SubstOne)
    (l : List TyIdentifier) (mty : LMonoTy)
    (h_clash : annotNoRigidClashIn σ l mty = true)
    (h_sub : ∀ v ∈ LMonoTy.freeVars mty, v ∈ l) :
    LMonoTy.subst [LExpr.buildSubstFromFunction l
        (fun v => deskolemizeTy σ (LMonoTy.subst S (LMonoTy.subst [ρ] (.ftvar v))))]
        (deskolemizeTy σ mty)
      = deskolemizeTy σ (LMonoTy.subst S (LMonoTy.subst [ρ] mty)) := by
  induction mty with
  | ftvar x =>
    have hx : x ∈ l := h_sub x (by simp [LMonoTy.freeVars])
    have hfind : HMaps.find? [LExpr.buildSubstFromFunction l
        (fun v => deskolemizeTy σ (LMonoTy.subst S (LMonoTy.subst [ρ] (.ftvar v))))] x
        = some (deskolemizeTy σ (LMonoTy.subst S (LMonoTy.subst [ρ] (.ftvar x)))) := by
      rw [HMaps.find?_single_scope]
      exact LExpr.find?_buildSubstFromFunction l _ x hx
    rw [deskolemizeTy_ftvar, LMonoTy.subst_unfold]
    simp only [hfind]
  | bitvec n =>
    rw [show deskolemizeTy σ (LMonoTy.bitvec n) = LMonoTy.bitvec n from rfl,
      LMonoTy.subst_bitvec, LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
    rfl
  | tcons nm args ih =>
    rw [deskolemizeTy_tcons]
    cases hfind : σ.find? (fun q => q.2 == nm) with
    | some q =>
      have hq : q ∈ σ := List.mem_of_find?_eq_some hfind
      have hnm : (q.2 == nm) = true := by simpa using List.find?_some hfind
      have hnl : q.1 ∉ l := not_mem_of_annotNoRigidClashIn h_clash hq hnm
      have hnone : HMaps.find? [LExpr.buildSubstFromFunction l
          (fun v => deskolemizeTy σ (LMonoTy.subst S (LMonoTy.subst [ρ] (.ftvar v))))] q.1
          = none := by
        rw [HMaps.find?_single_scope]
        exact LExpr.find?_buildSubstFromFunction_of_not_mem l _ q.1 hnl
      rw [LMonoTy.subst_unfold]
      simp only [hnone]
      rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, deskolemizeTy_tcons]
      simp only [hfind]
    | none =>
      rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTy.subst_tcons,
        LMonoTys.subst_eq_map, LMonoTy.subst_tcons, LMonoTys.subst_eq_map,
        deskolemizeTy_tcons]
      simp only [hfind, List.map_map]
      refine congrArg (LMonoTy.tcons nm) (List.map_congr_left ?_)
      intro t ht
      have ht_freeVars : ∀ v, v ∈ t.freeVars → v ∈ (LMonoTy.tcons nm args).freeVars := by
        intro v hv
        simp only [LMonoTy.freeVars]
        exact LMonoTys.freeVars_mem_subset ht hv
      exact ih t ht (annotNoRigidClashIn_of_mem_args h_clash t ht)
        (fun v hv => h_sub v (ht_freeVars v hv))

/-- Deskolemizing after substituting by `ρ` is substituting the deskolemized `ρ`-images on `l`
    after deskolemizing, for a type whose free variables lie in `l`, when `ρ` fixes every renamed
    parameter. -/
theorem subst_deskolInst_comm_of_fix (σ : RigidNames) (ρ : SubstOne) (l : List TyIdentifier)
    (hfix : ∀ q ∈ σ, LMonoTy.subst [ρ] (.ftvar q.1) = .ftvar q.1) (mty : LMonoTy)
    (h_sub : ∀ v ∈ LMonoTy.freeVars mty, v ∈ l) :
    LMonoTy.subst [LExpr.buildSubstFromFunction l
        (fun v => deskolemizeTy σ (LMonoTy.subst [ρ] (.ftvar v)))] (deskolemizeTy σ mty)
      = deskolemizeTy σ (LMonoTy.subst [ρ] mty) := by
  induction mty with
  | ftvar x =>
    have hx : x ∈ l := h_sub x (by simp [LMonoTy.freeVars])
    rw [deskolemizeTy_ftvar]
    apply LMonoTy.subst_ftvar_of_some
    rw [HMaps.find?_single_scope]
    exact LExpr.find?_buildSubstFromFunction l _ x hx
  | bitvec n =>
    rw [show deskolemizeTy σ (LMonoTy.bitvec n) = LMonoTy.bitvec n from rfl,
      LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
    rfl
  | tcons nm args ih =>
    rw [deskolemizeTy_tcons]
    cases hfind : σ.find? (fun q => q.2 == nm) with
    | some q =>
      have hq : q ∈ σ := List.mem_of_find?_eq_some hfind
      have hlhs : LMonoTy.subst [LExpr.buildSubstFromFunction l
          (fun v => deskolemizeTy σ (LMonoTy.subst [ρ] (.ftvar v)))] (.ftvar q.1)
          = .ftvar q.1 := by
        by_cases hql : q.1 ∈ l
        · have hsome : HMaps.find? [LExpr.buildSubstFromFunction l
              (fun v => deskolemizeTy σ (LMonoTy.subst [ρ] (.ftvar v)))] q.1
              = some (deskolemizeTy σ (LMonoTy.subst [ρ] (.ftvar q.1))) := by
            rw [HMaps.find?_single_scope]
            exact LExpr.find?_buildSubstFromFunction l _ q.1 hql
          rw [LMonoTy.subst_ftvar_of_some hsome, hfix q hq, deskolemizeTy_ftvar]
        · apply LMonoTy.subst_ftvar_of_none
          rw [HMaps.find?_single_scope]
          exact LExpr.find?_buildSubstFromFunction_of_not_mem l _ q.1 hql
      simp only
      rw [hlhs, LMonoTy.subst_tcons, deskolemizeTy_tcons]
      simp only [hfind]
    | none =>
      rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTy.subst_tcons,
        LMonoTys.subst_eq_map, deskolemizeTy_tcons]
      simp only [hfind, List.map_map]
      refine congrArg (LMonoTy.tcons nm) (List.map_congr_left ?_)
      intro t ht
      have ht_freeVars : ∀ v, v ∈ t.freeVars → v ∈ (LMonoTy.tcons nm args).freeVars := by
        intro v hv
        simp only [LMonoTy.freeVars]
        exact LMonoTys.freeVars_mem_subset ht hv
      exact ih t ht (fun v hv => h_sub v (ht_freeVars v hv))

/-! #### Discharging the annotation condition -/

/-- When `l` contains no rigid parameter name, every type passes `annotNoRigidClashIn σ l`. -/
private theorem annotNoRigidClashIn_of_not_mem (σ : RigidNames) (l : List TyIdentifier)
    (mty : LMonoTy)
    (h : ∀ v ∈ l, v ∉ σ.map Prod.fst) :
    annotNoRigidClashIn σ l mty = true := by
  refine mtyAllTyConsNames_of_forall _ mty ?_
  intro nm
  refine List.all_eq_true.mpr ?_
  intro q hq
  have hnc : l.contains q.1 = false := by
    by_cases hm : q.1 ∈ l
    · exact absurd (List.mem_map.mpr ⟨q, hq, rfl⟩) (h q.1 hm)
    · simp only [List.contains_eq_mem, decide_eq_false_iff_not]
      exact hm
  simp only [hnc, Bool.not_false, Bool.or_true]

/-- An annotation with no rigid parameter name among its free variables satisfies
    `annotNoRigidClash`. -/
theorem annotNoRigidClash_of_freeVars_not_mem (σ : RigidNames) (mty : LMonoTy)
    (h : ∀ v ∈ LMonoTy.freeVars mty, v ∉ σ.map Prod.fst) :
    annotNoRigidClash σ mty = true :=
  annotNoRigidClashIn_of_not_mem σ (LMonoTy.freeVars mty) mty h

/-- An annotation naming no constant of `σ` satisfies `annotNoRigidClash`. -/
theorem annotNoRigidClash_of_notRigidConst {σ : RigidNames}
    (mty : LMonoTy) (h : mtyAllTyConsNames (notRigidConst σ) mty = true) :
    annotNoRigidClash σ mty = true := by
  refine mtyAllTyConsNames_mono ?_ mty h
  intro nm hnm
  refine List.all_eq_true.mpr ?_
  intro q hq
  have hne : (q.2 == nm) = false := by
    have hq' := List.all_eq_true.mp hnm q hq
    simpa only [bne_iff_ne, ne_eq, beq_eq_false_iff_ne] using hq'
  simp only [hne, Bool.not_false, Bool.true_or]

/-- Deskolemization transports an annotation's compatibility with a type to any substitution
    instance of the type, when the aliases are well formed and fixed by deskolemization and the
    annotation satisfies `annotNoRigidClash`. -/
private theorem annotCompat_transport_gen (σ : RigidNames) (aliases : List TypeAlias)
    (ann ty_s : LMonoTy) (S : Subst)
    (h : LExpr.AnnotCompat aliases ann ty_s)
    (h_aw : ∀ al ∈ aliases, TypeAlias.WF al)
    (h_alias : AliasesNoSkolem σ aliases)
    (h_ann : annotNoRigidClash σ ann = true) :
    LExpr.AnnotCompat aliases (deskolemizeTy σ ann)
      (deskolemizeTy σ (LMonoTy.subst S ty_s)) := by
  obtain ⟨ρ, h_ae⟩ := h
  have h_ae_S := LExpr.AliasEquiv_subst aliases (LMonoTy.subst [ρ] ann) ty_s S h_ae h_aw
  have h_ae_D := AliasEquiv_deskolemizeTy h_ae_S h_alias
  refine ⟨LExpr.buildSubstFromFunction (LMonoTy.freeVars ann)
    (fun v => deskolemizeTy σ (LMonoTy.subst S (LMonoTy.subst [ρ] (.ftvar v)))), ?_⟩
  rw [subst_buildSubstFromFunction_deskolemizeTy_gen σ S ρ (LMonoTy.freeVars ann) ann h_ann
    (fun v hv => hv)]
  exact h_ae_D

/-! ### Annotation conditions skolemized types satisfy -/

/-- No free type variable of a skolemized type is a rigid parameter name. -/
private theorem freeVars_skolemizeTy_not_mem (σ : RigidNames) (mty : LMonoTy) :
    ∀ v ∈ LMonoTy.freeVars (skolemizeTy σ mty), v ∉ σ.map Prod.fst := by
  induction mty with
  | ftvar x =>
    rw [skolemizeTy_ftvar]
    cases hfind : σ.find? (fun q => q.1 == x) with
    | some q =>
      intro v hv
      simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv
    | none =>
      intro v hv
      have hvx : v = x := by simpa [LMonoTy.freeVars] using hv
      rw [hvx]
      intro hmem
      obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hmem
      rw [List.find?_eq_none] at hfind
      exact absurd (by simpa using hqx) (by simpa using hfind q hq)
  | bitvec n =>
    rw [skolemizeTy_bitvec]
    intro v hv
    simp [LMonoTy.freeVars] at hv
  | tcons nm args ih =>
    rw [skolemizeTy_tcons]
    intro v hv
    simp only [LMonoTy.freeVars] at hv
    obtain ⟨t, ht, hvt⟩ := LMonoTys.freeVars_exists hv
    obtain ⟨t0, ht0, ht0eq⟩ := List.mem_map.mp ht
    exact ih t0 ht0 v (ht0eq ▸ hvt)

/-- A type skolemized by `σ` satisfies `annotNoRigidClash σ`: none of its free type variables is
    a parameter `σ` renames. -/
theorem annotNoRigidClash_skolemizeTy (σ : RigidNames) (mty : LMonoTy) :
    annotNoRigidClash σ (skolemizeTy σ mty) = true :=
  annotNoRigidClash_of_freeVars_not_mem σ (skolemizeTy σ mty) (freeVars_skolemizeTy_not_mem σ mty)

/-! ### Annotation sweeps, and type variables deskolemization keeps -/

/-- `allExprTys` and `LExpr.allUserProvidedTypes` check the same annotations. -/
theorem allExprTys_eq_allUserProvidedTypes (p : LMonoTy → Bool) (e : Expression.Expr) :
    allExprTys p e = LExpr.allUserProvidedTypes e p :=
  rfl

/-- A type `deskolKeeps` accepts keeps each of its type variables under deskolemization. -/
theorem mem_freeVars_deskolemizeTy_of_deskolKeeps {σ : RigidNames} {t : LMonoTy}
    (h : deskolKeeps σ t = true) :
    ∀ v ∈ LMonoTy.freeVars t, v ∈ LMonoTy.freeVars (deskolemizeTy σ t) := by
  intro v hv
  simp only [deskolKeeps, List.all_eq_true, List.contains_iff_mem] at h
  exact h v hv

/-- Skolemizing a type only removes type variables. -/
private theorem freeVars_skolemizeTy_subset (σ : RigidNames) :
    ∀ (t : LMonoTy), ∀ v ∈ LMonoTy.freeVars (skolemizeTy σ t), v ∈ LMonoTy.freeVars t := by
  intro t
  induction t with
  | ftvar x =>
    intro v hv
    rw [skolemizeTy_ftvar] at hv
    cases hfind : σ.find? (fun p => p.1 == x) with
    | some p => simp only [hfind, LMonoTy.freeVars, LMonoTys.freeVars, List.not_mem_nil] at hv
    | none => simpa only [hfind] using hv
  | bitvec n =>
    intro v hv
    rw [skolemizeTy_bitvec] at hv
    exact hv
  | tcons nm args ih =>
    intro v hv
    rw [skolemizeTy_tcons] at hv
    simp only [LMonoTy.freeVars] at hv ⊢
    obtain ⟨a, ha, hva⟩ := LMonoTys.freeVars_exists hv
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    exact LMonoTys.freeVars_mem_subset ha₀ (ih a₀ ha₀ v hva)

/-- A type naming no constant of `σ`, skolemized by a sub-renaming of `σ`, keeps its type
    variables under deskolemization by `σ`. -/
theorem deskolKeeps_skolemizeTy_of_sublist {inner σ : RigidNames} (hsub : inner.Sublist σ)
    (hnd : (σ.map Prod.snd).Nodup) (t : LMonoTy)
    (h : mtyAllTyConsNames (notRigidConst σ) t = true) :
    deskolKeeps σ (skolemizeTy inner t) = true := by
  simp only [deskolKeeps, List.all_eq_true, List.contains_iff_mem]
  intro v hv
  rw [deskolemizeTy_skolemizeTy_eq_deskolemizeTy_of_sublist hsub hnd t,
    deskolemizeTy_eq_self_of_notRigidConst t h]
  exact freeVars_skolemizeTy_subset inner t v hv

/-- A type naming no constant of `σ` keeps its type variables under deskolemization by `σ`. -/
theorem deskolKeeps_of_notRigidConst {σ : RigidNames} (t : LMonoTy)
    (h : mtyAllTyConsNames (notRigidConst σ) t = true) : deskolKeeps σ t = true := by
  simp only [deskolKeeps, List.all_eq_true, List.contains_iff_mem]
  intro v hv
  rw [deskolemizeTy_eq_self_of_notRigidConst t h]
  exact hv

/-! ### Reading a condition on annotations off a compound expression -/

/-- If the `annotNoRigidClash` sweep accepts an abstraction, its bound-variable annotation
    satisfies `annotNoRigidClash`. -/
private theorem annotNoRigidClash_of_abs (σ : RigidNames) (m : ExpressionMetadata) (name : String)
    (ann : LMonoTy)
    (e : Expression.Expr)
    (h : allExprTys (annotNoRigidClash σ) (.abs m name (some ann) e) = true) :
    annotNoRigidClash σ ann = true := by
  simp only [allExprTys_eq_allUserProvidedTypes, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    at h
  exact h.1

/-- If the `annotNoRigidClash` sweep accepts a quantifier, its bound-variable annotation
    satisfies `annotNoRigidClash`. -/
private theorem annotNoRigidClash_of_quant (σ : RigidNames) (m : ExpressionMetadata)
    (qk : QuantifierKind)
    (name : String) (ann : LMonoTy) (tr e : Expression.Expr)
    (h : allExprTys (annotNoRigidClash σ) (.quant m qk name (some ann) tr e) = true) :
    annotNoRigidClash σ ann = true := by
  simp only [allExprTys_eq_allUserProvidedTypes, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    at h
  exact h.1.1

/-- A sweep over the annotations of an abstraction passes to its body. -/
private theorem allExprTys_abs {p : LMonoTy → Bool} {m : ExpressionMetadata} {name : String}
    {o : Option LMonoTy}
    {e : Expression.Expr} (h : allExprTys p (.abs m name o e) = true) :
    allExprTys p e = true := by
  simp only [allExprTys_eq_allUserProvidedTypes, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    at h ⊢
  exact h.2

/-- A sweep over the annotations of a quantifier passes to its trigger and its body. -/
private theorem allExprTys_quant {p : LMonoTy → Bool} {m : ExpressionMetadata} {qk : QuantifierKind}
    {name : String}
    {o : Option LMonoTy} {tr e : Expression.Expr}
    (h : allExprTys p (.quant m qk name o tr e) = true) :
    allExprTys p tr = true ∧ allExprTys p e = true := by
  simp only [allExprTys_eq_allUserProvidedTypes, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    at h ⊢
  exact ⟨h.1.2, h.2⟩

/-- A sweep over the annotations of an application passes to both operands. -/
private theorem allExprTys_app {p : LMonoTy → Bool} {m : ExpressionMetadata}
    {e1 e2 : Expression.Expr}
    (h : allExprTys p (.app m e1 e2) = true) :
    allExprTys p e1 = true ∧ allExprTys p e2 = true := by
  simp only [allExprTys_eq_allUserProvidedTypes, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    at h ⊢
  exact h

/-- A sweep over the annotations of an equality passes to both operands. -/
private theorem allExprTys_eq {p : LMonoTy → Bool} {m : ExpressionMetadata}
    {e1 e2 : Expression.Expr}
    (h : allExprTys p (.eq m e1 e2) = true) :
    allExprTys p e1 = true ∧ allExprTys p e2 = true := by
  simp only [allExprTys_eq_allUserProvidedTypes, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    at h ⊢
  exact h

/-- A sweep over the annotations of a conditional passes to all three branches. -/
private theorem allExprTys_ite {p : LMonoTy → Bool} {m : ExpressionMetadata}
    {c e1 e2 : Expression.Expr}
    (h : allExprTys p (.ite m c e1 e2) = true) :
    allExprTys p c = true ∧ allExprTys p e1 = true ∧ allExprTys p e2 = true := by
  simp only [allExprTys_eq_allUserProvidedTypes, LExpr.allUserProvidedTypes, Bool.and_eq_true]
    at h ⊢
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! #### Opening a bound variable injects the opened variable's own annotation -/

/-- `mapExprTys` commutes with opening a bound variable, when also applied to the opened
    variable's annotation. -/
private theorem mapExprTys_varOpen (f : LMonoTy → LMonoTy) (k : Nat)
    (x : CoreIdent × Option LMonoTy) (e : Expression.Expr) :
    mapExprTys f (LExpr.varOpen k x e)
      = LExpr.varOpen k (x.1, x.2.map f) (mapExprTys f e) := by
  simp only [mapExprTys]
  exact LExpr.replaceUserProvidedType_varOpen f k x e

/-- Opening a bound variable preserves an annotation sweep that accepts the opened variable's
    annotation. -/
private theorem allExprTys_varOpen {p : LMonoTy → Bool} {k : Nat} {x : CoreIdent × Option LMonoTy}
    {e : Expression.Expr} (he : allExprTys p e = true) (hx : x.2.all p = true) :
    allExprTys p (LExpr.varOpen k x e) = true := by
  rw [allExprTys_eq_allUserProvidedTypes] at he ⊢
  induction e generalizing k with
  | const m c => rfl
  | op m o uty => exact he
  | bvar m i =>
    show LExpr.allUserProvidedTypes
        (if i == k then (LExpr.fvar m x.1 x.2 : Expression.Expr) else .bvar m i) p = true
    by_cases hik : (i == k) = true
    · simp only [hik, ite_true]
      exact hx
    · simp only [hik, Bool.false_eq_true, ite_false]
      rfl
  | fvar m y uty => exact he
  | abs m name uty e' ih =>
    show (uty.all p && LExpr.allUserProvidedTypes (LExpr.varOpen (k + 1) x e') p) = true
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at he
    simp only [Bool.and_eq_true]
    exact ⟨he.1, ih he.2⟩
  | quant m qk name uty tr e' ihtr ih =>
    show (uty.all p && LExpr.allUserProvidedTypes (LExpr.varOpen (k + 1) x tr) p
      && LExpr.allUserProvidedTypes (LExpr.varOpen (k + 1) x e') p) = true
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at he
    simp only [Bool.and_eq_true]
    exact ⟨⟨he.1.1, ihtr he.1.2⟩, ih he.2⟩
  | app m e1 e2 ih1 ih2 =>
    show (LExpr.allUserProvidedTypes (LExpr.varOpen k x e1) p
      && LExpr.allUserProvidedTypes (LExpr.varOpen k x e2) p) = true
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at he
    simp only [Bool.and_eq_true]
    exact ⟨ih1 he.1, ih2 he.2⟩
  | ite m c t e' ihc iht ih =>
    show (LExpr.allUserProvidedTypes (LExpr.varOpen k x c) p
      && LExpr.allUserProvidedTypes (LExpr.varOpen k x t) p
      && LExpr.allUserProvidedTypes (LExpr.varOpen k x e') p) = true
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at he
    simp only [Bool.and_eq_true]
    exact ⟨⟨ihc he.1.1, iht he.1.2⟩, ih he.2⟩
  | eq m e1 e2 ih1 ih2 =>
    show (LExpr.allUserProvidedTypes (LExpr.varOpen k x e1) p
      && LExpr.allUserProvidedTypes (LExpr.varOpen k x e2) p) = true
    simp only [LExpr.allUserProvidedTypes, Bool.and_eq_true] at he
    simp only [Bool.and_eq_true]
    exact ⟨ih1 he.1, ih2 he.2⟩

/-! ### What an unannotated operator occurrence transfers to -/

/-- Two factories related by deskolemization of their signatures contain the same names. -/
theorem FactorySigDeskolemizes.mem_iff {σ : RigidNames}
    {Fsk Frig : Lambda.Factory CoreLParams} (h : FactorySigDeskolemizes σ Fsk Frig)
    (nm : String) : nm ∈ Fsk ↔ nm ∈ Frig := by
  rw [Factory.mem_iff_getElem?_isSome, Factory.mem_iff_getElem?_isSome, (h nm).1]

/-- A source signature has its deskolemized counterpart in a related target factory. -/
theorem FactorySigDeskolemizes.find_type {σ : RigidNames}
    {Fsk Frig : Lambda.Factory CoreLParams} (h : FactorySigDeskolemizes σ Fsk Frig)
    (nm : String) (f : LFunc CoreLParams) (ty : LTy)
    (hf : Fsk[nm]? = some f) (hty : f.type = .ok ty) :
    ∃ f', Frig[nm]? = some f' ∧
      f'.type = .ok (mapLTyTys (deskolemizeTy σ) ty) :=
  (h nm).2 f ty hf hty

/-- Deskolemization relates a factory to itself when it fixes every signature. -/
theorem FactorySigDeskolemizes.refl_of_fixed (σ : RigidNames)
    (F : Lambda.Factory CoreLParams)
    (hfix : ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
      F[nm]? = some f → f.type = .ok ty →
        mapLTyTys (deskolemizeTy σ) ty = ty) :
    FactorySigDeskolemizes σ F F := by
  intro nm
  refine ⟨rfl, fun f ty hf hty => ⟨f, hf, ?_⟩⟩
  rw [hfix nm f ty hf hty]
  exact hty

/-- A factory whose signatures deskolemization fixes is safe to deskolemize. -/
theorem FactorySigDeskolSafe.of_fixed (σ : RigidNames) (F : Lambda.Factory CoreLParams)
    (hfix : ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
      F[nm]? = some f → f.type = .ok ty →
        mapLTyTys (deskolemizeTy σ) ty = ty) :
    FactorySigDeskolSafe σ F :=
  fun nm f ty hf hty => Or.inl (hfix nm f ty hf hty)

/-- Deskolemizing an instance of a monotype in which no rigid parameter name is free gives an
    instance of its deskolemization by a substitution that changes only type variables free in
    the monotype. -/
theorem deskolemizeTy_subst_instance_fixing (σ : RigidNames) (τ : Subst) (mty : LMonoTy)
    (hfree : ∀ v ∈ LMonoTy.freeVars mty, v ∉ σ.map Prod.fst) :
    ∃ τ' : Subst,
      (∀ v, v ∉ LMonoTy.freeVars mty → LMonoTy.subst τ' (.ftvar v) = .ftvar v) ∧
      deskolemizeTy σ (LMonoTy.subst τ mty) = LMonoTy.subst τ' (deskolemizeTy σ mty) := by
  have hgen := subst_buildSubstFromFunction_deskolemizeTy_gen σ τ HMap.empty
    (LMonoTy.freeVars mty) mty (annotNoRigidClash_of_freeVars_not_mem σ mty hfree)
    (fun _ hv => hv)
  have hemp : Subst.hasEmptyScopes [(HMap.empty : SubstOne)] = true := by
    simp [Subst.hasEmptyScopes, HMap.isEmpty, HMap.empty]
  have hρ : ∀ t, LMonoTy.subst [(HMap.empty : SubstOne)] t = t :=
    LMonoTy.subst_of_hasEmptyScopes hemp
  simp only [hρ] at hgen
  refine ⟨_, fun v hv => ?_, hgen.symm⟩
  apply LMonoTy.subst_ftvar_of_none
  rw [Strata.Util.HMaps.find?_single_scope]
  exact LExpr.find?_buildSubstFromFunction_of_not_mem _ _ v hv

/-- Deskolemizing an instance of a monotype gives an instance of its deskolemization, when
    deskolemization fixes the monotype or no rigid parameter name is free in it. -/
theorem deskolemizeTy_subst_instance (σ : RigidNames) (τ : Subst) (mty : LMonoTy)
    (hsafe : deskolemizeTy σ mty = mty ∨ ∀ v ∈ LMonoTy.freeVars mty, v ∉ σ.map Prod.fst) :
    ∃ τ' : Subst,
      deskolemizeTy σ (LMonoTy.subst τ mty) = LMonoTy.subst τ' (deskolemizeTy σ mty) := by
  rcases hsafe with hfix | hfree
  · refine ⟨[LExpr.buildSubstFromFunction (LMonoTy.freeVars mty)
      (fun v => deskolemizeTy σ (LMonoTy.subst τ (.ftvar v)))], ?_⟩
    rw [hfix]
    refine deskolemizeTy_subst_eq_subst σ τ _ mty hfix (fun x hx => ?_)
    symm
    apply LMonoTy.subst_ftvar_of_some
    rw [HMaps.find?_single_scope]
    exact LExpr.find?_buildSubstFromFunction _ _ x hx
  · obtain ⟨τ', -, h⟩ := deskolemizeTy_subst_instance_fixing σ τ mty hfree
    exact ⟨τ', h⟩

/-- Deskolemization commutes with simultaneous instantiation of binders that include no rigid
    parameter name. -/
private theorem deskolemizeTy_subst_ofZip_of_disjoint
    (σ : RigidNames) (vars : List String) (vals : LMonoTys) (mty : LMonoTy)
    (hlen : vals.length = vars.length)
    (hnd : vars.Nodup)
    (hdisj : List.Disj vars (σ.map Prod.fst)) :
    LMonoTy.subst (Subst.ofZip vars (vals.map (deskolemizeTy σ))) (deskolemizeTy σ mty) =
      deskolemizeTy σ (LMonoTy.subst (Subst.ofZip vars vals) mty) := by
  induction mty with
  | ftvar x =>
    rw [deskolemizeTy_ftvar]
    by_cases hx : x ∈ vars
    · obtain ⟨t, ht⟩ := List.mem_zip_1 hlen.symm hx
      rw [LMonoTy.subst_ftvar_of_some
          (Subst.find?_ofZip_of_mem_zip hnd (List.mem_zip_map_snd (deskolemizeTy σ) ht)),
        LMonoTy.subst_ftvar_of_some (Subst.find?_ofZip_of_mem_zip hnd ht)]
    · rw [LMonoTy.subst_ftvar_of_none (Subst.find?_ofZip_of_not_mem hx),
        LMonoTy.subst_ftvar_of_none (Subst.find?_ofZip_of_not_mem hx),
        deskolemizeTy_ftvar]
  | bitvec n =>
    simp only [deskolemizeTy]
    rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
    unfold deskolemizeTy
    rfl
  | tcons nm args ih =>
    rw [deskolemizeTy_tcons, LMonoTy.subst_tcons_map, deskolemizeTy_tcons]
    cases hfind : σ.find? (fun p => p.2 == nm) with
    | some q =>
      simp only
      have hq : q ∈ σ := List.mem_of_find?_eq_some hfind
      have hqnot : q.1 ∉ vars := by
        intro hmem
        exact hdisj hmem (List.mem_map.mpr ⟨q, hq, rfl⟩)
      rw [LMonoTy.subst_ftvar_of_none (Subst.find?_ofZip_of_not_mem hqnot)]
    | none =>
      simp only
      rw [LMonoTy.subst_tcons_map]
      simp only [List.map_map]
      congr 1
      exact List.map_congr_left fun t ht => ih t ht

/-- Opening a closed scheme commutes with deskolemization when deskolemization fixes the scheme or
    its binders include no rigid parameter name. -/
private theorem openFull_deskolemizeTy_transfer_of_safe
    (σ : RigidNames) (Sc : Subst) (ty : LTy) (tys : LMonoTys)
    (hnd : ty.boundVars.Nodup)
    (hclosed : ∀ x ∈ LMonoTy.freeVars ty.toMonoTypeUnsafe, x ∈ ty.boundVars)
    (hsafe : mapLTyTys (deskolemizeTy σ) ty = ty ∨
      List.Disj ty.boundVars (σ.map Prod.fst))
    (hlen : tys.length = ty.boundVars.length) :
    LTy.openFull (mapLTyTys (deskolemizeTy σ) ty)
        (tys.map (fun t => deskolemizeTy σ (LMonoTy.subst Sc t))) =
      deskolemizeTy σ (LMonoTy.subst Sc (LTy.openFull ty tys)) := by
  cases ty with
  | forAll vars body =>
    simp only [LTy.boundVars] at hnd hlen hsafe
    simp only [LTy.toMonoTypeUnsafe, LTy.boundVars] at hclosed
    have hlook : ∀ x ∈ LMonoTy.freeVars body, ∃ t, (x, t) ∈ List.zip vars tys :=
      fun x hx => List.mem_zip_1 hlen.symm (hclosed x hx)
    have hpush : LMonoTy.subst Sc (LMonoTy.subst (Subst.ofZip vars tys) body)
        = LMonoTy.subst (Subst.ofZip vars (tys.map (LMonoTy.subst Sc))) body := by
      refine LMonoTy.subst_subst_of_pointwise _ _ _ body ?_
      intro x hx
      obtain ⟨t, ht⟩ := hlook x hx
      rw [LMonoTy.subst_ftvar_of_some (Subst.find?_ofZip_of_mem_zip hnd ht),
        LMonoTy.subst_ftvar_of_some (Subst.find?_ofZip_of_mem_zip hnd
          (List.mem_zip_map_snd (LMonoTy.subst Sc) ht))]
    simp only [mapLTyTys, LTy.openFull_eq_subst_ofZip]
    rw [hpush]
    rcases hsafe with hfix | hdisj
    · have hbodyfix : deskolemizeTy σ body = body := by
        simpa only [mapLTyTys, LTy.forAll.injEq, true_and] using hfix
      rw [hbodyfix]
      symm
      refine deskolemizeTy_subst_eq_subst σ _ _ body hbodyfix ?_
      intro x hx
      obtain ⟨t, ht⟩ := hlook x hx
      rw [LMonoTy.subst_ftvar_of_some (Subst.find?_ofZip_of_mem_zip hnd
          (List.mem_zip_map_snd (LMonoTy.subst Sc) ht)),
        LMonoTy.subst_ftvar_of_some (Subst.find?_ofZip_of_mem_zip hnd
          (List.mem_zip_map_snd (fun t => deskolemizeTy σ (LMonoTy.subst Sc t)) ht))]
    · simpa only [List.map_map, Function.comp_def] using
        deskolemizeTy_subst_ofZip_of_disjoint σ vars
          (tys.map (LMonoTy.subst Sc)) body (by simp [hlen]) hnd hdisj

/-- An unannotated operator transfers between factories related by deskolemization. -/
private theorem HasType_top_transfer_between {C : Expression.TyContext} {σ : RigidNames}
    (Frig : Lambda.Factory CoreLParams)
    (h_fwf : FactorySigWF (T := CoreLParams) C.functions)
    (h_frel : FactorySigDeskolemizes σ C.functions Frig)
    (h_fsafe : FactorySigDeskolSafe σ C.functions)
    (Γp : TContext CoreLParams.IDMeta) (Sc : Subst)
    (m : CoreLParams.Metadata) (op : CoreLParams.Identifier)
    (f : LFunc CoreLParams) (ty0 : LTy)
    (h_get : (addSkolemTypes C σ).functions[op.name]? = some f)
    (h_ty : f.type = .ok ty0) :
    LExpr.HasType (T := CoreLParams) { C with functions := Frig } Γp
      (mapExprTys (deskolemizeTy σ) (LExpr.op m op none))
      (.forAll [] (deskolemizeTy σ (LMonoTy.subst Sc (LTy.toMonoTypeUnsafe ty0)))) := by
  have hgetsk : C.functions[op.name]? = some f := h_get
  obtain ⟨f', hgetrig, htyrig⟩ := h_frel.find_type op.name f ty0 hgetsk h_ty
  obtain ⟨hnd, hclosed⟩ := Lambda.factory_type_nodup_closed h_fwf hgetsk h_ty
  have htop : LExpr.HasType (T := CoreLParams) { C with functions := Frig } Γp
      (LExpr.op m op none) (mapLTyTys (deskolemizeTy σ) ty0) :=
    .top Γp m f' op _ hgetrig htyrig
  have hopen : LTy.openFull ty0 (ty0.boundVars.map LMonoTy.ftvar)
      = LTy.toMonoTypeUnsafe ty0 := by
    cases ty0 with
    | forAll vars body =>
      simp only [LTy.boundVars] at hnd
      simp only [LTy.toMonoTypeUnsafe, LTy.boundVars] at hclosed
      simp only [LTy.boundVars, LTy.openFull_eq_subst_ofZip, LTy.toMonoTypeUnsafe]
      rw [← LMonoTy.subst_nil body]
      refine agree_on_freeVars_implies_subst_eq ?_
      intro x hx
      rw [LMonoTy.subst_ftvar_of_some
          (Subst.find?_ofZip_of_mem_zip hnd
            (List.mem_zip_map_self vars LMonoTy.ftvar (hclosed x hx))),
        LMonoTy.subst_nil]
  have hcomm := openFull_deskolemizeTy_transfer_of_safe σ Sc ty0
    (ty0.boundVars.map LMonoTy.ftvar) hnd hclosed
    (h_fsafe op.name f ty0 hgetsk h_ty) (by simp)
  rw [hopen] at hcomm
  have hnd' : (mapLTyTys (deskolemizeTy σ) ty0).boundVars.Nodup := by
    cases ty0
    exact hnd
  have hlen : ((ty0.boundVars.map LMonoTy.ftvar).map
      (fun t => deskolemizeTy σ (LMonoTy.subst Sc t))).length =
      (mapLTyTys (deskolemizeTy σ) ty0).boundVars.length := by
    cases ty0 <;> simp [mapLTyTys, LTy.boundVars]
  have hinst := Lambda.HasType_openFull { C with functions := Frig } Γp
    (LExpr.op m op none) (mapLTyTys (deskolemizeTy σ) ty0)
    ((ty0.boundVars.map LMonoTy.ftvar).map
      (fun t => deskolemizeTy σ (LMonoTy.subst Sc t)))
    htop hlen hnd'
  rw [hcomm] at hinst
  rwa [mapExprTys_op_none]

/-! ### The transfer statement -/

/-- If `ρ` acts only on an empty `vars`, prefixing `ρ` to `S` changes nothing. -/
private theorem subst_eq_of_BinderOnly_nil {ρ S : Subst} {vars : List TyIdentifier} (m : LMonoTy)
    (h : BinderOnly ρ S vars) (hvars : vars = []) :
    LMonoTy.subst (ρ ++ S) m = LMonoTy.subst S m := by
  refine agree_on_freeVars_implies_subst_eq ?_
  intro x _
  refine h x ?_
  rw [hvars]
  simp

/-- Extending `S` at `a` by `a`'s image under `ρ ++ S` turns `BinderOnly` on `a :: vars` into
    `BinderOnly` on `vars`. -/
private theorem BinderOnly.extend {ρ S : Subst} {vars : List TyIdentifier} (a : TyIdentifier)
    (h : BinderOnly ρ S (a :: vars)) :
    BinderOnly ρ (HMap.single a (LMonoTy.subst (ρ ++ S) (.ftvar a)) :: S) vars := by
  intro kk hkk
  rw [LMonoTy.subst_ftvar_cons_of_value ρ S a kk]
  by_cases hka : kk = a
  · subst hka
    exact (LMonoTy.subst_ftvar_of_some (HMaps.find?_cons_single_self kk
      (LMonoTy.subst (ρ ++ S) (.ftvar kk)) S)).symm
  · have hnotmem : kk ∉ a :: vars := by
      simp only [List.mem_cons]
      rintro (hc | hc)
      · exact hka hc
      · exact hkk hc
    rw [h kk hnotmem]
    exact (LMonoTy.subst_ftvar_congr kk (HMaps.find?_cons_single_ne a kk
      (LMonoTy.subst (ρ ++ S) (.ftvar a)) S (by simp [bne, hka]))).symm

/-- Prefixing the empty substitution changes nothing. -/
theorem BinderOnly_nil (S : Subst) (vars : List TyIdentifier) : BinderOnly [] S vars := by
  intro k _
  rw [List.nil_append]

/-- Extending `S` at a type variable fresh for `Γsk` preserves `ScopeCorr`. -/
private theorem ScopeCorr.extend {σ : RigidNames} {S : Subst}
    {Γsk Γp : TContext CoreLParams.IDMeta} (a : TyIdentifier) (v : LMonoTy)
    (h_corr : ScopeCorr σ S Γsk Γp) (h_mono : MonoScope Γsk)
    (h_fresh : TContext.isFresh (T := CoreLParams) a Γsk) :
    ScopeCorr σ (HMap.single a v :: S) Γsk Γp := by
  intro k
  rw [h_corr k]
  cases h_find : Γsk.types.find? k with
  | none => simp only [Option.map_none]
  | some tyk =>
    have hbv : LTy.boundVars tyk = [] := h_mono k tyk h_find
    have hnf : a ∉ LMonoTy.freeVars tyk.toMonoTypeUnsafe := by
      have hfv := h_fresh k tyk h_find
      cases tyk with
      | forAll vs mm =>
        simp only [LTy.boundVars] at hbv
        subst hbv
        simpa [LTy.freeVars, LTy.toMonoTypeUnsafe, List.removeAll] using hfv
    have hagree : LMonoTy.subst (HMap.single a v :: S) tyk.toMonoTypeUnsafe
        = LMonoTy.subst S tyk.toMonoTypeUnsafe := by
      refine agree_on_freeVars_implies_subst_eq ?_
      intro x hx
      have hxne : x ≠ a := fun hxeq => hnf (hxeq ▸ hx)
      have hxa : x != a := by simp [bne, hxne]
      exact LMonoTy.subst_ftvar_congr x (HMaps.find?_cons_single_ne a x v S hxa)
    cases tyk with
    | forAll vs mm =>
      simp only [Option.map_some, mapLTyTys]
      simp only [LTy.toMonoTypeUnsafe] at hagree
      rw [hagree]

/-- Inserting a monotype binding in `Γsk` and its substituted, deskolemized image in `Γp`
    preserves `ScopeCorr`. -/
private theorem ScopeCorr.insert_mono {σ : RigidNames} {S : Subst}
    {Γsk Γp : TContext CoreLParams.IDMeta} (k : CoreIdent) (x_ty : LTy)
    (hx : LTy.isMonoType x_ty) (h_corr : ScopeCorr σ S Γsk Γp) :
    ScopeCorr σ S
      { Γsk with types := Γsk.types.insert k x_ty }
      { Γp with
        types := Γp.types.insert k (LTy.forAll []
          (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType x_ty hx)))) } := by
  intro kk
  show HMaps.find? (Γp.types.insert k
        (LTy.forAll [] (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType x_ty hx))))) kk
    = (HMaps.find? (Γsk.types.insert k x_ty) kk).map
        (mapLTyTys (fun mm => deskolemizeTy σ (LMonoTy.subst S mm)))
  by_cases hkk : kk = k
  · subst hkk
    rw [HMaps.find?_insert_self, HMaps.find?_insert_self, Option.map_some,
      mapLTyTys_of_isMonoType _ x_ty hx]
  · rw [HMaps.find?_insert_ne _ _ _ _ hkk, HMaps.find?_insert_ne _ _ _ _ hkk]
    exact h_corr kk

/-- Deskolemization transports an optional binder annotation's compatibility with `mx` to the
    substituted, deskolemized `mx`, when the annotation satisfies `annotNoRigidClash`. -/
private theorem binderAnnot_transfer {σ : RigidNames} {Γsk Γp : TContext CoreLParams.IDMeta}
    (S : Subst) (o : Option LMonoTy) (mx : LMonoTy)
    (h_al : Γp.aliases = Γsk.aliases) (h_awf : TContext.AliasesWF Γsk)
    (h_adesk : AliasesNoSkolem σ Γsk.aliases)
    (h_o : o = none ∨ ∃ t, o = some t ∧ LExpr.AnnotCompat Γsk.aliases t mx)
    (hann : ∀ t, o = some t → annotNoRigidClash σ t = true) :
    o.map (deskolemizeTy σ) = none ∨
      ∃ t, o.map (deskolemizeTy σ) = some t ∧
        LExpr.AnnotCompat Γp.aliases t (deskolemizeTy σ (LMonoTy.subst S mx)) := by
  rcases h_o with hnone | ⟨t0, ht0, hac0⟩
  · refine Or.inl ?_
    rw [hnone]
    rfl
  · refine Or.inr ⟨deskolemizeTy σ t0, ?_, ?_⟩
    · rw [ht0]
      rfl
    · rw [h_al]
      exact annotCompat_transport_gen σ Γsk.aliases t0 mx S hac0 h_awf h_adesk (hann t0 ht0)

/-- Deskolemizing a substituted nullary constructor a user may declare gives it back. -/
private theorem deskolemizeTy_subst_nullary {σ : RigidNames} (hpfx : RigidNamesPrefixed σ)
    (nm : String) (hallowed : isAllowedName nm = true) (Sc : Subst) :
    deskolemizeTy σ (LMonoTy.subst Sc (LTy.toMonoTypeUnsafe (LTy.forAll [] (.tcons nm []))))
      = .tcons nm [] := by
  simp only [LTy.toMonoTypeUnsafe]
  rw [LMonoTy.subst_ground _ _ (by simp [LMonoTy.freeVars, LMonoTys.freeVars]),
    deskolemizeTy_tcons_of_isAllowedName hpfx nm hallowed []]
  rfl

/-- Deskolemizing a substituted function type acts on the argument and result separately. -/
private theorem deskolemizeTy_subst_arrow {σ : RigidNames} (hpfx : RigidNamesPrefixed σ)
    (Sc : Subst) (a b : LMonoTy) :
    deskolemizeTy σ (LMonoTy.subst Sc
        (LTy.toMonoTypeUnsafe (LTy.forAll [] (LMonoTy.arrow a b))))
      = LMonoTy.arrow (deskolemizeTy σ (LMonoTy.subst Sc a))
          (deskolemizeTy σ (LMonoTy.subst Sc b)) := by
  simp only [LTy.toMonoTypeUnsafe, LMonoTy.arrow]
  rw [LMonoTy.subst_tcons_map]
  simp only [List.map_cons, List.map_nil]
  exact deskolemizeTy_arrow hpfx _ _

/-- A literal whose type deskolemization fixes keeps that type under any substitution and
    deskolemization. -/
private theorem constTy_transfer_fixed {σ : RigidNames} (c : LConst) (Sc : Subst)
    (h : deskolemizeTy σ c.ty = c.ty) :
    deskolemizeTy σ (LMonoTy.subst Sc (LTy.toMonoTypeUnsafe (LTy.forAll [] c.ty))) = c.ty := by
  simp only [LTy.toMonoTypeUnsafe]
  rw [LMonoTy.subst_ground Sc c.ty (LConst.ty_freeVars c)]
  exact h

/-- Opening a binder keeps the types of the literals fixed by deskolemization. -/
private theorem ConstTysFixed_varOpen {σ : RigidNames} {e : LExpr CoreLParams.mono}
    (x : IdentT LMonoTy Unit) (k : Nat) (h : ConstTysFixed σ e) :
    ConstTysFixed σ (LExpr.varOpen k x e) := by
  intro c hc
  rw [getConsts_varOpen] at hc
  exact h c hc

/-- Deskolemization transports a constant's typing at `t` when substituting and deskolemizing
    fixes `t`. -/
private theorem skolemTransfer_const {Ctx : Expression.TyContext} {σ : RigidNames}
    (Γ : TContext CoreLParams.IDMeta) (m : ExpressionMetadata) (c : LConst) (t : LMonoTy)
        (Sc : Subst)
    (hty : deskolemizeTy σ (LMonoTy.subst Sc (LTy.toMonoTypeUnsafe (LTy.forAll [] t))) = t)
    (h : LExpr.HasType (T := CoreLParams) Ctx Γ (.const m c) (.forAll [] t)) :
    LExpr.HasType (T := CoreLParams) Ctx Γ (mapExprTys (deskolemizeTy σ) (.const m c))
      (.forAll [] (deskolemizeTy σ
        (LMonoTy.subst Sc (LTy.toMonoTypeUnsafe (LTy.forAll [] t))))) := by
  have hexpr : mapExprTys (deskolemizeTy σ) (LExpr.const m c : LExpr CoreLParams.mono)
      = .const m c := by
    simp [mapExprTys, LExpr.replaceUserProvidedType]
  rw [hexpr, hty]
  exact h

/-- Skolem-scope elimination: a derivation for `esk` over `Γsk` at `ty` gives, for choices `S` of
    the rigid parameters and `ρ` of `ty`'s binders, one for its deskolemization over `Γp` at the
    deskolemized instance, when no literal's type of `esk` names a rigid constant. -/
private theorem skolemTransfer_aux_gen_between {C : Expression.TyContext} {σ : RigidNames}
    (Frig : Lambda.Factory CoreLParams)
    (hpfx : RigidNamesPrefixed σ)
    (h_fwf : FactorySigWF (T := CoreLParams) C.functions)
    (h_frel : FactorySigDeskolemizes σ C.functions Frig)
    (h_fsafe : FactorySigDeskolSafe σ C.functions)
    (n : Nat) :
    ∀ (Γsk : TContext CoreLParams.IDMeta) (esk : LExpr CoreLParams.mono) (ty : LTy),
      LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ) Γsk esk ty →
      LExpr.sizeOf esk ≤ n →
      ∀ (Γp : TContext CoreLParams.IDMeta) (S ρ : Subst),
        ScopeCorr σ S Γsk Γp → MonoScope Γsk → BinderOnly ρ S (LTy.boundVars ty) →
        Γp.aliases = Γsk.aliases → TContext.AliasesWF Γsk →
        AliasesNoSkolem σ Γsk.aliases →
        allExprTys (annotNoRigidClash σ) esk = true → ConstTysFixed σ esk →
        LExpr.HasType (T := CoreLParams) { C with functions := Frig } Γp
          (mapExprTys (deskolemizeTy σ) esk)
          (.forAll [] (deskolemizeTy σ
            (LMonoTy.subst (ρ ++ S) (LTy.toMonoTypeUnsafe ty)))) := by
  have hknownSk := knownTypes_contains_of_getElem?_addSkolemTypes
    (Csk := addSkolemTypes C σ) (Crig := { C with functions := Frig })
    (addSkolemTypes_getElem?_congr C { C with functions := Frig } σ (fun _ => rfl))
  have hmono_forAll : ∀ t : LMonoTy, LTy.isMonoType (LTy.forAll [] t) := fun _ => rfl
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  intro Γsk esk ty h hsize
  induction h with
  | tbool_const Γ' m b hk =>
    intro Γp S ρ _ _ _ _ _ _ _ _
    exact skolemTransfer_const Γp m (LConst.boolConst b) _ (ρ ++ S)
      (deskolemizeTy_subst_nullary hpfx "bool" (isAllowedName_eq_toList ▸ rfl) _)
      (LExpr.HasType.tbool_const (T := CoreLParams) Γp m b
        (containsName_of_addSkolemTypes C hpfx "bool" (isAllowedName_eq_toList ▸ rfl) hk))
  | tint_const Γ' m n hk =>
    intro Γp S ρ _ _ _ _ _ _ _ _
    exact skolemTransfer_const Γp m (LConst.intConst n) _ (ρ ++ S)
      (deskolemizeTy_subst_nullary hpfx "int" (isAllowedName_eq_toList ▸ rfl) _)
      (LExpr.HasType.tint_const (T := CoreLParams) Γp m n
        (containsName_of_addSkolemTypes C hpfx "int" (isAllowedName_eq_toList ▸ rfl) hk))
  | treal_const Γ' m r hk =>
    intro Γp S ρ _ _ _ _ _ _ _ _
    exact skolemTransfer_const Γp m (LConst.rationalConst r) _ (ρ ++ S)
      (deskolemizeTy_subst_nullary hpfx "real" (isAllowedName_eq_toList ▸ rfl) _)
      (LExpr.HasType.treal_const (T := CoreLParams) Γp m r
        (containsName_of_addSkolemTypes C hpfx "real" (isAllowedName_eq_toList ▸ rfl) hk))
  | tstr_const Γ' m st hk =>
    intro Γp S ρ _ _ _ _ _ _ _ _
    exact skolemTransfer_const Γp m (LConst.strConst st) _ (ρ ++ S)
      (deskolemizeTy_subst_nullary hpfx "string" (isAllowedName_eq_toList ▸ rfl) _)
      (LExpr.HasType.tstr_const (T := CoreLParams) Γp m st
        (containsName_of_addSkolemTypes C hpfx "string" (isAllowedName_eq_toList ▸ rfl) hk))
  | tbitvec_const Γ' m n b hk =>
    intro Γp S ρ _ _ _ _ _ _ _ _
    have hty : deskolemizeTy σ (LMonoTy.subst (ρ ++ S)
        (LTy.toMonoTypeUnsafe (LTy.forAll [] (LMonoTy.bitvec n)))) = LMonoTy.bitvec n := by
      simp only [LTy.toMonoTypeUnsafe]
      rw [LMonoTy.subst_bitvec]
      rfl
    exact skolemTransfer_const Γp m (LConst.bitvecConst n b) _ (ρ ++ S) hty
      (LExpr.HasType.tbitvec_const (T := CoreLParams) Γp m n b
        (containsName_of_addSkolemTypes C hpfx "bitvec" (isAllowedName_eq_toList ▸ rfl) hk))
  | tmap_const Γ' m k v d es hk hw =>
    intro Γp S ρ _ _ _ _ _ _ _ h_cf
    exact skolemTransfer_const Γp m (LConst.mapConst k v d es) _ (ρ ++ S)
      (constTy_transfer_fixed _ _ (h_cf _ (List.mem_singleton_self _)))
      (LExpr.HasType.tmap_const (T := CoreLParams) Γp m k v d es
        (containsName_of_addSkolemTypes C hpfx "Map" (isAllowedName_eq_toList ▸ rfl) hk) hw)
  | tseq_const Γ' m a es hk hw =>
    intro Γp S ρ _ _ _ _ _ _ _ h_cf
    exact skolemTransfer_const Γp m (LConst.sequenceConst a es) _ (ρ ++ S)
      (constTy_transfer_fixed _ _ (h_cf _ (List.mem_singleton_self _)))
      (LExpr.HasType.tseq_const (T := CoreLParams) Γp m a es
        (containsName_of_addSkolemTypes C hpfx "Sequence" (isAllowedName_eq_toList ▸ rfl) hk) hw)
  | tvar Γ' m k tyk h_find =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have hbv : LTy.boundVars tyk = [] := h_mono k tyk h_find
    have hexpr : mapExprTys (deskolemizeTy σ) (.fvar m k none)
        = (.fvar m k none : LExpr CoreLParams.mono) := by
      simp [mapExprTys, LExpr.replaceUserProvidedType]
    rw [hexpr]
    have hfp : Γp.types.find? k
        = some (mapLTyTys (fun mm => deskolemizeTy σ (LMonoTy.subst S mm)) tyk) := by
      rw [h_corr k, h_find, Option.map_some]
    have hgoal : (LTy.forAll [] (deskolemizeTy σ
          (LMonoTy.subst (ρ ++ S) (LTy.toMonoTypeUnsafe tyk))))
        = mapLTyTys (fun mm => deskolemizeTy σ (LMonoTy.subst S mm)) tyk := by
      cases tyk with
      | forAll vs mm =>
        simp only [LTy.boundVars] at hbv
        subst hbv
        simp only [mapLTyTys, LTy.toMonoTypeUnsafe]
        rw [subst_eq_of_BinderOnly_nil mm h_bo (by simp [LTy.boundVars])]
    rw [hgoal]
    exact LExpr.HasType.tvar (T := CoreLParams) Γp m k _ hfp
  | tvar_annotated Γ' m k ty_o ty_s tys ann h_find h_len h_open h_ac =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have hbv : LTy.boundVars ty_o = [] := h_mono k ty_o h_find
    have htys : tys = [] := by
      rw [hbv] at h_len
      exact List.eq_nil_of_length_eq_zero (by simpa using h_len)
    have hts : ty_s = LTy.toMonoTypeUnsafe ty_o := by
      rw [← h_open, htys]
      exact openFull_of_boundVars_nil ty_o hbv _
    have hcollapse : LMonoTy.subst (ρ ++ S) ty_s = LMonoTy.subst S ty_s :=
      subst_eq_of_BinderOnly_nil ty_s h_bo (by simp [LTy.boundVars])
    have hfp : Γp.types.find? k
        = some (mapLTyTys (fun mm => deskolemizeTy σ (LMonoTy.subst S mm)) ty_o) := by
      rw [h_corr k, h_find, Option.map_some]
    have hbv' : LTy.boundVars
        (mapLTyTys (fun mm => deskolemizeTy σ (LMonoTy.subst S mm)) ty_o) = [] := by
      cases ty_o with
      | forAll vs mm =>
        simp only [LTy.boundVars] at hbv
        subst hbv
        rfl
    have hopen' : LTy.openFull
          (mapLTyTys (fun mm => deskolemizeTy σ (LMonoTy.subst S mm)) ty_o) []
        = deskolemizeTy σ (LMonoTy.subst (ρ ++ S) ty_s) := by
      rw [openFull_of_boundVars_nil _ hbv' _, hcollapse, hts]
      cases ty_o with
      | forAll vs mm => rfl
    have hac' : LExpr.AnnotCompat Γp.aliases (deskolemizeTy σ ann)
        (deskolemizeTy σ (LMonoTy.subst (ρ ++ S) ty_s)) := by
      rw [h_al]
      exact annotCompat_transport_gen σ Γ'.aliases ann ty_s (ρ ++ S) h_ac h_awf h_adesk h_sk
    rw [mapExprTys_fvar_some]
    simp only [LTy.toMonoTypeUnsafe]
    exact LExpr.HasType.tvar_annotated (T := CoreLParams) Γp m k _ _ [] _ hfp
      (by simp [hbv']) hopen' hac'
  | tabs Γ' m name x x_ty e' e_ty o h_efresh hx he h_body h_o h_valid ih =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have h_cf_body : ConstTysFixed σ e' := h_cf
    have hcollapse : ∀ mm : LMonoTy, LMonoTy.subst (ρ ++ S) mm = LMonoTy.subst S mm :=
      fun mm => subst_eq_of_BinderOnly_nil mm h_bo (by simp [LTy.boundVars])
    have harr : deskolemizeTy σ (LMonoTy.subst (ρ ++ S)
          (LTy.toMonoTypeUnsafe (LTy.forAll [] (LMonoTy.arrow
            (LTy.toMonoType x_ty hx) (LTy.toMonoType e_ty he)))))
        = LMonoTy.arrow (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType x_ty hx)))
            (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType e_ty he))) := by
      rw [deskolemizeTy_subst_arrow hpfx, hcollapse, hcollapse]
    obtain ⟨v, hv_fresh, _, h_body'⟩ :=
      HasType_varOpen_reopen h_mono hx h_body (mapExprTys (deskolemizeTy σ) e') (σ.map Prod.fst)
    have hcorr' := ScopeCorr.insert_mono x.1 x_ty hx h_corr
    have h_ftvar_ok : Option.all (annotNoRigidClash σ) (some (LMonoTy.ftvar v)) = true :=
      mtyAllTyConsNames_ftvar _ v
    have h_sk_body : allExprTys (annotNoRigidClash σ) (LExpr.varOpen 0
          ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) e') = true :=
      allExprTys_varOpen (allExprTys_abs h_sk) h_ftvar_ok
    have hlt : LExpr.sizeOf (LExpr.varOpen 0
        ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) e') < n := by
      rw [LExpr.varOpen_sizeOf]
      simp only [LExpr.sizeOf] at hsize
      omega
    have h_rec := ihn _ hlt
      { Γ' with
        types := Γ'.types.insert x.1 x_ty }
      (LExpr.varOpen 0 ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) e')
      e_ty h_body' (Nat.le_refl _)
      { Γp with
        types := Γp.types.insert x.1 (LTy.forAll []
            (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType x_ty hx)))) } S []
      hcorr' (h_mono.insert (List.isEmpty_iff.mp hx))
      (BinderOnly_nil S (LTy.boundVars e_ty)) h_al h_awf h_adesk h_sk_body
      (ConstTysFixed_varOpen _ _ h_cf_body)
    rw [mapExprTys_varOpen, List.nil_append] at h_rec
    simp only [Option.map_some, deskolemizeTy_ftvar] at h_rec
    have h_o' := binderAnnot_transfer S o (LTy.toMonoType x_ty hx) h_al h_awf h_adesk h_o
      (fun t0 ht0 => annotNoRigidClash_of_abs σ m name t0 e' (ht0 ▸ h_sk))
    show LExpr.HasType (T := CoreLParams) { C with functions := Frig } Γp
        (LExpr.abs m name (o.map (deskolemizeTy σ)) (mapExprTys (deskolemizeTy σ) e'))
        (LTy.forAll [] (deskolemizeTy σ (LMonoTy.subst (ρ ++ S)
          (LTy.toMonoTypeUnsafe (LTy.forAll [] (LMonoTy.arrow
            (LTy.toMonoType x_ty hx) (LTy.toMonoType e_ty he)))))))
    rw [harr]
    exact LExpr.HasType.tabs (T := CoreLParams) Γp m name
      ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy)
      (LTy.forAll [] (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType x_ty hx))))
      (mapExprTys (deskolemizeTy σ) e')
      (LTy.forAll [] (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType e_ty he))))
      (o.map (deskolemizeTy σ)) hv_fresh (hmono_forAll _) (hmono_forAll _) h_rec h_o'
      (binderAnnot_sourceTyWF_deskolemizeTy hknownSk h_al h_adesk h_valid)
  | tapp Γ' m e1 e2 t1 t2 h1 h2 hd1 hd2 ih1 ih2 =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have hbv1 : LTy.boundVars t1 = [] := List.isEmpty_iff.mp h1
    have hbv2 : LTy.boundVars t2 = [] := List.isEmpty_iff.mp h2
    have hexpr : mapExprTys (deskolemizeTy σ) (LExpr.app m e1 e2)
        = LExpr.app m (mapExprTys (deskolemizeTy σ) e1)
            (mapExprTys (deskolemizeTy σ) e2) := rfl
    have hbo2 : BinderOnly ρ S (LTy.boundVars t2) := by rw [hbv2]; rw [hbv1] at h_bo; exact h_bo
    obtain ⟨h_sk1, h_sk2⟩ := allExprTys_app h_sk
    have h_cf1 : ConstTysFixed σ e1 := fun c hc => h_cf c (List.mem_append_left _ hc)
    have h_cf2 : ConstTysFixed σ e2 := fun c hc => h_cf c (List.mem_append_right _ hc)
    have hsz : LExpr.sizeOf e1 ≤ n ∧ LExpr.sizeOf e2 ≤ n := by
      simp only [LExpr.sizeOf] at hsize
      omega
    have hih2 := ih2 hsz.2 Γp S ρ h_corr h_mono hbo2 h_al h_awf h_adesk h_sk2 h_cf2
    have hboArr : BinderOnly ρ S
        (LTy.boundVars (LTy.forAll [] (LMonoTy.arrow
          (LTy.toMonoType t2 h2) (LTy.toMonoType t1 h1)))) := by
      simp only [LTy.boundVars]; rw [hbv1] at h_bo; exact h_bo
    have hih1 := ih1 hsz.1 Γp S ρ h_corr h_mono hboArr h_al h_awf h_adesk h_sk1 h_cf1
    have harr : deskolemizeTy σ (LMonoTy.subst (ρ ++ S)
          (LTy.toMonoTypeUnsafe (LTy.forAll [] (LMonoTy.arrow
            (LTy.toMonoType t2 h2) (LTy.toMonoType t1 h1)))))
        = LMonoTy.arrow (deskolemizeTy σ (LMonoTy.subst (ρ ++ S) (LTy.toMonoType t2 h2)))
            (deskolemizeTy σ (LMonoTy.subst (ρ ++ S) (LTy.toMonoType t1 h1))) :=
      deskolemizeTy_subst_arrow hpfx _ _ _
    rw [← LMonoTy.arrow, harr] at hih1
    have hmono1 : LTy.isMonoType
        (LTy.forAll [] (deskolemizeTy σ
          (LMonoTy.subst (ρ ++ S) (LTy.toMonoType t1 h1)))) := by
      simp [LTy.isMonoType, LTy.boundVars]
    have hmono2 : LTy.isMonoType
        (LTy.forAll [] (deskolemizeTy σ
          (LMonoTy.subst (ρ ++ S) (LTy.toMonoType t2 h2)))) := by
      simp [LTy.isMonoType, LTy.boundVars]
    have hgoal : LTy.toMonoTypeUnsafe t1 = LTy.toMonoType t1 h1 := by
      cases t1 with | forAll vs mm => rfl
    rw [hexpr, hgoal]
    exact LExpr.HasType.tapp (T := CoreLParams) Γp m _ _ _ _ hmono1 hmono2 hih1 hih2
  | tinst Γ' e' ty0 e_ty x x_ty h_sub h_open ih =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    cases ty0 with
    | forAll vars0 mty0 =>
      simp only [LTy.open] at h_open
      split at h_open
      · rename_i h_mem
        subst h_open
        have hbo' : BinderOnly (HMap.single x (LMonoTy.subst (ρ ++ S) x_ty) :: ρ) S vars0 := by
          intro kk hkk
          have hkxne : kk ≠ x := fun hkx => hkk (hkx ▸ h_mem)
          have hne : kk != x := by simp [bne, hkxne]
          have hleft : LMonoTy.subst
              ((HMap.single x (LMonoTy.subst (ρ ++ S) x_ty) :: ρ) ++ S) (.ftvar kk)
              = LMonoTy.subst (ρ ++ S) (.ftvar kk) := by
            rw [List.cons_append]
            exact LMonoTy.subst_ftvar_congr kk
              (HMaps.find?_cons_single_ne x kk (LMonoTy.subst (ρ ++ S) x_ty) (ρ ++ S) hne)
          rw [hleft]
          refine h_bo kk ?_
          simp only [LTy.boundVars]
          intro hmem'
          have hmem2 : kk ∈ vars0 := by
            simp only [List.removeAll] at hmem'
            exact (List.mem_filter.mp hmem').1
          exact hkk hmem2
        have hih := ih hsize Γp S (HMap.single x (LMonoTy.subst (ρ ++ S) x_ty) :: ρ)
          h_corr h_mono hbo' h_al h_awf h_adesk h_sk h_cf
        have heq : LMonoTy.subst
            ((HMap.single x (LMonoTy.subst (ρ ++ S) x_ty) :: ρ) ++ S) mty0
            = LMonoTy.subst (ρ ++ S) (LMonoTy.subst (Subst.singleton x x_ty) mty0) := by
          rw [List.cons_append]
          exact LMonoTy.subst_push_single x x_ty (ρ ++ S) mty0
        simp only [LTy.toMonoTypeUnsafe] at hih ⊢
        rw [heq] at hih
        exact hih
      · subst h_open
        exact ih hsize Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
  | tgen Γ' e' a ty0 h_sub h_fresh ih =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have hbvclose : LTy.boundVars (LTy.close a ty0) = a :: LTy.boundVars ty0 := by
      cases ty0 with | forAll vs mm => rfl
    have htmu : LTy.toMonoTypeUnsafe (LTy.close a ty0) = LTy.toMonoTypeUnsafe ty0 := by
      cases ty0 with | forAll vs mm => rfl
    rw [hbvclose] at h_bo
    have hcorr' := ScopeCorr.extend a (LMonoTy.subst (ρ ++ S) (.ftvar a))
      h_corr h_mono h_fresh
    have hih := ih hsize Γp (HMap.single a (LMonoTy.subst (ρ ++ S) (.ftvar a)) :: S) ρ
      hcorr' h_mono (BinderOnly.extend a h_bo) h_al h_awf h_adesk h_sk h_cf
    have hbody := agree_on_freeVars_implies_subst_eq
      (S₁ := ρ ++ (HMap.single a (LMonoTy.subst (ρ ++ S) (.ftvar a)) :: S)) (S₂ := ρ ++ S)
      (ty := LTy.toMonoTypeUnsafe ty0)
      (fun kk _ => LMonoTy.subst_ftvar_cons_of_value ρ S a kk)
    rw [hbody] at hih
    rw [htmu]
    exact hih
  | tif Γ' m c e1 e2 ty0 hc h1 h2 ihc ih1 ih2 =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have hexpr : mapExprTys (deskolemizeTy σ) (LExpr.ite m c e1 e2)
        = LExpr.ite m (mapExprTys (deskolemizeTy σ) c)
            (mapExprTys (deskolemizeTy σ) e1) (mapExprTys (deskolemizeTy σ) e2) := rfl
    obtain ⟨h_skc, h_sk1, h_sk2⟩ := allExprTys_ite h_sk
    have h_cfc : ConstTysFixed σ c := fun x hx =>
      h_cf x (List.mem_append_left _ (List.mem_append_left _ hx))
    have h_cf1 : ConstTysFixed σ e1 := fun x hx =>
      h_cf x (List.mem_append_left _ (List.mem_append_right _ hx))
    have h_cf2 : ConstTysFixed σ e2 := fun x hx => h_cf x (List.mem_append_right _ hx)
    have hsz : LExpr.sizeOf c ≤ n ∧ LExpr.sizeOf e1 ≤ n ∧ LExpr.sizeOf e2 ≤ n := by
      simp only [LExpr.sizeOf] at hsize
      omega
    have hihc := ihc hsz.1 Γp S [] h_corr h_mono
      (BinderOnly_nil S (LTy.boundVars (LTy.forAll [] LMonoTy.bool)))
      h_al h_awf h_adesk h_skc h_cfc
    have hbool : deskolemizeTy σ (LMonoTy.subst ([] ++ S)
        (LTy.toMonoTypeUnsafe (LTy.forAll [] LMonoTy.bool))) = LMonoTy.bool :=
      deskolemizeTy_subst_nullary hpfx "bool" (isAllowedName_eq_toList ▸ rfl) _
    rw [hbool] at hihc
    have hih1 := ih1 hsz.2.1 Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk1 h_cf1
    have hih2 := ih2 hsz.2.2 Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk2 h_cf2
    rw [hexpr]
    exact LExpr.HasType.tif (T := CoreLParams) Γp m _ _ _ _ hihc hih1 hih2
  | teq Γ' m e1 e2 ty0 h1 h2 ih1 ih2 =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have hexpr : mapExprTys (deskolemizeTy σ) (LExpr.eq m e1 e2)
        = LExpr.eq m (mapExprTys (deskolemizeTy σ) e1)
            (mapExprTys (deskolemizeTy σ) e2) := rfl
    obtain ⟨h_sk1, h_sk2⟩ := allExprTys_eq h_sk
    have h_cf1 : ConstTysFixed σ e1 := fun c hc => h_cf c (List.mem_append_left _ hc)
    have h_cf2 : ConstTysFixed σ e2 := fun c hc => h_cf c (List.mem_append_right _ hc)
    have hsz : LExpr.sizeOf e1 ≤ n ∧ LExpr.sizeOf e2 ≤ n := by
      simp only [LExpr.sizeOf] at hsize
      omega
    have hih1 := ih1 hsz.1 Γp S [] h_corr h_mono (BinderOnly_nil S (LTy.boundVars ty0))
      h_al h_awf h_adesk h_sk1 h_cf1
    have hih2 := ih2 hsz.2 Γp S [] h_corr h_mono (BinderOnly_nil S (LTy.boundVars ty0))
      h_al h_awf h_adesk h_sk2 h_cf2
    have hbool : deskolemizeTy σ (LMonoTy.subst (ρ ++ S)
        (LTy.toMonoTypeUnsafe (LTy.forAll [] LMonoTy.bool))) = LMonoTy.bool :=
      deskolemizeTy_subst_nullary hpfx "bool" (isAllowedName_eq_toList ▸ rfl) _
    rw [hexpr, hbool]
    exact LExpr.HasType.teq (T := CoreLParams) Γp m _ _ _ hih1 hih2
  | tquant Γ' m kd name tr tr_ty x x_ty e' o h_efresh hx h_body h_tr h_o h_valid ih1 ih2 =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    obtain ⟨h_sk_tr, h_sk_e⟩ := allExprTys_quant h_sk
    have h_cf_tr : ConstTysFixed σ tr := fun c hc => h_cf c (List.mem_append_left _ hc)
    have h_cf_e : ConstTysFixed σ e' := fun c hc => h_cf c (List.mem_append_right _ hc)
    have hbool : ∀ Sc : Subst, deskolemizeTy σ (LMonoTy.subst Sc
        (LTy.toMonoTypeUnsafe (LTy.forAll [] LMonoTy.bool))) = LMonoTy.bool :=
      deskolemizeTy_subst_nullary hpfx "bool" (isAllowedName_eq_toList ▸ rfl)
    have hmono' : MonoScope { Γ' with
        types := Γ'.types.insert x.1 x_ty } :=
      h_mono.insert (List.isEmpty_iff.mp hx)
    obtain ⟨v, hv_fresh, _, h_body'⟩ :=
      HasType_varOpen_reopen h_mono hx h_body (mapExprTys (deskolemizeTy σ) e') (σ.map Prod.fst)
    have h_tr' : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ)
        { Γ' with
          types := Γ'.types.insert x.1 x_ty }
        (LExpr.varOpen 0 ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) tr)
        tr_ty :=
      HasType_varOpen_ftvar hmono' v h_tr
    have hcorr' := ScopeCorr.insert_mono x.1 x_ty hx h_corr
    have hsz : LExpr.sizeOf e' < n ∧ LExpr.sizeOf tr < n := by
      simp only [LExpr.sizeOf] at hsize
      omega
    have h_ftvar_ok : Option.all (annotNoRigidClash σ) (some (LMonoTy.ftvar v)) = true :=
      mtyAllTyConsNames_ftvar _ v
    have h_sk_varOpen : ∀ ee : Expression.Expr, allExprTys (annotNoRigidClash σ) ee = true →
        allExprTys (annotNoRigidClash σ) (LExpr.varOpen 0
            ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) ee) = true := by
      intro ee hee
      exact allExprTys_varOpen hee h_ftvar_ok
    have hltBody : LExpr.sizeOf (LExpr.varOpen 0
        ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) e') < n := by
      rw [LExpr.varOpen_sizeOf]
      exact hsz.1
    have h_recBody := ihn _ hltBody
      { Γ' with
        types := Γ'.types.insert x.1 x_ty }
      (LExpr.varOpen 0 ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) e')
      (LTy.forAll [] LMonoTy.bool) h_body' (Nat.le_refl _)
      { Γp with
        types := Γp.types.insert x.1 (LTy.forAll []
            (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType x_ty hx)))) } S []
      hcorr' hmono' (BinderOnly_nil S (LTy.boundVars (LTy.forAll [] LMonoTy.bool)))
      h_al h_awf h_adesk (h_sk_varOpen e' h_sk_e) (ConstTysFixed_varOpen _ _ h_cf_e)
    have hltTr : LExpr.sizeOf (LExpr.varOpen 0
        ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) tr) < n := by
      rw [LExpr.varOpen_sizeOf]
      exact hsz.2
    have h_recTr := ihn _ hltTr
      { Γ' with
        types := Γ'.types.insert x.1 x_ty }
      (LExpr.varOpen 0 ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy) tr)
      tr_ty h_tr' (Nat.le_refl _)
      { Γp with
        types := Γp.types.insert x.1 (LTy.forAll []
            (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType x_ty hx)))) } S []
      hcorr' hmono' (BinderOnly_nil S (LTy.boundVars tr_ty))
      h_al h_awf h_adesk (h_sk_varOpen tr h_sk_tr)
      (ConstTysFixed_varOpen _ _ h_cf_tr)
    rw [mapExprTys_varOpen, hbool] at h_recBody
    rw [mapExprTys_varOpen] at h_recTr
    simp only [Option.map_some, deskolemizeTy_ftvar] at h_recBody h_recTr
    have h_o' := binderAnnot_transfer S o (LTy.toMonoType x_ty hx) h_al h_awf h_adesk h_o
      (fun t0 ht0 => annotNoRigidClash_of_quant σ m kd name t0 tr e' (ht0 ▸ h_sk))
    show LExpr.HasType (T := CoreLParams) { C with functions := Frig } Γp
        (LExpr.quant m kd name (o.map (deskolemizeTy σ)) (mapExprTys (deskolemizeTy σ) tr)
          (mapExprTys (deskolemizeTy σ) e'))
        (LTy.forAll [] (deskolemizeTy σ (LMonoTy.subst (ρ ++ S)
          (LTy.toMonoTypeUnsafe (LTy.forAll [] LMonoTy.bool)))))
    rw [hbool]
    exact LExpr.HasType.tquant (T := CoreLParams) Γp m kd name
      (mapExprTys (deskolemizeTy σ) tr) _
      ((x.1, some (LMonoTy.ftvar v)) : CoreIdent × Option LMonoTy)
      (LTy.forAll [] (deskolemizeTy σ (LMonoTy.subst S (LTy.toMonoType x_ty hx))))
      (mapExprTys (deskolemizeTy σ) e') (o.map (deskolemizeTy σ))
      hv_fresh (hmono_forAll _) h_recBody h_recTr h_o'
      (binderAnnot_sourceTyWF_deskolemizeTy hknownSk h_al h_adesk h_valid)
  | top Γ' m f op ty0 h_get h_ty =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    exact HasType_top_transfer_between Frig h_fwf h_frel h_fsafe
      Γp (ρ ++ S) m op f ty0 h_get h_ty
  | top_annotated Γ' m f op ty_o ty_s tys ann h_get h_ty h_len h_open h_ac =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have hget' : C.functions[op.name]? = some f := h_get
    obtain ⟨f', hgetrig, htyrig⟩ := h_frel.find_type op.name f ty_o hget' h_ty
    obtain ⟨hnd, hclosed⟩ := Lambda.factory_type_nodup_closed h_fwf hget' h_ty
    have hac' : LExpr.AnnotCompat Γp.aliases (deskolemizeTy σ ann)
        (deskolemizeTy σ (LMonoTy.subst (ρ ++ S) ty_s)) := by
      rw [h_al]
      exact annotCompat_transport_gen σ Γ'.aliases ann ty_s (ρ ++ S) h_ac h_awf h_adesk h_sk
    have hopen' : LTy.openFull (mapLTyTys (deskolemizeTy σ) ty_o)
          (tys.map (fun t => deskolemizeTy σ (LMonoTy.subst (ρ ++ S) t)))
        = deskolemizeTy σ (LMonoTy.subst (ρ ++ S) ty_s) := by
      rw [← h_open]
      exact openFull_deskolemizeTy_transfer_of_safe σ (ρ ++ S) ty_o tys hnd hclosed
        (h_fsafe op.name f ty_o hget' h_ty) h_len
    rw [mapExprTys_op_some]
    simp only [LTy.toMonoTypeUnsafe]
    exact LExpr.HasType.top_annotated (T := CoreLParams) Γp m f' op
      (mapLTyTys (deskolemizeTy σ) ty_o) _ _ _ hgetrig htyrig
      (Eq.trans (List.length_map _) h_len) hopen' hac'
  | talias Γ' e' mty mty' h_ae h_sub ih =>
    intro Γp S ρ h_corr h_mono h_bo h_al h_awf h_adesk h_sk h_cf
    have h_bo_mty : BinderOnly ρ S (LTy.boundVars (LTy.forAll [] mty)) := h_bo
    have hih := ih hsize Γp S ρ h_corr h_mono h_bo_mty h_al h_awf h_adesk h_sk h_cf
    have h_ae_S : AliasEquiv Γ'.aliases (LMonoTy.subst (ρ ++ S) mty)
        (LMonoTy.subst (ρ ++ S) mty') :=
      Lambda.LExpr.AliasEquiv_subst Γ'.aliases mty mty' (ρ ++ S) h_ae h_awf
    have h_ae_p : AliasEquiv Γp.aliases
        (deskolemizeTy σ (LMonoTy.subst (ρ ++ S) mty))
        (deskolemizeTy σ (LMonoTy.subst (ρ ++ S) mty')) := by
      rw [h_al]
      exact AliasEquiv_deskolemizeTy h_ae_S h_adesk
    simp only [LTy.toMonoTypeUnsafe] at hih ⊢
    exact LExpr.HasType.talias (T := CoreLParams) Γp _ _ _ h_ae_p hih

/-- Skolem-scope elimination between factories related by deskolemization, when no literal's
    type of `esk` names a rigid constant. -/
theorem skolemTransfer_gen_between {C : Expression.TyContext} {σ : RigidNames}
    (Frig : Lambda.Factory CoreLParams)
    (hpfx : RigidNamesPrefixed σ)
    (h_fwf : FactorySigWF (T := CoreLParams) C.functions)
    (h_frel : FactorySigDeskolemizes σ C.functions Frig)
    (h_fsafe : FactorySigDeskolSafe σ C.functions)
    {Γsk : TContext CoreLParams.IDMeta} {esk : LExpr CoreLParams.mono} {ty : LTy}
    (h : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ) Γsk esk ty) :
    ∀ (Γp : TContext CoreLParams.IDMeta) (S ρ : Subst),
      ScopeCorr σ S Γsk Γp → MonoScope Γsk → BinderOnly ρ S (LTy.boundVars ty) →
      Γp.aliases = Γsk.aliases → TContext.AliasesWF Γsk →
      AliasesNoSkolem σ Γsk.aliases →
      allExprTys (annotNoRigidClash σ) esk = true → ConstTysFixed σ esk →
      LExpr.HasType (T := CoreLParams) { C with functions := Frig } Γp
        (mapExprTys (deskolemizeTy σ) esk)
        (.forAll [] (deskolemizeTy σ
          (LMonoTy.subst (ρ ++ S) (LTy.toMonoTypeUnsafe ty)))) :=
  skolemTransfer_aux_gen_between Frig hpfx h_fwf h_frel h_fsafe
    (LExpr.sizeOf esk) Γsk esk ty h (Nat.le_refl _)

/-! ### Connecting the two pushed scopes -/

/-- The two pushed scopes correspond at the empty rigid-parameter choice. -/
private theorem ScopeCorr_pushed (C : Expression.TyContext) (Γ : TContext CoreLParams.IDMeta)
    (σ : RigidNames) (sigR : @LMonoTySignature Unit)
    (h_amb : NoSkolemAmbient C Γ σ)
    (h_rt_sig : ∀ mty ∈ sigR.values, deskolemizeTy σ (skolemizeTy σ mty) = mty) :
    ScopeCorr σ []
      { Γ with
        types := Γ.types.push (HMap.ofList
          (sigR.map (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2))))) }
      { Γ with
        types := Γ.types.push (HMap.ofList
          (sigR.map (fun q => (q.1, LTy.forAll [] q.2)))) } := by
  have hfun : (fun m => deskolemizeTy σ (LMonoTy.subst ([] : Subst) m))
      = deskolemizeTy σ := by
    funext m; rw [LMonoTy.subst_nil]
  intro k
  have hSk : HMap.find? (HMap.ofList
      (sigR.map (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2))))) k
      = (HMap.find? (HMap.ofList sigR) k).map (fun m => LTy.forAll [] (skolemizeTy σ m)) :=
    HMap.find?_ofList_map_snd sigR (fun m => LTy.forAll [] (skolemizeTy σ m)) k
  have hP : HMap.find? (HMap.ofList (sigR.map (fun q => (q.1, LTy.forAll [] q.2)))) k
      = (HMap.find? (HMap.ofList sigR) k).map (fun m => LTy.forAll [] m) :=
    HMap.find?_ofList_map_snd sigR (fun m => LTy.forAll [] m) k
  show HMaps.find? (Γ.types.push (HMap.ofList
        (sigR.map (fun q => (q.1, LTy.forAll [] q.2))))) k
      = (HMaps.find? (Γ.types.push (HMap.ofList
          (sigR.map (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2)))))) k).map
        (mapLTyTys (fun m => deskolemizeTy σ (LMonoTy.subst ([] : Subst) m)))
  rw [hfun]
  cases hcase : HMap.find? (HMap.ofList sigR) k with
  | none =>
    simp only [HMaps.push, HMaps.find?, hSk, hP, hcase, Option.map_none]
    cases hamb : HMaps.find? Γ.types k with
    | none => simp only [Option.map_none]
    | some ty => simp only [Option.map_some, h_amb.ctxTypes k ty hamb]
  | some mty =>
    have hmem : mty ∈ sigR.values := by
      rw [ListMap.values_eq_map_snd]
      exact HMap.mem_values_ofList sigR mty (HMap.find?_mem_values _ hcase)
    simp only [HMaps.push, HMaps.find?, hSk, hP, hcase, Option.map_some, mapLTyTys,
      h_rt_sig mty hmem]

/-- Pushing a skolemized monotype signature keeps every stored scheme a monotype. -/
theorem MonoScope_pushed (Γ : TContext CoreLParams.IDMeta) (σ : RigidNames)
    (sigR : @LMonoTySignature Unit) (h_mono : MonoScope Γ) :
    MonoScope
      { Γ with
        types := Γ.types.push (HMap.ofList
          (sigR.map (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2))))) } := by
  intro k ty h_find
  have hSk : HMap.find? (HMap.ofList
      (sigR.map (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2))))) k
      = (HMap.find? (HMap.ofList sigR) k).map (fun m => LTy.forAll [] (skolemizeTy σ m)) :=
    HMap.find?_ofList_map_snd sigR (fun m => LTy.forAll [] (skolemizeTy σ m)) k
  have hfind : HMaps.find? (Γ.types.push (HMap.ofList
      (sigR.map (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2)))))) k = some ty := h_find
  cases hcase : HMap.find? (HMap.ofList sigR) k with
  | none =>
    rw [HMaps.push, HMaps.find?, hSk, hcase, Option.map_none] at hfind
    exact h_mono k ty hfind
  | some mty =>
    rw [HMaps.push, HMaps.find?, hSk, hcase, Option.map_some] at hfind
    rw [← Option.some_inj.mp hfind]
    rfl

/-- Skolem-scope elimination: a derivation for `esk` over the scope binding each parameter at its
    skolemized type gives one for its deskolemization `e` over the scope binding each parameter at
    its own type, at the deskolemized type, when `esk`'s annotations satisfy `annotNoRigidClash`
    and no literal's type of `esk` names a rigid constant. -/
theorem HasType_of_skolemScope_general
    (C : Expression.TyContext) (Γ : TContext Unit) (σ : RigidNames)
    (hpfx : RigidNamesPrefixed σ)
    (sigR : @LMonoTySignature Unit) (e esk : Expression.Expr) (mty : LMonoTy)
    (h : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ)
          { Γ with types := Γ.types.push (Strata.Util.HMap.ofList
              (sigR.map (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2))))) }
          esk (.forAll [] mty))
    (h_amb : NoSkolemAmbient C Γ σ)
    (h_fwf : FactorySigWF C.functions)
    (h_aliasesWF : Lambda.TContext.AliasesWF Γ)
    (h_mono : MonoScope Γ)
    (h_rt_sig : ∀ mty ∈ sigR.values, deskolemizeTy σ (skolemizeTy σ mty) = mty)
    (h_annot : allExprTys (annotNoRigidClash σ) esk = true)
    (h_consts : ConstTysFixed σ esk)
    (h_rt_e : mapExprTys (deskolemizeTy σ) esk = e) :
    LExpr.HasType (T := CoreLParams) C
      { Γ with types := Γ.types.push (Strata.Util.HMap.ofList
          (sigR.map (fun q => (q.1, LTy.forAll [] q.2)))) }
      e (.forAll [] (deskolemizeTy σ mty)) := by
  have hT := skolemTransfer_gen_between C.functions hpfx h_fwf
    (FactorySigDeskolemizes.refl_of_fixed σ C.functions h_amb.functions)
    (FactorySigDeskolSafe.of_fixed σ C.functions h_amb.functions) h
    { Γ with
      types := Γ.types.push (Strata.Util.HMap.ofList
        (sigR.map (fun q => (q.1, LTy.forAll [] q.2)))) } [] []
    (ScopeCorr_pushed C Γ σ sigR h_amb h_rt_sig)
    (MonoScope_pushed Γ σ sigR h_mono)
    (BinderOnly_nil [] (LTy.boundVars (LTy.forAll [] mty)))
    rfl h_aliasesWF h_amb.aliases h_annot h_consts
  simp only [LTy.toMonoTypeUnsafe, List.append_nil, LMonoTy.subst_nil] at hT
  rw [h_rt_e] at hT
  exact hT

/-! ## Type names in scope and registered skolemized types -/

/-! ### Registering skolemized types -/

/-- Registering a renaming's unregistered constants keeps every recorded arity. -/
theorem KnownTypesExtends_addSkolemTypes (C : Expression.TyContext) {σ : RigidNames}
    (hfresh : RigidNamesFresh C.knownTypes σ) :
    KnownTypesExtends C.knownTypes (addSkolemTypes C σ).knownTypes := by
  intro n a h
  rw [addSkolemTypes_getElem?]
  by_cases hn : n ∈ σ.map Prod.snd
  · obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hn
    subst hpn
    have hmem : p.2 ∈ C.knownTypes := Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])
    exact absurd hmem (hfresh p hp)
  · rw [ite_eq_right hn]
    exact h

/-- A type a table contains is contained in any table extending it. -/
private theorem KnownTypes_contains_mono (ks ks' : Lambda.KnownTypes)
    (k : KnownType)
    (hext : KnownTypesExtends ks ks')
    (h : KnownTypes.contains ks k = true) :
    KnownTypes.contains ks' k = true := by
  simp only [KnownTypes.contains, Identifiers.contains,
    KnownType.arity] at h ⊢
  elim_err h with i hlk
  simp only [beq_iff_eq] at h
  subst h
  rw [hext k.name k.metadata hlk]
  simp

mutual
/-- Skolemizing a registered type by a renaming with fresh constants gives a type registered after
    adding those constants. -/
theorem knownInstance_skolemizeTy (C : Expression.TyContext) {σ : RigidNames}
    (hfresh : RigidNamesFresh C.knownTypes σ)
    (t : LMonoTy) (h : t.knownInstance C.knownTypes = true) :
    (skolemizeTy σ t).knownInstance (addSkolemTypes C σ).knownTypes = true := by
  match t with
  | .ftvar x =>
    rw [skolemizeTy_ftvar]
    cases hf : σ.find? (fun p => p.1 == x) with
    | none => simp only [LMonoTy.knownInstance]
    | some p =>
      have hp : p ∈ σ := List.mem_of_find?_eq_some hf
      have hlk : (addSkolemTypes C σ).knownTypes[p.2]? = some 0 := by
        rw [addSkolemTypes_getElem?, ite_eq_left (List.mem_map.mpr ⟨p, hp, rfl⟩)]
      simp [LMonoTy.knownInstance, LMonoTys.knownInstances, KnownTypes.contains,
        Identifiers.contains, KnownType.arity, hlk]
  | .bitvec n =>
    rw [skolemizeTy_bitvec]
    simp only [LMonoTy.knownInstance]
  | .tcons name args =>
    rw [skolemizeTy_tcons]
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h ⊢
    refine ⟨?_, knownInstances_skolemizeTy C hfresh args h.2⟩
    rw [List.length_map]
    exact KnownTypes_contains_mono _ _ _ (KnownTypesExtends_addSkolemTypes C hfresh) h.1

/-- Skolemizing a list of registered types by a renaming with fresh constants gives types
    registered after adding those constants. -/
private theorem knownInstances_skolemizeTy (C : Expression.TyContext) {σ : RigidNames}
    (hfresh : RigidNamesFresh C.knownTypes σ)
    (ts : LMonoTys) (h : LMonoTys.knownInstances ts C.knownTypes = true) :
    LMonoTys.knownInstances (ts.map (skolemizeTy σ)) (addSkolemTypes C σ).knownTypes = true := by
  match ts with
  | [] => simp only [List.map_nil, LMonoTys.knownInstances]
  | t :: rest =>
    simp only [LMonoTys.knownInstances] at h
    elim_err h with ht
    simp only [List.map_cons, LMonoTys.knownInstances]
    rw [ite_eq_left (knownInstance_skolemizeTy C hfresh t ht)]
    exact knownInstances_skolemizeTy C hfresh rest h
end

/-! ### Discharging `NoSkolemAmbient` -/

/-- Splitting a fixed type, or a list of fixed types, along the arrow spine exposes only fixed
    pieces. -/
private theorem deskolemizeTy_destructArrow_fixed_combined
    {σ : RigidNames} (hpfx : RigidNamesPrefixed σ) (n : Nat) :
    (∀ mty : LMonoTy, tySize mty ≤ n → deskolemizeTy σ mty = mty →
      ∀ t ∈ LMonoTy.destructArrow mty, deskolemizeTy σ t = t) ∧
    (∀ mtys : LMonoTys, tysSize mtys ≤ n →
      (∀ t ∈ mtys, deskolemizeTy σ t = t) →
      ∀ t ∈ LMonoTys.destructArrow mtys, deskolemizeTy σ t = t) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    refine ⟨?_, ?_⟩
    · intro mty hsize hfixed t ht
      rcases destructArrow_eq_self_or_arrow mty with hself | ⟨hd, tl, rfl⟩
      · rw [hself] at ht
        exact List.mem_singleton.mp ht ▸ hfixed
      · have hargs :
            (hd :: tl).map (deskolemizeTy σ) = hd :: tl := by
          rw [deskolemizeTy_tcons_of_isAllowedName hpfx "arrow"
            (isAllowedName_eq_toList ▸ rfl)] at hfixed
          exact LMonoTy.tcons.inj hfixed |>.2
        have hargs' :
            deskolemizeTy σ hd = hd ∧ tl.map (deskolemizeTy σ) = tl := by
          simpa only [List.map_cons, List.cons.injEq] using hargs
        have hhd : deskolemizeTy σ hd = hd := by
          exact hargs'.1
        have htl : ∀ u ∈ tl, deskolemizeTy σ u = u :=
          List.forall_eq_self_of_map_eq_self hargs'.2
        simp only [LMonoTy.destructArrow] at ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hhd
        · have htlSize : tysSize tl < n := by
            simp only [tySize, tysSize] at hsize
            omega
          exact (ih (tysSize tl) htlSize).2 tl (Nat.le_refl _) htl t ht
    · intro mtys hsize hfixed t ht
      cases mtys with
      | nil => exact absurd ht (by simp [LMonoTys.destructArrow])
      | cons hd tl =>
        simp only [LMonoTys.destructArrow, List.mem_append] at ht
        have hhdSize : tySize hd < n := by
          simp only [tysSize] at hsize
          omega
        have htlSize : tysSize tl < n := by
          simp only [tysSize] at hsize
          omega
        rcases ht with ht | ht
        · exact (ih (tySize hd) hhdSize).1 hd (Nat.le_refl _)
            (hfixed hd List.mem_cons_self) t ht
        · exact (ih (tysSize tl) htlSize).2 tl (Nat.le_refl _)
            (fun u hu => hfixed u (List.mem_cons_of_mem hd hu)) t ht

/-- Splitting a fixed type along its arrow spine exposes only fixed pieces. -/
private theorem deskolemizeTy_destructArrow_fixed {σ : RigidNames}
    (hpfx : RigidNamesPrefixed σ) (mty : LMonoTy)
    (hfixed : deskolemizeTy σ mty = mty) :
    ∀ t ∈ LMonoTy.destructArrow mty, deskolemizeTy σ t = t :=
  (deskolemizeTy_destructArrow_fixed_combined hpfx (tySize mty)).1
    mty (Nat.le_refl _) hfixed

/-- Every factory scheme is fixed when every stored input and output type is fixed. -/
private theorem functions_of_fixed_signature_parts (C : Expression.TyContext) {σ : RigidNames}
    (hpfx : RigidNamesPrefixed σ)
    (hfixed : ∀ f ∈ C.functions.toArray,
      (∀ ity ∈ f.inputs.values, deskolemizeTy σ ity = ity) ∧
      deskolemizeTy σ f.output = f.output) :
    ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
      C.functions[nm]? = some f → f.type = .ok ty →
      mapLTyTys (deskolemizeTy σ) ty = ty := by
  intro nm f ty hf hty
  have hmem : f ∈ C.functions.toArray :=
    Factory.getElem?_is_some_implies_mem hf
  obtain ⟨hins, hout⟩ := hfixed f hmem
  have houtPieces := deskolemizeTy_destructArrow_fixed hpfx f.output hout
  simp only [LFunc.type, LFuncDefined.type, bind, Except.bind] at hty
  elim_err hty
  elim_err hty
  cases hvals : f.inputs.values with
  | nil =>
    rw [hvals] at hty
    simp only [Except.ok.injEq] at hty
    rw [← hty]
    simp only [mapLTyTys, hout]
  | cons ity irest =>
    rw [hvals] at hty
    simp only [Except.ok.injEq] at hty
    rw [← hty]
    have hity : deskolemizeTy σ ity = ity :=
      hins ity (hvals ▸ List.mem_cons_self)
    have hrest : ∀ t ∈ irest ++ LMonoTy.destructArrow f.output,
        deskolemizeTy σ t = t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hins t (hvals ▸ List.mem_cons_of_mem ity ht)
      · exact houtPieces t ht
    simp only [mapLTyTys]
    rw [deskolemizeTy_mkArrow hpfx ity
      (irest ++ LMonoTy.destructArrow f.output) hity hrest]

/-- Deskolemization by a rigid-prefixed renaming fixes every factory scheme when no factory
    signature type names a constant of the renaming. -/
private theorem functions_fixed_of_notRigidConst {C : Expression.TyContext} {σ : RigidNames}
    (hpfx : RigidNamesPrefixed σ)
    (h : ∀ f ∈ C.functions.toArray, ∀ ty ∈ f.output :: f.inputs.values,
      mtyAllTyConsNames (notRigidConst σ) ty = true) :
    ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
      C.functions[nm]? = some f → f.type = .ok ty →
      mapLTyTys (deskolemizeTy σ) ty = ty := by
  apply functions_of_fixed_signature_parts C hpfx
  intro f hf
  refine ⟨fun ity hity => ?_, ?_⟩
  · exact deskolemizeTy_eq_self_of_notRigidConst ity (h f hf ity (List.mem_cons_of_mem _ hity))
  · exact deskolemizeTy_eq_self_of_notRigidConst f.output (h f hf f.output List.mem_cons_self)

/-- When no constant of `σ` is a type name in scope (`scopeTyNames`), no constant of `σ` names a
    type synonym in scope. -/
private theorem aliasNames_ne_of_not_scopeTyNames {C : Expression.TyContext}
    {Env : Expression.TyEnv} {σ : RigidNames} (hnot : ∀ p ∈ σ, p.2 ∉ scopeTyNames C Env) :
    ∀ al ∈ Env.context.aliases, ∀ p ∈ σ, p.2 ≠ al.name := by
  intro al hal p hp heq
  refine hnot p hp ?_
  unfold scopeTyNames
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  exact List.mem_flatMap.mpr ⟨al, hal, heq ▸ List.mem_cons_self⟩

/-- Deskolemizing by a prefixed renaming `σ` none of whose constants is a type name in scope
    (`scopeTyNames`) changes nothing in scope: no variable type, type synonym or factory
    signature mentions one of its constants. -/
theorem NoSkolemAmbient.of_not_scopeTyNames {C : Expression.TyContext}
    {Env : Expression.TyEnv} {σ : RigidNames} (hpfx : RigidNamesPrefixed σ)
    (hnot : ∀ p ∈ σ, p.2 ∉ scopeTyNames C Env) : NoSkolemAmbient C Env.context σ := by
  refine ⟨?_, ?_, ?_⟩
  · intro z ty hz
    obtain ⟨vs, mty⟩ := ty
    simp only [mapLTyTys]
    congr 1
    refine deskolemizeTy_eq_self_of_notRigidConst mty
      (mtyAllTyConsNames_notRigidConst_of_not_mem fun p hp hn => hnot p hp ?_)
    unfold scopeTyNames
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    exact List.mem_flatMap.mpr ⟨_, Strata.Util.HMaps.find?_mem_values _ hz, hn⟩
  · intro al hal
    refine ⟨deskolemizeTy_eq_self_of_notRigidConst al.type
      (mtyAllTyConsNames_notRigidConst_of_not_mem fun p hp hn => hnot p hp ?_), ?_⟩
    · unfold scopeTyNames
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      exact List.mem_flatMap.mpr ⟨al, hal, List.mem_cons_of_mem _ hn⟩
    · intro args
      have hfind : σ.find? (fun p => p.2 == al.name) = none := by
        rw [List.find?_eq_none]
        intro q hq
        simpa only [beq_iff_eq] using aliasNames_ne_of_not_scopeTyNames hnot al hal q hq
      rw [deskolemizeTy_tcons, hfind]
  · refine functions_fixed_of_notRigidConst hpfx fun f hf ty hty =>
      mtyAllTyConsNames_notRigidConst_of_not_mem fun p hp hn => hnot p hp ?_
    unfold scopeTyNames
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨f, Array.mem_toList_iff.mpr hf, ?_⟩)
    exact List.mem_flatMap.mpr ⟨ty, hty, hn⟩

/-! ### Rigid renamings chosen against the names in scope -/

/-- Minting rigid names against a set `scope` that holds every type name in scope whenever there
    are type parameters gives a rigid renaming against the names in scope and the names
    `own ()`. -/
theorem ScopeRigid.of_cover (C : Expression.TyContext) (Env : Expression.TyEnv)
    (scope progSigs : Thunk (Std.HashSet String)) (name : String) (own : Unit → List String)
    (typeArgs : List String)
    (hcov : typeArgs ≠ [] → ∀ n ∈ scopeTyNames C Env, n ∈ scope.get) :
    ScopeRigid C Env (own ()) typeArgs (rigidNamesAvoiding C scope progSigs name own typeArgs) :=
  have hspec := rigidNamesAvoiding_spec C scope progSigs name own typeArgs
  { prefixed := hspec.1
    nodup := hspec.2.1
    fresh := hspec.2.2.1
    map_fst := hspec.2.2.2.1
    not_scope := fun p hp hn => by
      have hne : typeArgs ≠ [] :=
        hspec.2.2.2.1 ▸ List.ne_nil_of_mem (List.mem_map_of_mem (f := Prod.fst) hp)
      exact (hspec.2.2.2.2 p hp).1 (hcov hne _ hn)
    not_extra := fun p hp => (hspec.2.2.2.2 p hp).2.2 }

/-- `scopeTyNameThunk` holds every type name in scope. -/
theorem scopeTyNameThunk_cover (C : Expression.TyContext) (Env : Expression.TyEnv) :
    ∀ n ∈ scopeTyNames C Env, n ∈ (scopeTyNameThunk C Env).get :=
  Std.HashSet.mem_ofList_of_mem

/-- No constant of a rigid renaming chosen against the names in scope names a type synonym in
    scope. -/
theorem ScopeRigid.aliasNames {C : Expression.TyContext} {Env : Expression.TyEnv}
    {extra typeArgs : List String} {σ : RigidNames} (h : ScopeRigid C Env extra typeArgs σ) :
    ∀ al ∈ Env.context.aliases, ∀ p ∈ σ, p.2 ≠ al.name :=
  aliasNames_ne_of_not_scopeTyNames h.not_scope

/-- Deskolemizing by a rigid renaming chosen against the names in scope changes nothing in scope:
    no variable type, type synonym or factory signature mentions one of its constants. -/
theorem ScopeRigid.noSkolemAmbient {C : Expression.TyContext} {Env : Expression.TyEnv}
    {extra typeArgs : List String} {σ : RigidNames} (h : ScopeRigid C Env extra typeArgs σ) :
    NoSkolemAmbient C Env.context σ :=
  NoSkolemAmbient.of_not_scopeTyNames h.prefixed h.not_scope

/-! ### How the type names in scope change from one declaration to the next -/

/-- Contexts with the same functions and environments with the same typing context have the
    same type names in scope. -/
theorem scopeTyNames_congr {C C' : Expression.TyContext} {Env Env' : Expression.TyEnv}
    (hf : C'.functions.toArray = C.functions.toArray) (hc : Env'.context = Env.context) :
    scopeTyNames C' Env' = scopeTyNames C Env := by
  unfold scopeTyNames
  rw [hf, hc]

/-- An environment with the same type synonyms as `Env`, and whose variable types all occur
    among those of `Env`, has no type names in scope beyond those of `Env`. -/
private theorem scopeTyNames_of_values_mem {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} (ha : Env'.context.aliases = Env.context.aliases)
    (hv : ∀ ty ∈ Env'.context.types.values, ty ∈ Env.context.types.values) :
    ∀ n ∈ scopeTyNames C Env', n ∈ scopeTyNames C Env := by
  intro n hn
  unfold scopeTyNames at hn ⊢
  rw [ha] at hn
  rcases List.mem_append.mp hn with hctx | hfun
  · rcases List.mem_append.mp hctx with hal | hvar
    · exact List.mem_append_left _ (List.mem_append_left _ hal)
    · obtain ⟨ty, hty, hnty⟩ := List.mem_flatMap.mp hvar
      exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ty, hv ty hty, hnty⟩))
  · exact List.mem_append_right _ hfun

/-- Environments with equivalent typing contexts (the same lookups in each variable scope and
    the same type synonyms) have the same type names in scope. -/
private theorem scopeTyNames_of_equiv {C : Expression.TyContext} {Env Env' : Expression.TyEnv}
    (h : TContext.Equiv (T := CoreLParams) Env'.context Env.context) :
    ∀ n ∈ scopeTyNames C Env', n ∈ scopeTyNames C Env :=
  scopeTyNames_of_values_mem h.2 fun ty => (h.1.mem_values ty).mp

/-- A variable scope with no entries adds no type names in scope: when the variable scopes of
    `Env'` are equivalent to those of `Env` below an extra scope `m` with no entries, and the type
    synonyms agree, every type name in scope for `Env'` is one for `Env`. -/
private theorem scopeTyNames_of_empty_scope {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv}
    {m : Strata.Util.HMap (Identifier CoreLParams.IDMeta) LTy} (hm : m.values = [])
    (ht : Strata.Util.HMaps.Equiv Env'.context.types (m :: Env.context.types))
    (ha : Env'.context.aliases = Env.context.aliases) :
    ∀ n ∈ scopeTyNames C Env', n ∈ scopeTyNames C Env := by
  refine scopeTyNames_of_values_mem ha fun ty hty => ?_
  obtain ⟨m', hm', hty'⟩ :=
    (Strata.Util.HMaps.mem_values_iff_exists_scope _ ty).mp ((ht.mem_values ty).mp hty)
  rcases List.mem_cons.mp hm' with rfl | hrest
  · rw [hm] at hty'
    nomatch hty'
  · exact (Strata.Util.HMaps.mem_values_iff_exists_scope _ ty).mpr ⟨m', hrest, hty'⟩

/-- Core source resolution adds no type names in scope, even from an empty type-scope stack:
    every type name in scope in the resulting environment is one in the starting environment,
    against any context. -/
theorem scopeTyNames_of_resolve {C D : Expression.TyContext} {Env Env' : Expression.TyEnv}
    {source : Expression.Expr} {typed : LExprT CoreLParams.mono}
    (h : SourceExpr.resolve C Env source = .ok (typed, Env')) :
    ∀ n ∈ scopeTyNames D Env', n ∈ scopeTyNames D Env := by
  cases htypes : Env.context.types with
  | nil =>
    obtain ⟨hequiv, haliases⟩ :=
      SourceExpr.resolve_context_of_empty C Env Env' source typed h htypes
    have hstack : Strata.Util.HMaps.Equiv Env'.context.types
        (Strata.Util.HMap.empty :: Env.context.types) := by
      rw [htypes]
      exact hequiv
    exact scopeTyNames_of_empty_scope Strata.Util.HMap.values_empty hstack haliases
  | cons first rest =>
    have hne : Env.context.types ≠ [] := by
      rw [htypes]
      exact List.cons_ne_nil first rest
    exact scopeTyNames_of_equiv
      (SourceExpr.resolve_context_equiv_of_ne C Env Env' source typed h hne)

/-- Registering the function `f` adds at most the type names of its signature to the type names
    in scope. -/
private theorem scopeTyNames_addFactoryFunction (C : Expression.TyContext)
    (Env : Expression.TyEnv) (f : LFunc CoreLParams) :
    ∀ n ∈ scopeTyNames (C.addFactoryFunction f) Env,
      n ∈ scopeTyNames C Env ∨ n ∈ funcSigTyNames f := by
  intro n hn
  unfold scopeTyNames at hn ⊢
  rcases List.mem_append.mp hn with hctx | hfun
  · exact Or.inl (List.mem_append_left _ hctx)
  · obtain ⟨g, hg, hng⟩ := List.mem_flatMap.mp hfun
    rcases mem_addFactoryFunction C f g (Array.mem_toList_iff.mp hg) with hold | rfl
    · refine Or.inl (List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, ?_, hng⟩))
      exact Array.mem_toList_iff.mpr hold
    · exact Or.inr hng

/-- If `S` holds every type name in scope, then once the function `f` is registered, `S` with
    the type names of the signature of `f` added holds every type name in scope. -/
theorem scopeTyNames_addFactoryFunction_cover {C : Expression.TyContext}
    {Env : Expression.TyEnv} {S : Std.HashSet String} {f : LFunc CoreLParams}
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) :
    ∀ n ∈ scopeTyNames (C.addFactoryFunction f) Env, n ∈ S.insertMany (funcSigTyNames f) :=
  Std.HashSet.mem_insertMany_of_cover hcov (scopeTyNames_addFactoryFunction C Env f)

/-- Declaring the type synonym `al` (prepending it to the synonyms, keeping the variables) adds
    its name and the type names of its body to the type names in scope. -/
theorem scopeTyNames_addAlias (C : Expression.TyContext) {Env Env' : Expression.TyEnv}
    {al : TypeAlias} (ha : Env'.context.aliases = al :: Env.context.aliases)
    (ht : Env'.context.types = Env.context.types) :
    scopeTyNames C Env' = al.name :: getTypeRefs al.type ++ scopeTyNames C Env := by
  unfold scopeTyNames
  rw [ha, ht, List.flatMap_cons]
  simp only [List.cons_append, List.append_assoc]

/-- Appending functions to the factory, with the same typing context, adds exactly the
    signature type names of the appended functions to the type names in scope. -/
theorem scopeTyNames_append {C C' : Expression.TyContext} {Env Env' : Expression.TyEnv}
    {l : List (LFunc CoreLParams)}
    (h : C'.functions.toArray.toList = C.functions.toArray.toList ++ l)
    (hc : Env'.context = Env.context) :
    scopeTyNames C' Env' =
      scopeTyNames C Env ++ Factory.tyNamesFrom C.functions.toArray.size C'.functions := by
  have hsuffix :
      (C'.functions.toArray.extract C.functions.toArray.size).toList = l := by
    rw [Array.toList_extract, List.extract_eq_drop_take',
      ← Array.length_toList (xs := C'.functions.toArray), List.take_length, h,
      ← Array.length_toList, List.drop_left]
  unfold scopeTyNames Factory.tyNamesFrom
  rw [hsuffix, h, hc, List.flatMap_append]
  simp only [List.append_assoc]

/-- Registering the functions `g a` for `a ∈ l` in order adds exactly the signature type names
    of the functions it registers to the type names in scope. -/
theorem scopeTyNames_foldl_addFactoryFunction_eq {α : Type} (C : Expression.TyContext)
    (Env : Expression.TyEnv) (l : List α) (g : α → LFunc CoreLParams) :
    scopeTyNames (l.foldl (fun C a => C.addFactoryFunction (g a)) C) Env =
      scopeTyNames C Env ++ Factory.tyNamesFrom C.functions.toArray.size
        (l.foldl (fun C a => C.addFactoryFunction (g a)) C).functions := by
  obtain ⟨_, hfs⟩ := foldl_addFactoryFunction_toList C l g
  exact scopeTyNames_append hfs rfl

/-- Registering, in order, the functions `g a` in a context `D` and `g' a` in a context `D'`,
    where `g a` and `g' a` have the same name and signature, keeps the signature type names of
    the factories equal when `D` and `D'` register the same function names and have the same
    signature type names. -/
private theorem foldl_addFactoryFunction_sigTyNames_congr {α : Type}
    (g g' : α → LFunc CoreLParams) :
    ∀ (l : List α), (∀ a ∈ l, (g a).name.name = (g' a).name.name ∧
      (g a).inputs = (g' a).inputs ∧ (g a).output = (g' a).output) →
    ∀ (D D' : Expression.TyContext), (∀ n, n ∈ D.functions ↔ n ∈ D'.functions) →
      D.functions.toArray.toList.flatMap funcSigTyNames =
        D'.functions.toArray.toList.flatMap funcSigTyNames →
      (l.foldl (fun C a => C.addFactoryFunction (g a)) D).functions.toArray.toList.flatMap
          funcSigTyNames =
        (l.foldl (fun C a => C.addFactoryFunction (g' a)) D').functions.toArray.toList.flatMap
          funcSigTyNames
  | [], _, _, _, _, hsig => hsig
  | a :: rest, h, D, D', hmem, hsig => by
    obtain ⟨hname, hins, hout⟩ := h a List.mem_cons_self
    have hrest : ∀ b ∈ rest, (g b).name.name = (g' b).name.name ∧
        (g b).inputs = (g' b).inputs ∧ (g b).output = (g' b).output :=
      fun b hb => h b (List.mem_cons_of_mem a hb)
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hn : (g a).name.name ∈ D.functions
    · have hn' : (g' a).name.name ∈ D'.functions := by
        rw [← hname]
        exact (hmem _).mp hn
      simp only [LContext.addFactoryFunction, hn, hn', ↓reduceDIte]
      exact foldl_addFactoryFunction_sigTyNames_congr g g' rest hrest D D' hmem hsig
    · have hn' : (g' a).name.name ∉ D'.functions := by
        rw [← hname]
        exact fun hmem' => hn ((hmem _).mpr hmem')
      simp only [LContext.addFactoryFunction, hn, hn', ↓reduceDIte]
      refine foldl_addFactoryFunction_sigTyNames_congr g g' rest hrest _ _ ?_ ?_
      · intro n
        rw [Factory.push_mem_iff, Factory.push_mem_iff, hmem n, hname]
      · simp only [Factory.push, Array.toList_push, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, hsig, funcSigTyNames, hins, hout]

/-- Registering, in order, the functions `g a` or the functions `g' a` for `a ∈ l` gives the
    same type names in scope when each `g a` has the name and signature of `g' a`. -/
theorem scopeTyNames_foldl_addFactoryFunction_congr {α : Type} (C : Expression.TyContext)
    (Env : Expression.TyEnv) (l : List α) (g g' : α → LFunc CoreLParams)
    (h : ∀ a ∈ l, (g a).name.name = (g' a).name.name ∧
      (g a).inputs = (g' a).inputs ∧ (g a).output = (g' a).output) :
    scopeTyNames (l.foldl (fun C a => C.addFactoryFunction (g a)) C) Env =
      scopeTyNames (l.foldl (fun C a => C.addFactoryFunction (g' a)) C) Env := by
  unfold scopeTyNames
  rw [foldl_addFactoryFunction_sigTyNames_congr g g' l h C C (fun _ => Iff.rfl) rfl]

/-! ### Annotations naming only type constructors that satisfy a predicate -/

/-- Every annotation of `e` names only type constructors satisfying `q` when every type name of
    its annotations (`exprTyNames`) does. -/
theorem allExprTys_of_exprTyNames {q : String → Bool} {e : Expression.Expr}
    (h : ∀ n ∈ exprTyNames e, q n = true) : allExprTys (mtyAllTyConsNames q) e = true := by
  rw [allExprTys_eq_all_exprAnnotTys]
  refine List.all_eq_true.mpr fun t ht => List.all_eq_true.mpr fun n hn => h n ?_
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨t, ht, hn⟩)

/-- The literals of an expression have unchanged types when none of the type names in the types
    of its annotations or literals (`exprTyNames`) is a rigid constant. -/
theorem ConstTysFixed_of_exprTyNames {σ : RigidNames} {e : Expression.Expr}
    (h : ∀ p ∈ σ, p.2 ∉ exprTyNames e) : ConstTysFixed σ e :=
  ConstTysFixed_of_litTyNames e fun p hp hn => h p hp (List.mem_append_right _ hn)

end Core

end -- public section
