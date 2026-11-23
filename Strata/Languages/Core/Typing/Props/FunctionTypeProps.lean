/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.FunctionType
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
public import Strata.Languages.Core.Typing.Props.SkolemScopeProps
public import Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
public import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
import Strata.Util.Tactics
import all Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
import Strata.DL.Lambda.LExprTypeSpecProps
import all Strata.Languages.Core.FunctionType
import all Strata.Languages.Core.TypeSkolem
import all Strata.Languages.Core.Typing.Props.TypeSkolemProps
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.NamePrefixesProps
import Strata.Util.NameProofs

/-! # Properties of function type checking

Key theorems:
* `Function.rigidNames_fresh`, `Function.rigidNames_spec`: a function's rigid renaming uses
  distinct, reserved, unregistered constants that avoid the given names and, minted against a
  set covering the names in scope, those names.
* `Function.tyNames_renameReservedTypeArgs`, `Function.sigTyNames_renameReservedTypeArgs`:
  renaming type parameters keeps the type names a function mentions.
* `Function.measureTy_int_or_mem`: a measure is checked at `int` or a formal's type.
* `resolveKnownTys_ok_inv`: resolving a signature's declared types.
* `FuncAlphaVariant.eq_self_of_allowed`, `FuncHasType_iff_of_allowed`: a function without
  reserved type parameters is its only renaming.
* `Function.renameReservedTypeArgs_alphaVariant`,
  `Function.renameReservedTypeArgs_typeArgs_allowed`: the checker's renaming of reserved type
  parameters is such a renaming, to allowed names.
* `Function.checkNameFresh_ok`, `Function.typeCheck_inputs_nodup`: a passing freshness check means
  the name is unused, and a type-checked function has distinct input names. -/

public section

namespace Core

open Lambda Imperative
open TypeSpec
open Strata.Util (HMap HMaps)

/-! ### Resolving the declared types of a signature -/

/-- A fold whose step resolves a type's aliases and appends a resolution
    satisfying `P` keeps the environment and returns the pointwise
    resolutions. -/
private theorem resolveAliasesFold_spec {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] [Std.ToFormat IDMeta] (P : LMonoTy → Prop)
    (step : (LMonoTys × TEnv IDMeta) → LMonoTy →
      Except Std.Format (LMonoTys × TEnv IDMeta))
    (hstep : ∀ (acc : LMonoTys × TEnv IDMeta) (ty : LMonoTy)
        (res : LMonoTys × TEnv IDMeta),
        step acc ty = .ok res →
        ∃ ty' EnvA, LMonoTy.resolveAliases ty acc.snd = .ok (ty', EnvA) ∧
          P ty' ∧ res = (acc.fst ++ [ty'], EnvA))
    (tys : LMonoTys) (Env0 EnvF : TEnv IDMeta) (acc0 resAcc : LMonoTys)
    (h : List.foldlM step (acc0, Env0) tys = .ok (resAcc, EnvF)) :
    EnvF = Env0 ∧ ∃ rtys : LMonoTys, resAcc = acc0 ++ rtys ∧
      LMonoTys.resolveAliases tys Env0 = .ok (rtys, Env0) ∧
      List.Rel₂
        (fun ty ty' => LMonoTy.resolveAliases ty Env0 = .ok (ty', Env0) ∧ P ty')
        tys rtys := by
  induction tys generalizing acc0 with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, [], by simp, ?_, .nil⟩
    simp only [LMonoTys.resolveAliases, pure, Except.pure]
  | cons ty rest ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨accMid, hs, hrest⟩ := (Except.bind_is_ok _ _ _).mp h
    obtain ⟨ty', EnvA, hres, hP, hmid⟩ := hstep (acc0, Env0) ty accMid hs
    have hEnvA : EnvA = Env0 :=
      LMonoTy.resolveAliases_env_eq ty Env0 ty' EnvA hres
    subst hmid hEnvA
    obtain ⟨hEnvF, rtys, hacc, hresolve, hrel⟩ := ih (acc0 ++ [ty']) hrest
    have hacc' : resAcc = acc0 ++ ty' :: rtys := by
      rw [hacc, List.append_assoc, List.singleton_append]
    refine ⟨hEnvF, ty' :: rtys, hacc', ?_, .cons ⟨hres, hP⟩ hrel⟩
    simp only [LMonoTys.resolveAliases, bind, Except.bind, hres, hresolve, pure,
      Except.pure]

/-- A successful `resolveKnownTys` leaves the environment unchanged and returns
    the alias resolutions of the given types; each resolution is
    alias-equivalent to its type and is a registered instance. -/
theorem resolveKnownTys_ok_inv (C : Core.Expression.TyContext)
    (errf : LMonoTy → Std.Format) (tys : LMonoTys)
    (Env EnvF : Core.Expression.TyEnv) (rs : LMonoTys)
    (h : resolveKnownTys C errf tys Env = .ok (rs, EnvF)) :
    EnvF = Env ∧ LMonoTys.resolveAliases tys Env = .ok (rs, Env) ∧
      List.Rel₂ (fun ty ty' => LMonoTy.resolveAliases ty Env = .ok (ty', Env) ∧
          AliasEquiv Env.context.aliases ty ty' ∧
          isInstanceOfKnownType ty' C = true)
        tys rs := by
  unfold resolveKnownTys at h
  have hspec := resolveAliasesFold_spec (isInstanceOfKnownType · C = true) _
    ?hstep tys Env EnvF [] rs h
  · obtain ⟨hEnvF, rtys, hacc, hresolve, hrel⟩ := hspec
    rw [List.nil_append] at hacc
    subst hacc
    refine ⟨hEnvF, hresolve, hrel.imp fun ty ty' hr => ⟨hr.1, ?_, hr.2⟩⟩
    exact
      (LMonoTy.resolveAliases_sourceTyResolves (T := CoreLParams) ty Env ty' Env
        hr.1).aliasEquiv
  · intro acc ty res hs
    simp only [bind, Except.bind] at hs
    elim_err hs with vra hra
    obtain ⟨rty, rEnv⟩ := vra
    elim_err hs with hknown
    simp only [Except.ok.injEq] at hs
    have hknown' : isInstanceOfKnownType rty C = true := by simpa using hknown
    exact ⟨rty, rEnv, hra, hknown', hs.symm⟩

/-! ### Registered primitive types -/

/-- When every primitive literal's type is a registered instance, `bool` is registered with
    no parameters. -/
theorem knownTypes_bool_of_literalTys {ks : Lambda.KnownTypes}
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      Lambda.LMonoTy.knownInstance c.ty ks = true) :
    ks["bool"]? = some 0 := by
  have hbool : LMonoTy.knownInstance (.tcons "bool" []) ks = true :=
    h_lit (.boolConst true) rfl
  have hc := (knownInstance_tcons_inv ks "bool" [] hbool).1
  simp only [KnownTypes.contains, Identifiers.contains, KnownType.arity, List.length_nil] at hc
  cases hv : ks["bool"]? with
  | none => simp only [hv, Bool.false_eq_true] at hc
  | some i =>
    simp only [hv, beq_iff_eq] at hc
    rw [hc]

/-! ### Properties of a function's rigid renaming -/

/-- A function's rigid renaming pairs its type parameters, in order, with distinct
    rigid-prefixed constants that are neither registered types nor names of `scope` or
    `tyNames ()`. -/
theorem Function.rigidNames_fresh (scope : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (func : Function) (tyNames : Unit → List String) :
    RigidNamesPrefixed (Function.rigidNames scope C func tyNames) ∧
      ((Function.rigidNames scope C func tyNames).map Prod.snd).Nodup ∧
      RigidNamesFresh C.knownTypes (Function.rigidNames scope C func tyNames) ∧
      (Function.rigidNames scope C func tyNames).map Prod.fst = func.typeArgs ∧
      ∀ p ∈ Function.rigidNames scope C func tyNames, p.2 ∉ scope.get ∧ p.2 ∉ tyNames () :=
  have hspec := rigidNamesAvoiding_spec C scope (Thunk.pure ∅) _ tyNames func.typeArgs
  ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1,
    fun p hp => (hspec.2.2.2.2 p hp).imp_right (·.2)⟩

/-- A function's rigid renaming, minted against a set `scope` holding every type name in scope
    in `C` and `Env`, is chosen against the names in scope and the names `tyNames ()`. -/
theorem Function.rigidNames_spec (scope : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (func : Function)
    (tyNames : Unit → List String) (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ scope.get) :
    ScopeRigid C Env (tyNames ()) func.typeArgs (Function.rigidNames scope C func tyNames) :=
  ScopeRigid.of_cover C Env scope _ _ tyNames _ fun _ => hcov

/-- When `tyNames ()` includes every type name the function mentions (`Function.tyNames` of the
    types it writes), no annotation of its expressions names a constant of its rigid
    renaming. -/
theorem Function.rigidNames_annots (scope : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (func : Function) (tyNames : Unit → List String)
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tyNames ()) :
    ∀ e ∈ func.exprs, allExprTys
      (mtyAllTyConsNames (notRigidConst (Function.rigidNames scope C func tyNames))) e =
        true := by
  intro e he
  rw [allExprTys_eq_all_exprAnnotTys]
  refine List.all_eq_true.mpr fun t ht => mtyAllTyConsNames_notRigidConst_of_not_mem ?_
  intro p hp hn
  refine ((Function.rigidNames_fresh scope C func tyNames).2.2.2.2 p hp).2 (htn _ ?_)
  unfold Function.tyNames LFuncDefined.annotTys
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ?_, hn⟩))
  exact List.mem_flatMap.mpr ⟨e, he, ht⟩

/-- When `tyNames ()` includes every type name the function mentions (`Function.tyNames` of the
    types it writes), no literal's type in its expressions names a constant of its rigid
    renaming. -/
theorem Function.rigidNames_consts (scope : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (func : Function) (tyNames : Unit → List String)
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tyNames ()) :
    ∀ e ∈ func.exprs, ConstTysFixed (Function.rigidNames scope C func tyNames) e := by
  intro e he
  refine ConstTysFixed_of_litTyNames e fun p hp hn => ?_
  refine ((Function.rigidNames_fresh scope C func tyNames).2.2.2.2 p hp).2 (htn _ ?_)
  unfold Function.tyNames
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, hn⟩)

/-! ### The type a measure is checked at -/

/-- A measure that is not a bare variable is checked at `int`. -/
theorem Function.measureTy_of_ne_fvar (C : Core.Expression.TyContext)
    (sig : @LMonoTySignature Unit) (m : Core.Expression.Expr)
    (h : ∀ mid x ann, m ≠ .fvar mid x ann) :
    Function.measureTy C sig m = .int := by
  cases m
  case fvar mid x ann => exact absurd rfl (h mid x ann)
  all_goals rfl

/-- A measure is checked at `int` or at the type of a formal. -/
theorem Function.measureTy_int_or_mem (C : Core.Expression.TyContext)
    (sig : @LMonoTySignature Unit) (m : Core.Expression.Expr) :
    Function.measureTy C sig m = .int ∨ Function.measureTy C sig m ∈ sig.values := by
  unfold Function.measureTy
  split
  · split
    · rename_i hfind
      split
      · exact Or.inr (ListMap.find?_mem_values sig hfind)
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- The skolemized measure type is closed when every free type variable of the formals' types is
    renamed. -/
theorem Function.freeVars_skolemizeTy_measureTy (C : Core.Expression.TyContext)
    (sig : @LMonoTySignature Unit) (σ : RigidNames) (m : Core.Expression.Expr)
    (hnud : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst) :
    LMonoTy.freeVars (skolemizeTy σ (Function.measureTy C sig m)) = [] := by
  apply LMonoTy.freeVars_skolemizeTy_eq_nil
  intro v hv
  rcases Function.measureTy_int_or_mem C sig m with hint | hmem
  · rw [hint] at hv
    simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv
  · exact hnud v (LMonoTys.freeVars_mem_subset hmem hv)

/-- Registering rigid constants leaves the type a measure is checked at unchanged. -/
theorem Function.measureTy_addSkolemTypes (C : Core.Expression.TyContext) (σ : RigidNames) :
    Function.measureTy (addSkolemTypes C σ) = Function.measureTy C := by
  funext sig m
  rfl

/-- Deskolemizing the skolemized measure type gives it back when that holds of every formal's
    type. -/
theorem Function.deskolemizeTy_skolemizeTy_measureTy (C : Core.Expression.TyContext)
    (sig : @LMonoTySignature Unit) {σ : RigidNames} (m : Core.Expression.Expr)
    (hpfx : RigidNamesPrefixed σ)
    (hrt : ∀ mty ∈ sig.values, deskolemizeTy σ (skolemizeTy σ mty) = mty) :
    deskolemizeTy σ (skolemizeTy σ (Function.measureTy C sig m)) = Function.measureTy C sig m := by
  rcases Function.measureTy_int_or_mem C sig m with hint | hmem
  · rw [hint, skolemizeTy_int, deskolemizeTy_int hpfx]
  · exact hrt _ hmem

/-! ### Variables a checked expression reads -/

/-- The variables of an elaborated expression that reads only formals of `sig` are named like
    formals of `sig`. -/
theorem getVars_names_subset_of_nonInputVars_nil {sig : @LMonoTySignature Unit}
    {eT : LExprT CoreLParams.mono} (hnil : Function.nonInputVars sig eT = []) :
    (LExpr.LExpr.getVars eT).map (fun x => x.name) ⊆ sig.map (fun p => p.1.name) := by
  intro n hn
  have hkeep := List.filter_eq_nil_iff.mp hnil n hn
  simpa using hkeep

/-- An identifier named like a formal of `sig` is that formal. -/
theorem mem_keys_of_name_mem {sig : @LMonoTySignature Unit} {x : CoreIdent}
    (h : x.name ∈ sig.map (fun p => p.1.name)) : x ∈ ListMap.keys sig := by
  obtain ⟨⟨⟨pn, pm⟩, pv⟩, hp, hname⟩ := List.mem_map.mp h
  obtain ⟨xn, xm⟩ := x
  simp only at hname
  subst hname
  rw [ListMap.keys_eq_map_fst]
  exact List.mem_map.mpr ⟨_, hp, rfl⟩

namespace TypeSpec

/-! ### Function typing under related scopes -/

/-- Function typing by the typechecker spec transfers to a type scope with the same lookups and
    aliases. -/
theorem FuncHasTypeExact_transport {C : LContext CoreLParams}
    {Γ Ξ : TContext Unit} {func : Function} (hR : TContext.FindEq (T := CoreLParams) Ξ Γ)
    (h : FuncHasTypeExact C Γ func) :
    FuncHasTypeExact C Ξ func where
  inputsNodup := h.inputsNodup
  typeArgsNodup := h.typeArgsNodup
  noUndeclaredVars := h.noUndeclaredVars
  typeArgsInSignature := h.typeArgsInSignature
  signatureWellKinded := fun ty hty =>
    hR.aliases ▸ h.signatureWellKinded ty hty
  bodyTyped := fun body hb =>
    HasType_FindEq C _ _ _ _ (push_FindEq _ _ _ hR) (h.bodyTyped body hb)
  measureOnlyRecursive := h.measureOnlyRecursive
  measureTyped := by
    intro m hm
    have hmt := h.measureTyped m hm
    have hfc : TContext.FindEq (T := CoreLParams) (funcContext Ξ func) (funcContext Γ func) :=
      push_FindEq _ _ _ hR
    cases m
    case fvar =>
      obtain ⟨ty, hty, hint | ⟨n, args, hc, hdt, ht⟩⟩ := hmt
      · exact ⟨ty, hty, Or.inl (HasType_FindEq C _ _ _ _ hfc hint)⟩
      · exact ⟨ty, hty, Or.inr ⟨n, args, hR.aliases ▸ hc, hdt,
          HasType_FindEq C _ _ _ _ hfc ht⟩⟩
    all_goals exact HasType_FindEq C _ _ _ _ hfc hmt
  preconditionsTyped := fun p hp =>
    HasType_FindEq C _ _ _ _ (push_FindEq _ _ _ hR) (h.preconditionsTyped p hp)
  axiomsTyped := fun a ha =>
    HasType_FindEq C _ _ _ _ (push_FindEq _ _ _ hR) (h.axiomsTyped a ha)
  annotsScoped := h.annotsScoped
  writtenAnnotsOk := fun e he =>
    writtenAnnotsOk_of_aliases_eq hR.aliases (h.writtenAnnotsOk e he)
  formalsNotFunctions := h.formalsNotFunctions
  typeArgsNotReserved := h.typeArgsNotReserved
  constrNoBody := h.constrNoBody

/-- A renaming of a function's type parameters for one context is one for any context with the
    same rigid type variables and the same variable lookups. -/
theorem FuncAlphaVariant.congr {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit}
    {func f' : Function} (hrigid : C'.rigidTypeVars = C.rigidTypeVars)
    (hscope : TContext.FindEq (T := CoreLParams) Γ' Γ) (h : FuncAlphaVariant C Γ func f') :
    FuncAlphaVariant C' Γ' func f' := by
  obtain ⟨ren, hren, rfl⟩ := h
  exact ⟨ren, TyArgRenaming.congr hrigid hscope hren, rfl⟩

/-- Renaming no type parameter leaves a function unchanged. -/
theorem LFuncDefined.renameTypeArgs_nil {T : LExprParams} (f : LFuncDefined T) :
    f.renameTypeArgs [] = f := by
  cases f
  unfold LFuncDefined.renameTypeArgs LFuncDefined.applyTypeSubst renameTyArgList
  simp only [LExpr.applyTypeSubst, LMonoTy.subst, Subst.hasEmptyScopes_ofRenaming_nil, ite_true,
    Option.map_id', List.map_id', List.lookup_nil, Option.getD_none]
  congr 1
  exact List.map_id' _

/-- A function whose type parameters all have allowed names is its only renaming. -/
theorem FuncAlphaVariant.eq_self_of_allowed {C : LContext CoreLParams} {Γ : TContext Unit}
    {func f' : Function} (hallowed : ∀ a ∈ func.typeArgs, isAllowedName a = true)
    (h : FuncAlphaVariant C Γ func f') : f' = func := by
  obtain ⟨ren, hren, rfl⟩ := h
  rw [TyArgRenaming.eq_nil_of_allowed hallowed hren]
  exact LFuncDefined.renameTypeArgs_nil func

/-- For a function whose type parameters all have allowed names, the typechecker spec
    `FuncHasType` means exactly `FuncHasTypeExact` for the function itself. -/
theorem FuncHasType_iff_of_allowed {C : LContext CoreLParams} {Γ : TContext Unit}
    {func : Function} (hallowed : ∀ a ∈ func.typeArgs, isAllowedName a = true) :
    FuncHasType C Γ func ↔ FuncHasTypeExact C Γ func := by
  constructor
  · rintro ⟨f', hv, ht⟩
    rw [← FuncAlphaVariant.eq_self_of_allowed hallowed hv]
    exact ht
  · intro ht
    have hren : TyArgRenaming C Γ func.typeArgs func.mentionedTyVars [] :=
      ⟨⟨List.nodup_nil, List.nodup_nil, fun _ hp => absurd hp List.not_mem_nil⟩,
        fun _ hp => absurd hp List.not_mem_nil⟩
    exact ⟨func, ⟨[], hren, (LFuncDefined.renameTypeArgs_nil func).symm⟩, ht⟩

end TypeSpec

/-! ### Renaming reserved type parameters -/

/-- `renameReservedTypeArgs` renames a function by its reserved renaming. -/
private theorem Function.renameReservedTypeArgs_eq (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy) :
    Function.renameReservedTypeArgs C Env func annot =
      func.renameTypeArgs (reservedTypeArgsRenaming func.typeArgs
        (fun u => func.mentionedTyVarsIn (annot u) ++ scopeTyVars C Env)) := by
  unfold Function.renameReservedTypeArgs
  exact renameReservedWith_eq_of_nil (LFuncDefined.renameTypeArgs_nil func)

/-- Renaming a function's type parameters renames the types it writes. -/
private theorem Function.annotTys_renameTypeArgs (func : Function)
    (ren : List (String × String)) :
    (func.renameTypeArgs ren).annotTys =
      func.annotTys.map (LMonoTy.subst (Subst.ofRenaming ren)) := by
  have he : ∀ e : Expression.Expr,
      exprAnnotTys (e.applyTypeSubst (Subst.ofRenaming ren)) =
        (exprAnnotTys e).map (LMonoTy.subst (Subst.ofRenaming ren)) := by
    intro e
    rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType]
    exact exprAnnotTys_mapExprTys _ e
  unfold LFuncDefined.annotTys LFuncDefined.renameTypeArgs LFuncDefined.applyTypeSubst
    Strata.DL.Util.Func.exprs
  simp only [Option.toList_map, List.map_map, List.flatMap_append, List.map_append,
    List.flatMap_map, List.map_flatMap, Function.comp_def, he]

/-- Renaming a function's type parameters keeps the type names of its literals. -/
private theorem Function.litTyNames_renameTypeArgs (func : Function)
    (ren : List (String × String)) :
    (func.renameTypeArgs ren).exprs.flatMap exprLitTyNames =
      func.exprs.flatMap exprLitTyNames := by
  have he : ∀ e : Expression.Expr,
      exprLitTyNames (e.applyTypeSubst (Subst.ofRenaming ren)) = exprLitTyNames e := by
    intro e
    rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType]
    exact exprLitTyNames_mapExprTys _ e
  unfold LFuncDefined.renameTypeArgs LFuncDefined.applyTypeSubst Strata.DL.Util.Func.exprs
  simp only [Option.toList_map, List.flatMap_append, List.flatMap_map, he]

/-- Renaming a function's type parameters renames its input types. -/
private theorem Function.renameTypeArgs_inputs_values (func : Function)
    (ren : List (String × String)) :
    (func.renameTypeArgs ren).inputs.values =
      func.inputs.values.map (LMonoTy.subst (Subst.ofRenaming ren)) := by
  show ListMap.values (func.inputs.map _) = _
  induction func.inputs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨id, mty⟩ := p
    simp only [List.map_cons, ListMap.values, ih]

/-- Renaming a function's type parameters keeps the type names of its signature. -/
private theorem Function.tyNames_renameTypeArgs (func : Function)
    (ren : List (String × String)) (annot : List LMonoTy) :
    Function.tyNames (func.renameTypeArgs ren) annot = func.tyNames annot := by
  have hsig : (func.renameTypeArgs ren).output :: (func.renameTypeArgs ren).inputs.values =
      (func.output :: func.inputs.values).map (LMonoTy.subst (Subst.ofRenaming ren)) := by
    rw [List.map_cons, Function.renameTypeArgs_inputs_values]
    rfl
  unfold Function.tyNames sigTyNames
  rw [hsig, flatMap_getTypeRefs_subst_of_ftvar (Subst.ofRenaming_ftvar _),
    Function.litTyNames_renameTypeArgs]

/-- With any list of written types, a function with its reserved type parameters renamed
    mentions the type names the original mentions. -/
theorem Function.sigTyNames_renameReservedTypeArgs (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy)
    (written : List LMonoTy) :
    (Function.renameReservedTypeArgs C Env func annot).tyNames written =
      func.tyNames written := by
  rw [Function.renameReservedTypeArgs_eq]
  exact Function.tyNames_renameTypeArgs func _ written

/-- A successful `Function.renameAndResolve` returns the function with its reserved type
    parameters renamed, the resolved signature of that renaming, and the types the function
    writes; the renaming mentions the type names the function mentions. -/
theorem Function.renameAndResolve_ok_inv {C : Core.Expression.TyContext}
    {Env : Core.Expression.TyEnv} {func : Function} {sig : CheckedSignature}
    (h : Function.renameAndResolve C Env func = .ok sig) :
    sig.func = Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys)
      ∧ Function.resolveSignature C Env sig.func = .ok (sig.output, sig.inputs)
      ∧ sig.annot.get = func.annotTys
      ∧ sig.tyNames = fun _ => func.tyNames func.annotTys := by
  unfold Function.renameAndResolve at h
  obtain ⟨⟨output, inputs⟩, hres, h⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨rfl, hres, rfl, ?_⟩
  funext
  exact Function.sigTyNames_renameReservedTypeArgs C Env func _ func.annotTys

/-- Renaming a function's reserved type parameters keeps the type names it mentions. -/
theorem Function.tyNames_renameReservedTypeArgs (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy) :
    (Function.renameReservedTypeArgs C Env func annot).tyNames
        (Function.renameReservedTypeArgs C Env func annot).annotTys =
      func.tyNames func.annotTys := by
  rw [Function.sigTyNames_renameReservedTypeArgs, Function.renameReservedTypeArgs_eq,
    Function.annotTys_renameTypeArgs]
  unfold Function.tyNames
  rw [flatMap_getTypeRefs_subst_of_ftvar (Subst.ofRenaming_ftvar _)]

/-- The checker's renaming, in `C` and `Env`, of the reserved type parameters of a function with
    distinct type parameters renames them injectively to names that neither the
    function nor the context uses. -/
theorem Function.renameReservedTypeArgs_alphaVariant (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (hnd : func.typeArgs.Nodup) :
    TypeSpec.FuncAlphaVariant C Env.context func
      (Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys)) := by
  rw [Function.renameReservedTypeArgs_eq]
  exact ⟨_, reservedTypeArgsRenaming_tyArgRenaming _ hnd mem_append_scopeTyVars, rfl⟩

/-- Renaming a function's type parameters renames the type variables of its signature. -/
private theorem Function.renameTypeArgs_sig (func : Function) (ren : List (String × String)) :
    LMonoTy.mkArrow' (func.renameTypeArgs ren).output (func.renameTypeArgs ren).inputs.values =
      LMonoTy.subst (Subst.ofRenaming ren) (LMonoTy.mkArrow' func.output func.inputs.values) := by
  have hout : (func.renameTypeArgs ren).output =
      LMonoTy.subst (Subst.ofRenaming ren) func.output := rfl
  rw [Function.renameTypeArgs_inputs_values, hout, ← subst_mkArrow']

/-- Every type variable of a function's signature is one it mentions. -/
private theorem Function.mem_mentionedTyVars_of_sig {func : Function} {v : String}
    (hv : v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values)) :
    v ∈ func.mentionedTyVars := by
  unfold LFuncDefined.mentionedTyVars LFuncDefined.mentionedTyVarsIn
    LFuncDefined.sigTyVars
  rcases freeVars_mkArrow'_cases _ v _ hv with hout | ⟨ty, hty, hvty⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hout))
  · refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ?_))
    rw [ListMap.values_eq_map_snd] at hty
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hty
    exact ⟨p, hp, hvty⟩

/-- Renaming a function's distinct type parameters injectively to names it does not mention
    (`TyArgRenamingCore`) keeps them distinct, and keeps every type variable of the signature a
    type parameter. -/
theorem Function.renameTypeArgs_sigDeclared {func : Function} {ren : List (String × String)}
    (hren : TypeSpec.TyArgRenamingCore func.typeArgs func.mentionedTyVars ren)
    (hnd : func.typeArgs.Nodup)
    (hsig : ∀ v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values),
      v ∈ func.typeArgs) :
    (func.renameTypeArgs ren).typeArgs.Nodup ∧
      ∀ v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' (func.renameTypeArgs ren).output
          (func.renameTypeArgs ren).inputs.values),
        v ∈ (func.renameTypeArgs ren).typeArgs := by
  refine ⟨renameTyArgList_nodup hnd hren fun a ha =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ha)), ?_⟩
  rw [Function.renameTypeArgs_sig]
  exact freeVars_subst_ofRenaming_mem hren.1 (fun p hp => (hren.2.2 p hp).1) hsig

/-- Conversely, after renaming a function's type parameters injectively to names it does not
    mention (`TyArgRenamingCore`), if every type variable of the renamed signature is a type
    parameter, so is every type variable of the original signature. -/
theorem Function.sigDeclared_of_renameTypeArgs {func : Function} {ren : List (String × String)}
    (hren : TypeSpec.TyArgRenamingCore func.typeArgs func.mentionedTyVars ren)
    (hsig : ∀ v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' (func.renameTypeArgs ren).output
          (func.renameTypeArgs ren).inputs.values),
        v ∈ (func.renameTypeArgs ren).typeArgs) :
    ∀ v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values),
      v ∈ func.typeArgs := by
  intro v hv
  by_cases hin : v ∈ func.typeArgs
  · exact hin
  · have hnot : v ∉ ren.map Prod.fst := by
      intro hm
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact hin (hren.2.2 p hp).1
    have hvren : v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' (func.renameTypeArgs ren).output
        (func.renameTypeArgs ren).inputs.values) := by
      rw [Function.renameTypeArgs_sig]
      exact mem_freeVars_subst_ofRenaming_of_not_mem _ hv hnot
    rcases mem_renameTyArgList (hsig v hvren) with ⟨hmem, -⟩ | ⟨p, hp, rfl⟩
    · exact absurd hmem hin
    · exact absurd (Function.mem_mentionedTyVars_of_sig hv) (hren.2.2 p hp).2

/-- After the checker's renaming, every type parameter of a function is an allowed name. -/
theorem Function.renameReservedTypeArgs_typeArgs_allowed (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy) :
    ∀ a ∈ (Function.renameReservedTypeArgs C Env func annot).typeArgs,
      isAllowedName a = true := by
  rw [Function.renameReservedTypeArgs_eq]
  exact renameTyArgList_reserved_allowed _ _

/-- A function whose type parameters are all allowed names is not renamed. -/
theorem Function.renameReservedTypeArgs_of_allowed (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy)
    (h : ∀ a ∈ func.typeArgs, isAllowedName a = true) :
    Function.renameReservedTypeArgs C Env func annot = func := by
  rw [Function.renameReservedTypeArgs_eq, reservedTypeArgsRenaming_of_allowed _ h]
  exact LFuncDefined.renameTypeArgs_nil func

/-- The checker's renaming of a function depends on its context only through the rigid type
    variables and the variables in scope. -/
theorem Function.renameReservedTypeArgs_congr {C C' : Core.Expression.TyContext}
    {Env Env' : Core.Expression.TyEnv} (func : Function) (annot : Unit → List LMonoTy)
    (hrigid : C'.rigidTypeVars = C.rigidTypeVars) (hctx : Env'.context = Env.context) :
    Function.renameReservedTypeArgs C' Env' func annot =
      Function.renameReservedTypeArgs C Env func annot := by
  unfold Function.renameReservedTypeArgs scopeTyVars
  rw [hrigid, hctx]

/-- If the renamed type parameters are distinct, so are the original ones. -/
theorem Function.typeArgs_nodup_of_renameReservedTypeArgs (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy)
    (h : (Function.renameReservedTypeArgs C Env func annot).typeArgs.Nodup) :
    func.typeArgs.Nodup := by
  rw [Function.renameReservedTypeArgs_eq] at h
  exact nodup_of_renameTyArgList h

/-- Renaming type parameters keeps a function's name, flags, attributes and formal names,
    whether it has a body and a measure, its number of axioms and its precondition metadata. -/
theorem Function.renameReservedTypeArgs_fields (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy) :
    (Function.renameReservedTypeArgs C Env func annot).name = func.name ∧
    (Function.renameReservedTypeArgs C Env func annot).isConstr = func.isConstr ∧
    (Function.renameReservedTypeArgs C Env func annot).isRecursive = func.isRecursive ∧
    (Function.renameReservedTypeArgs C Env func annot).attr = func.attr ∧
    (Function.renameReservedTypeArgs C Env func annot).inputs.keys = func.inputs.keys ∧
    (Function.renameReservedTypeArgs C Env func annot).body.isSome = func.body.isSome ∧
    (Function.renameReservedTypeArgs C Env func annot).measure.isSome = func.measure.isSome ∧
    (Function.renameReservedTypeArgs C Env func annot).axioms.length = func.axioms.length ∧
    (Function.renameReservedTypeArgs C Env func annot).preconditions.map (·.md) =
      func.preconditions.map (·.md) := by
  rw [Function.renameReservedTypeArgs_eq]
  refine ⟨rfl, rfl, rfl, rfl, LFuncDefined.renameTypeArgs_inputs_keys func _, ?_, ?_, ?_, ?_⟩
  · exact Option.isSome_map
  · exact Option.isSome_map
  · exact List.length_map _
  · show (func.preconditions.map _).map _ = _
    rw [List.map_map]
    rfl

namespace Function

/-- A function-name freshness check that succeeds means the context has no function of that
    name. -/
theorem checkNameFresh_ok {C : Core.Expression.TyContext} {func : Function} {u : Unit}
    (h : checkNameFresh C func = .ok u) : func.name.name ∉ C.functions := by
  intro hmem
  simp only [checkNameFresh, hmem, ite_true] at h
  contradiction

end Function

/-- Renaming type parameters keeps the names of the inputs. -/
private theorem Function.renameReservedTypeArgs_inputs_keys (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy) :
    (Function.renameReservedTypeArgs C Env func annot).inputs.keys = func.inputs.keys := by
  unfold Function.renameReservedTypeArgs
  rcases renameReservedWith_cases func.typeArgs
    (fun u => func.mentionedTyVarsIn (annot u) ++ scopeTyVars C Env)
    func.renameTypeArgs func with ⟨heq, -⟩ | heq
  · rw [heq]
  · rw [heq]
    exact Lambda.LFuncDefined.renameTypeArgs_inputs_keys _ _

/-- If `Function.typeCheck` succeeds, the function's inputs have no duplicate names. -/
theorem Function.typeCheck_inputs_nodup (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (func : Function) (func' : Function) (Env' : Core.Expression.TyEnv) :
    Function.typeCheck C Env func = .ok (func', Env') → func.inputs.keys.Nodup := by
  intro h
  rw [← Function.renameReservedTypeArgs_inputs_keys C Env]
  have hsig : ∃ sig, Function.renameAndResolve C Env func = .ok sig := by
    simp only [Function.typeCheck, bind, Except.bind] at h
    elim_err h with v hIn
    simp only [Function.typeCheckIn, bind, Except.bind] at hIn
    elim_err hIn
    elim_err hIn with sig hsig
    exact ⟨sig, hsig⟩
  obtain ⟨sig, hsig⟩ := hsig
  unfold Function.renameAndResolve Function.resolveSignature at hsig
  simp only [bind, Except.bind, Thunk.get] at hsig
  by_cases hnd : (Function.renameReservedTypeArgs C Env func
      (fun _ => func.annotTys)).inputs.keys.Nodup
  · exact hnd
  · exfalso
    simp only [hnd, decide_false, Bool.not_false, ite_true, reduceCtorEq] at hsig

/-! ### Function parameter scopes -/

/-- Every type the skolemized formals scope stores is closed, when the signature's free type
    variables are all skolemized. -/
theorem skolemScope_closed (σ : RigidNames) (sigR : @LMonoTySignature Unit)
    (h_nud : ∀ v ∈ LMonoTys.freeVars sigR.values, v ∈ σ.map Prod.fst) :
    ∀ ty ∈ (skolemScope σ sigR).values, LTy.freeVars ty = [] ∧ LTy.boundVars ty = [] := by
  show ∀ ty ∈ (Strata.Util.HMap.ofList
      (sigR.map (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2))))).values, _
  intro ty hty
  have hmem := Strata.Util.HMap.mem_values_ofList _ ty hty
  rw [List.map_map (l := sigR), List.mem_map (l := sigR)] at hmem
  obtain ⟨q, hq, hqe⟩ := hmem
  obtain ⟨id, mty⟩ := q
  simp only [Function.comp_apply] at hqe
  subst hqe
  have hmv : mty ∈ sigR.values := by
    rw [ListMap.values_eq_map_snd, List.mem_map (l := sigR)]
    exact ⟨(id, mty), hq, rfl⟩
  have hfv : LMonoTy.freeVars (skolemizeTy σ mty) = [] :=
    LMonoTy.freeVars_skolemizeTy_eq_nil σ mty
      (fun w hw => h_nud w (LMonoTys.freeVars_mem_subset hmv hw))
  exact ⟨by simp only [LTy.freeVars, hfv, List.removeAll, List.filter_nil], rfl⟩

/-- The environment a function's expressions are checked in is the skolemized formals scope
    pushed onto the ambient scope stack. -/
theorem formalsEnv_eq_push (Env : Expression.TyEnv) (σ : RigidNames)
    (sigR : @LMonoTySignature Unit) :
    Function.formalsEnv Env σ sigR
      = (Env.pushEmptyContext).addInNewestContext (T := CoreLParams) (skolemScope σ sigR) := by
  unfold Function.formalsEnv
  rfl

/-- The formals environment's scope stack is the skolemized formals scope on top of the ambient
    stack. -/
theorem formalsEnv_types (Env : Expression.TyEnv) (σ : RigidNames)
    (sigR : @LMonoTySignature Unit) :
    (Function.formalsEnv Env σ sigR).context.types
      = ((skolemScope σ sigR).union HMap.empty) :: Env.context.types := by
  rw [formalsEnv_eq_push Env σ sigR]
  simp only [TEnv.addInNewestContext, TEnv.pushEmptyContext, TEnv.updateContext,
    TEnv.context, HMaps.push, HMaps.addInNewest]

/-- The formals environment is well formed when the ambient one is and the formals' types have
    only the rigid parameters as type variables. -/
theorem formalsEnv_TEnvWF (Env : Expression.TyEnv) (σ : RigidNames)
    (sigR : @LMonoTySignature Unit)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_nud : ∀ v ∈ LMonoTys.freeVars sigR.values, v ∈ σ.map Prod.fst) :
    LExpr.TEnvWF (T := CoreLParams) (Function.formalsEnv Env σ sigR) :=
  pushEmptyContext_addInNewestContext_preserves_TEnvWF (T := CoreLParams)
    Env (skolemScope σ sigR) h_env
    (skolemScope_closed σ sigR h_nud)

/-- The formals environment has only monotype schemes when the ambient one does. -/
theorem formalsEnv_MonoScope (Env : Expression.TyEnv) (σ : RigidNames)
    (sigR : @LMonoTySignature Unit) (h_mono : MonoScope Env.context) :
    MonoScope (Function.formalsEnv Env σ sigR).context := by
  intro z tz hz
  rw [formalsEnv_eq_push Env σ sigR,
    ← (push_addInNewestContext_FindEq (T := CoreLParams) Env (skolemScope σ sigR)).find? z] at hz
  exact MonoScope_pushed Env.context σ sigR h_mono z tz hz

/-- The formals environment stores only closed schemes when the ambient one does and the formals'
    types have only the rigid parameters as type variables. -/
theorem formalsEnv_typesClosed (Env : Expression.TyEnv) (σ : RigidNames)
    (sigR : @LMonoTySignature Unit)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_nud : ∀ v ∈ LMonoTys.freeVars sigR.values, v ∈ σ.map Prod.fst) :
    LExpr.checkContextTypesClosed (T := CoreLParams) (Function.formalsEnv Env σ sigR) := by
  have hscope := skolemScope_closed σ sigR h_nud
  rw [LExpr.checkContextTypesClosed_iff_values (T := CoreLParams) _]
  intro ty hty
  rw [formalsEnv_types Env σ sigR] at hty
  have hsplit : ty ∈ HMap.values ((skolemScope σ sigR).union HMap.empty) ∨
      ty ∈ HMaps.values Env.context.types := by
    simpa only [HMaps.values, List.mem_append] using hty
  rcases hsplit with h1 | h2
  · obtain ⟨k, hk⟩ := (HMap.mem_values_iff_find? _ ty).mp h1
    rw [HMap.find?_union, HMap.find?_empty, Option.none_or] at hk
    exact (hscope ty (HMap.find?_mem_values _ hk)).1
  · exact (LExpr.checkContextTypesClosed_iff_values (T := CoreLParams) Env).mp h_closed ty h2

/-- Pushing the formals scope keeps the aliases resolved. -/
theorem formalsEnv_AliasesResolved (Env : Expression.TyEnv) (σ : RigidNames)
    (sigR : @LMonoTySignature Unit)
    (h_resolved : Lambda.TContext.AliasesResolved Env.context) :
    Lambda.TContext.AliasesResolved (Function.formalsEnv Env σ sigR).context := by
  intro a ha
  apply h_resolved a
  simpa only [Function.formalsEnv, skolemScope, TEnv.addInNewestContext, TEnv.pushEmptyContext,
    TEnv.updateContext, TEnv.context] using ha

/-- Pushing the formals scope keeps the type aliases. -/
theorem formalsEnv_aliases (Env : Expression.TyEnv) (σ : RigidNames)
    (sigR : @LMonoTySignature Unit) :
    (Function.formalsEnv Env σ sigR).context.aliases = Env.context.aliases := by
  simp only [Function.formalsEnv, skolemScope, TEnv.addInNewestContext, TEnv.pushEmptyContext,
    TEnv.updateContext, TEnv.context]

/-- A closed type scheme is fixed by every substitution. -/
theorem LTy.subst_of_closed (S : Subst) (ty : LTy) (hfv : LTy.freeVars ty = []) :
    LTy.subst S ty = ty := by
  cases ty with
  | forAll xs body =>
    show LTy.forAll xs (LMonoTy.subst (LTy.subst.go xs S) body) = LTy.forAll xs body
    rw [LExpr.subst_go_eq_self_of_irrelevant_keys S xs body]
    intro k _ hk hkfv
    have hfv' : (LMonoTy.freeVars body).removeAll xs = [] := hfv
    have hmem : k ∈ (LMonoTy.freeVars body).removeAll xs := by
      simp [List.removeAll, hkfv, hk]
    rw [hfv'] at hmem
    exact absurd hmem List.not_mem_nil

/-- The skolemized formals scope binds each formal at the skolemization of its declared
    scheme. -/
theorem find?_skolemScope (σ : RigidNames) (sig : @LMonoTySignature Unit) (x : CoreIdent) :
    (skolemScope σ sig).find? x
      = ((formalsScope sig).find? x).map (mapLTyTys (skolemizeTy σ)) := by
  have hlist : sig.map (fun p => ((p.1 : CoreIdent), LTy.forAll [] (skolemizeTy σ p.2)))
      = (sig.map (fun p => ((p.1 : CoreIdent), LTy.forAll [] p.2))).map
          (fun p => (p.1, mapLTyTys (skolemizeTy σ) p.2)) := by
    rw [List.map_map (l := sig)]
    rfl
  show HMap.find?
      (HMap.ofList (sig.map (fun p => (p.1, LTy.forAll [] (skolemizeTy σ p.2))))) x = _
  rw [hlist, HMap.find?_ofList_map_snd]

/-- Every scheme `formalsScope sig` stores is the trivial scheme over one of `sig`'s types. -/
theorem formalsScope_find?_mem (sig : @LMonoTySignature Unit) (x : CoreIdent) (t : LTy)
    (h : (formalsScope sig).find? x = some t) :
    ∃ mty ∈ sig.values, t = LTy.forAll [] mty := by
  unfold formalsScope at h
  have hv := HMap.mem_values_ofList _ t (HMap.find?_mem_values _ h)
  rw [List.map_map (l := sig), List.mem_map (l := sig)] at hv
  obtain ⟨p, hp, hpe⟩ := hv
  refine ⟨p.2, ?_, hpe.symm⟩
  rw [ListMap.values_eq_map_snd, List.mem_map (l := sig)]
  exact ⟨p, hp, rfl⟩

/-- For a scope lookup-equal to closed monotype ambient types, substituting its alias-resolved
    types gives the lookups of the alias-resolved ambient scope. -/
theorem subst_dealias_find?_of_closed (S : Subst) (Env : Expression.TyEnv) (Γ : TContext Unit)
    (hΓ : TContext.FindEq (T := CoreLParams) Γ Env.context)
    (h_aw : TContext.AliasesWF Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (x : Expression.Ident) :
    (TContext.subst Γ.dealias S).types.find? x = Env.context.dealias.types.find? x := by
  rw [TContext.subst_dealias_find?, hΓ.1 x, TContext.resolveScheme_congr (T := CoreLParams) hΓ.2,
    TContext.dealias_find? (T := CoreLParams)]
  cases hamb : Env.context.types.find? x with
  | none => rfl
  | some t =>
    obtain ⟨vs, mty⟩ := t
    have hvs : vs = [] := h_mono x _ hamb
    subst hvs
    have hfv := TContext.resolveScheme_freeVars_subset (T := CoreLParams) h_aw (.forAll [] mty)
    rw [LExpr.ctx_closed_of_check (T := CoreLParams) Env h_closed x _ hamb] at hfv
    have hclosed : LTy.freeVars (Env.context.resolveScheme (.forAll [] mty)) = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun v hv => absurd (hfv v hv) List.not_mem_nil
    simp only [Option.map_some]
    rw [LTy.subst_of_closed S _ hclosed]

/-- Pushing a scope of alias-resolved parameter types commutes with resolving the context's types
    and dropping its aliases. -/
theorem formalsScope_push_dealias_FindEq (Γ : TContext Unit) (sig : @LMonoTySignature Unit)
    (h_res : ∀ mty ∈ sig.values, Γ.resolveTy mty = mty) :
    TContext.FindEq (T := CoreLParams) { Γ with types := Γ.types.push (formalsScope sig) }.dealias
      { Γ.dealias with types := Γ.dealias.types.push (formalsScope sig) } := by
  refine ⟨fun x => ?_, rfl⟩
  rw [TContext.dealias_find? (T := CoreLParams),
    TContext.resolveScheme_congr (T := CoreLParams)
      (Γ := { Γ with types := Γ.types.push (formalsScope sig) }) (Γ' := Γ) rfl]
  show (HMaps.find? (formalsScope sig :: Γ.types) x).map Γ.resolveScheme
      = HMaps.find? (formalsScope sig :: Γ.dealias.types) x
  cases hd : (formalsScope sig).find? x with
  | none =>
    simp only [HMaps.find?, hd]
    exact (TContext.dealias_find? (T := CoreLParams) Γ x).symm
  | some t =>
    obtain ⟨mty, hmty, rfl⟩ := formalsScope_find?_mem sig x t hd
    simp only [HMaps.find?, hd, Option.map_some, TContext.resolveScheme_forAll, h_res mty hmty]

/-- `FuncHasTypeExact` is invariant under changing the context's `idents` field. -/
theorem TypeSpec.FuncHasTypeExact_idents_irrel
    (C : Expression.TyContext) (j : Identifiers Unit)
    (Γ : TContext Unit) (func : Function)
    (h : FuncHasTypeExact {C with idents := j} Γ func) : FuncHasTypeExact C Γ func where
  inputsNodup := h.inputsNodup
  typeArgsNodup := h.typeArgsNodup
  noUndeclaredVars := h.noUndeclaredVars
  typeArgsInSignature := h.typeArgsInSignature
  signatureWellKinded := fun ty hty =>
    validSourceTy_idents_irrel (h.signatureWellKinded ty hty)
  bodyTyped := fun body hb =>
    HasType_idents_irrel C j _ _ _ (h.bodyTyped body hb)
  measureOnlyRecursive := h.measureOnlyRecursive
  measureTyped := by
    intro m hm
    have hmt := h.measureTyped m hm
    cases m
    case fvar =>
      obtain ⟨ty, hty, hint | ⟨n, args, hc, hdt, ht⟩⟩ := hmt
      · exact ⟨ty, hty, Or.inl (HasType_idents_irrel C j _ _ _ hint)⟩
      · exact ⟨ty, hty, Or.inr ⟨n, args, hc, hdt,
          HasType_idents_irrel C j _ _ _ ht⟩⟩
    all_goals exact HasType_idents_irrel C j _ _ _ hmt
  preconditionsTyped := fun p hp =>
    HasType_idents_irrel C j _ _ _ (h.preconditionsTyped p hp)
  axiomsTyped := fun a ha =>
    HasType_idents_irrel C j _ _ _ (h.axiomsTyped a ha)
  annotsScoped := h.annotsScoped
  writtenAnnotsOk := fun e he =>
    writtenAnnotsOk_idents_irrel C j _ e (h.writtenAnnotsOk e he)
  formalsNotFunctions := h.formalsNotFunctions
  typeArgsNotReserved := h.typeArgsNotReserved
  constrNoBody := h.constrNoBody

/-- Expression well-typedness does not depend on the context's `idents` field. -/
theorem TypeSpec.ExprWellTyped.withIdents {C : Expression.TyContext} {j : Identifiers Unit}
    {ts : TypeScopes} {e : Expression.Expr} {mty : LMonoTy}
    (h : ExprWellTyped {C with idents := j} ts e mty) : ExprWellTyped C ts e mty :=
  ⟨h.1, h.2.1, ScopesAnnotAgree.of_functions_eq (C := {C with idents := j}) rfl h.2.2⟩

/-- Function well-typedness does not depend on the context's `idents` field. -/
theorem TypeSpec.FuncWellTyped.withIdents {C : Expression.TyContext} {j : Identifiers Unit}
    {ts : TypeScopes} {func : Function} (h : FuncWellTyped {C with idents := j} ts func) :
    FuncWellTyped C ts func where
  inputsNodup := h.inputsNodup
  typeArgsNodup := h.typeArgsNodup
  noUndeclaredVars := h.noUndeclaredVars
  typeArgsInSignature := h.typeArgsInSignature
  signatureWellKinded := h.signatureWellKinded
  bodyTyped := fun body hb => (h.bodyTyped body hb).withIdents
  measureOnlyRecursive := h.measureOnlyRecursive
  measureTyped := by
    intro m hm
    have hmt := h.measureTyped m hm
    cases m
    case fvar =>
      obtain ⟨ty, hty, hint | ⟨n, args, hc, hdt, ht⟩⟩ := hmt
      · exact ⟨ty, hty, Or.inl hint.withIdents⟩
      · exact ⟨ty, hty, Or.inr ⟨n, args, hc, hdt, ht.withIdents⟩⟩
    all_goals exact hmt.withIdents
  preconditionsTyped := fun p hp => (h.preconditionsTyped p hp).withIdents
  axiomsTyped := fun ax hax => (h.axiomsTyped ax hax).withIdents
  annotsScoped := h.annotsScoped
  constrNoBody := h.constrNoBody

end Core

end -- public section
