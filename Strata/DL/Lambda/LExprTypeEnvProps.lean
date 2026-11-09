/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LExprAliasFree
import all Strata.DL.Lambda.LExprAliasFree
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.LTyUnifyProps
public import Strata.DL.Lambda.LTyWF
public import Strata.DL.Lambda.LTyWFProps
import all Strata.DL.Lambda.LTyWF
import all Strata.DL.Lambda.LTyWFProps
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.IdentifiersProps
import all Strata.Util.ExceptProps
import all Strata.Util.HMapsProps
import all Strata.Util.ListMapProps
import all Strata.Util.ListUtilsProps
import all Strata.Util.StringProps

/-! # Properties of Lambda type environments

Key theorems: `AliasEquiv.mono` and `AliasEquiv.freeVars_iff` (alias
equivalence survives more aliases and keeps free type variables),
`LMonoTys.resolveAliases_eq_of_FreshExtension` (if a list of types resolves to
registered instances, adding aliases whose names are unregistered does not
change its resolution), `LMonoTy.knownInstance_iff_getTypeConsArities` (a type
is registered exactly when every constructor name and arity it uses is), and
`addTypeAlias_stored` (when the existing alias bodies are alias-free, declaring
an alias stores an alias-free, registered body). -/

namespace Lambda

open Std (ToFormat)
open Strata
open Strata.Util (HMap HMaps)

public section

attribute [local simp] Pure.pure Except.pure

/-- Resolving a scheme resolves its body. -/
theorem TContext.resolveScheme_forAll {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] [ToFormat IDMeta] (Γ : TContext IDMeta)
    (vs : List TyIdentifier) (mty : LMonoTy) :
    Γ.resolveScheme (.forAll vs mty) = .forAll vs (Γ.resolveTy mty) := by
  simp only [TContext.resolveScheme, mapLTyTys]

/-- Resolving `mty` in the fresh environment built from `Γ` succeeds with
    `Γ.resolveTy mty` and leaves that environment unchanged. -/
theorem TContext.resolveTy_resolveAliases {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (Γ : TContext T.IDMeta) (mty : LMonoTy) :
    LMonoTy.resolveAliases mty
        ({ genEnv := { context := Γ, genState := TState.init } }
          : TEnv T.IDMeta) =
      .ok (Γ.resolveTy mty,
        { genEnv := { context := Γ, genState := TState.init } }) := by
  obtain ⟨r, hr⟩ := LMonoTy.resolveAliases_isOk mty
    ({ genEnv := { context := Γ, genState := TState.init } } : TEnv T.IDMeta)
  simp only [TContext.resolveTy, hr]

/-- A type is alias-equivalent to its alias resolution against `Γ`. -/
theorem TContext.aliasEquiv_resolveTy {T : LExprParams} [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [ToFormat T.IDMeta] (Γ : TContext T.IDMeta)
    (mty : LMonoTy) :
    AliasEquiv Γ.aliases mty (Γ.resolveTy mty) :=
  LExpr.resolveAliases_aliasEquiv (Γ := Γ) mty _ _ _
    (TContext.resolveTy_resolveAliases Γ mty) rfl

/-- Looking up `x` in the alias-resolved context gives the scheme `Γ` holds for
    `x`, with its body resolved. -/
theorem TContext.resolveTypes_find? {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] [ToFormat IDMeta] {Γ : TContext IDMeta}
    {x : Identifier IDMeta} {vs : List TyIdentifier} {mty : LMonoTy}
    (h : Γ.types.find? x = some (.forAll vs mty)) :
    Γ.resolveTypes.types.find? x = some (.forAll vs (Γ.resolveTy mty)) := by
  simp only [TContext.resolveTypes, Strata.Util.HMaps.find?_mapValues, h,
    Option.map_some, TContext.resolveScheme_forAll]

/-- Resolving a signature keeps its names. -/
theorem TContext.resolveSig_keys {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] [ToFormat IDMeta] {α : Type} (Γ : TContext IDMeta)
    (sig : ListMap α LMonoTy) : (Γ.resolveSig sig).keys = sig.keys := by
  simp only [TContext.resolveSig, ListMap.keys_eq_map_fst,
    ListMap.values_eq_map_snd]
  have hlen : (sig.map Prod.fst).length ≤
      ((sig.map Prod.snd).map Γ.resolveTy).length := by
    rw [List.length_map, List.length_map (as := sig),
      List.length_map (as := sig)]
    exact Nat.le_refl _
  exact (ListMap.keys_eq_map_fst _).trans (List.map_fst_zip hlen)

/-- Resolving a signature resolves each of its types. -/
theorem TContext.resolveSig_values {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] [ToFormat IDMeta] {α : Type} (Γ : TContext IDMeta)
    (sig : ListMap α LMonoTy) :
    (Γ.resolveSig sig).values = sig.values.map Γ.resolveTy := by
  simp only [TContext.resolveSig, ListMap.keys_eq_map_fst,
    ListMap.values_eq_map_snd]
  have hlen : ((sig.map Prod.snd).map Γ.resolveTy).length ≤
      (sig.map Prod.fst).length := by
    rw [List.length_map, List.length_map (as := sig),
      List.length_map (as := sig)]
    exact Nat.le_refl _
  exact (ListMap.values_eq_map_snd _).trans (List.map_snd_zip hlen)

/-- `FreshExtension` is transitive. -/
theorem TypeAlias.FreshExtension.trans {A B D : List TypeAlias}
    (h1 : TypeAlias.FreshExtension A B) (h2 : TypeAlias.FreshExtension B D) :
    TypeAlias.FreshExtension A D := by
  obtain ⟨n1, rfl, hf1⟩ := h1
  obtain ⟨n2, rfl, hf2⟩ := h2
  refine ⟨n2 ++ n1, (List.append_assoc ..).symm, ?_⟩
  intro a ha b hb
  rcases List.mem_append.mp ha with h | h
  · exact hf2 a h b (List.mem_append_right _ hb)
  · exact hf1 a h b hb

/-- Every alias of an `AliasesWF` context is well formed. -/
theorem TContext.AliasesWF.mem {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] {Γ : TContext IDMeta}
    (h : TContext.AliasesWF Γ) :
    ∀ a, a ∈ Γ.aliases → TypeAlias.WF a := h

/-- Alias well-formedness transfers to a context with the same alias list. -/
theorem TContext.AliasesWF.of_aliases_eq {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] {Γ Δ : TContext IDMeta}
    (heq : Δ.aliases = Γ.aliases) (h_awf : TContext.AliasesWF Γ) :
    TContext.AliasesWF Δ := by
  intro al hal
  exact h_awf al (heq ▸ hal)

/-- A type context is a stack of variable-type scopes plus a list of aliases;
    one with no aliases is determined by its scopes. -/
theorem TContext.eq_of_aliases_nil {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] {Γ : TContext IDMeta} (h : Γ.aliases = []) :
    Γ = { types := Γ.types } := by
  cases Γ
  cases h
  rfl

/-- A list equal to `sub` is a fresh extension of `sub`. -/
theorem TypeAlias.FreshExtension.of_eq {sub sup : List TypeAlias}
    (h : sup = sub) :
    TypeAlias.FreshExtension sub sup :=
  ⟨[], by simp [h], by simp⟩

/-- Prepending an alias with a new name is a fresh extension. -/
theorem TypeAlias.FreshExtension.cons {sub : List TypeAlias} {a : TypeAlias}
    (h : ∀ b ∈ sub, b.name ≠ a.name) :
    TypeAlias.FreshExtension sub (a :: sub) := by
  refine ⟨[a], rfl, ?_⟩
  intro x hx b hb
  obtain rfl : x = a := by simpa using hx
  exact (h b hb).symm

mutual
/-- Alias equivalence holds under any larger alias list. -/
theorem AliasEquiv.mono {A A' : List TypeAlias} {a b : LMonoTy}
    (hsub : A ⊆ A') (h : AliasEquiv A a b) : AliasEquiv A' a b := by
  match h with
  | .refl => exact .refl
  | .expand hexp =>
    obtain ⟨al, hmem, hname, hlen, heq⟩ := hexp
    exact .expand ⟨al, hsub hmem, hname, hlen, heq⟩
  | .collapse hexp =>
    obtain ⟨al, hmem, hname, hlen, heq⟩ := hexp
    exact .collapse ⟨al, hsub hmem, hname, hlen, heq⟩
  | .cong_tcons hargs => exact .cong_tcons (AliasEquivList.mono hsub hargs)
  | .trans h1 h2 =>
    exact .trans (AliasEquiv.mono hsub h1) (AliasEquiv.mono hsub h2)

/-- Listwise alias equivalence holds under any larger alias list. -/
private theorem AliasEquivList.mono {A A' : List TypeAlias} {as bs : LMonoTys}
    (hsub : A ⊆ A') (h : AliasEquivList A as bs) : AliasEquivList A' as bs := by
  match h with
  | .nil => exact .nil
  | .cons hhd htl =>
    exact .cons (AliasEquiv.mono hsub hhd) (AliasEquivList.mono hsub htl)
end

/-- Every list of types is alias-equivalent to itself. -/
theorem AliasEquivList.refl (A : List TypeAlias) (ts : LMonoTys) :
    AliasEquivList A ts ts := by
  induction ts with
  | nil => exact .nil
  | cons t rest ih => exact .cons .refl ih

/-- Every type of a list is alias-equivalent, against `Γ`'s aliases, to its
    alias resolution. -/
theorem AliasEquivList.map_resolveTy {T : LExprParams} [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] (Γ : TContext T.IDMeta)
    (ts : LMonoTys) :
    AliasEquivList Γ.aliases ts (ts.map Γ.resolveTy) := by
  induction ts with
  | nil => exact .nil
  | cons t rest ih => exact .cons (TContext.aliasEquiv_resolveTy Γ t) ih

mutual
/-- With no aliases, alias equivalence is equality. -/
theorem AliasEquiv.eq_of_nil {a b : LMonoTy} (h : AliasEquiv [] a b) :
    a = b := by
  match h with
  | .refl => rfl
  | .expand hexp =>
    obtain ⟨_, hmem, -⟩ := hexp
    exact absurd hmem List.not_mem_nil
  | .collapse hexp =>
    obtain ⟨_, hmem, -⟩ := hexp
    exact absurd hmem List.not_mem_nil
  | .cong_tcons hargs => rw [AliasEquivList.eq_of_nil hargs]
  | .trans h1 h2 =>
    exact (AliasEquiv.eq_of_nil h1).trans (AliasEquiv.eq_of_nil h2)

/-- With no aliases, listwise alias equivalence is equality. -/
private theorem AliasEquivList.eq_of_nil {as bs : LMonoTys}
    (h : AliasEquivList [] as bs) : as = bs := by
  match h with
  | .nil => rfl
  | .cons hhd htl =>
    rw [AliasEquiv.eq_of_nil hhd, AliasEquivList.eq_of_nil htl]
end

/-- Alias-equivalent lists have equal length. -/
theorem AliasEquivList.length_eq {A : List TypeAlias} {as bs : LMonoTys}
    (h : AliasEquivList A as bs) : as.length = bs.length := by
  match h with
  | .nil => rfl
  | .cons _ htl => simp [AliasEquivList.length_eq htl]

/-- Alias-equivalent lists are alias-equivalent at each index. -/
theorem AliasEquivList.getElem {A : List TypeAlias} {as bs : LMonoTys}
    (h : AliasEquivList A as bs) :
    ∀ (i : Nat) (hi : i < as.length) (hj : i < bs.length),
      AliasEquiv A as[i] bs[i] := by
  match h with
  | .nil => intro i hi _; simp at hi
  | .cons hhd htl =>
    intro i hi hj
    match i with
    | 0 => simpa using hhd
    | n + 1 =>
      simp only [List.getElem_cons_succ]
      exact AliasEquivList.getElem htl n (by simpa using hi)
        (by simpa using hj)

/-- A pointwise relation implying alias equivalence gives listwise alias
    equivalence. -/
theorem AliasEquivList.of_forall₂ {A : List TypeAlias}
    {R : LMonoTy → LMonoTy → Prop} {as bs : LMonoTys}
    (hR : ∀ a b, R a b → AliasEquiv A a b)
    (h : List.Rel₂ R as bs) :
    AliasEquivList A as bs := by
  induction h with
  | nil => exact .nil
  | cons hhd _ ih => exact .cons (hR _ _ hhd) ih

/-- Alias-equivalent lists are alias-equivalent entry by entry. -/
theorem AliasEquivList.forall₂ {A : List TypeAlias} {as bs : LMonoTys}
    (h : AliasEquivList A as bs) : List.Rel₂ (AliasEquiv A) as bs := by
  match h with
  | .nil => exact List.Rel₂.nil
  | .cons hhd htl => exact List.Rel₂.cons hhd (AliasEquivList.forall₂ htl)

/-- If the types of `sig`, after substituting `Sren`, are pointwise
    alias-equivalent to `sig'` under well-formed aliases, then after a further
    substitution `S` they stay alias-equivalent at each index. -/
theorem AliasEquivList_rename_subst_getElem (aliases : List TypeAlias)
    (haWF : ∀ a, a ∈ aliases → TypeAlias.WF a) (Sren S : Subst)
    (sig sig' : LMonoTys)
    (h : AliasEquivList aliases (sig.map (LMonoTy.subst Sren)) sig') :
    ∀ k (hk : k < sig.length) (hk2 : k < sig'.length),
      AliasEquiv aliases (LMonoTy.subst S (LMonoTy.subst Sren sig[k]))
        (LMonoTy.subst S sig'[k]) := by
  intro k hk hk2
  have hk1 : k < (sig.map (LMonoTy.subst Sren)).length := by
    rw [List.length_map]
    exact hk
  have hae := h.getElem k hk1 hk2
  simp only [List.getElem_map] at hae
  exact LExpr.AliasEquiv_subst aliases _ _ S hae haWF

-- `KnownTypes.containsName` is defined apart from `Identifiers.containsName`,
-- so `Identifiers.containsName_eq_true_iff_mem` does not apply to it.
/-- `containsName` holds exactly for the table's keys. -/
theorem KnownTypes.containsName_eq_true_iff_mem (ks : KnownTypes) (n : String) :
    KnownTypes.containsName ks n = true ↔ n ∈ ks := by
  unfold KnownTypes.containsName
  exact Std.HashMap.contains_iff_mem

/-- A registered type constructor has its name registered. -/
theorem containsName_of_contains (ks : KnownTypes) (k : KnownType)
    (h : KnownTypes.contains ks k = true) :
    KnownTypes.containsName ks k.name = true := by
  simp only [KnownTypes.contains, Identifiers.contains] at h
  elim_err h with i hlk
  simp only [KnownTypes.containsName]
  have hsome : (ks[k.name]?).isSome = true := by simp [hlk]
  exact Std.HashMap.contains_eq_isSome_getElem? (m := ks) (a := k.name) ▸
    hsome

/-- Closing the newest variable scope keeps every alias body alias-free. -/
theorem TEnv.popContext_preserves_aliasesResolved {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] (Env : TEnv IDMeta)
    (hr : TContext.AliasesResolved Env.context) :
    TContext.AliasesResolved (Env.popContext).context := by
  intro a ha
  apply hr a
  simpa only [TEnv.popContext, TEnv.updateContext, TEnv.context] using ha

/-- Replacing the context keeps the substitution. -/
theorem TEnv.updateContext_stateSubstInfo {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] (Env : TEnv IDMeta)
    (C : TContext IDMeta) :
    (Env.updateContext C).stateSubstInfo = Env.stateSubstInfo := by
  simp only [TEnv.updateContext]

/-- Opening a variable scope keeps the substitution. -/
theorem TEnv.pushEmptyContext_stateSubstInfo {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] (Env : TEnv IDMeta) :
    Env.pushEmptyContext.stateSubstInfo = Env.stateSubstInfo := by
  simp only [TEnv.pushEmptyContext, TEnv.updateContext]

/-- Closing a variable scope keeps the substitution. -/
theorem TEnv.popContext_stateSubstInfo {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] (Env : TEnv IDMeta) :
    Env.popContext.stateSubstInfo = Env.stateSubstInfo := by
  simp only [TEnv.popContext, TEnv.updateContext]

/-- A fresh extension of `sub` expands an application as `sub` does if `sub`
    has an alias for it. -/
private theorem LMonoTy.tconsAliasSimple_eq_of_FreshExtension (name : String)
    (args : LMonoTys) (sub sup : List TypeAlias) (alias : TypeAlias)
    (hext : TypeAlias.FreshExtension sub sup)
    (hfind : sub.find?
        (fun a => a.name == name && a.typeArgs.length == args.length)
      = some alias) :
    LMonoTy.tconsAliasSimple name args sup =
      LMonoTy.tconsAliasSimple name args sub := by
  obtain ⟨new, heq, hfresh⟩ := hext
  have hpred := List.find?_some hfind
  have hname : alias.name = name := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    exact hpred.1
  have hmem : alias ∈ sub := List.mem_of_find?_eq_some hfind
  have hnone : new.find?
      (fun a => a.name == name && a.typeArgs.length == args.length) = none := by
    rw [List.find?_eq_none]
    intro a ha hpa
    simp only [Bool.and_eq_true, beq_iff_eq] at hpa
    exact hfresh a ha alias hmem (by rw [hpa.1, hname])
  have hsup : sup.find?
      (fun a => a.name == name && a.typeArgs.length == args.length)
      = some alias := by
    rw [heq, List.find?_append, hnone, Option.none_or, hfind]
  simp only [LMonoTy.tconsAliasSimple, hsup, hfind]

/-- Instantiating an unquantified scheme only resolves its aliases. -/
private theorem LTy.resolveAliases_forAll_nil {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta] (mty : LMonoTy)
    (Env : TEnv IDMeta) :
    LTy.resolveAliases (LTy.forAll [] mty) Env =
      LMonoTy.resolveAliases mty Env := by
  simp only [LTy.resolveAliases, LTy.instantiate, bind, Except.bind]

/-- Checked instantiation of an unquantified scheme yields its registered alias
    resolution. -/
theorem LTy.instantiateWithCheck_forAll_nil_inv {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (C : LContext T) (mty r : LMonoTy) (Env Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck (LTy.forAll [] mty) C Env = .ok (r, Env')) :
    LMonoTy.resolveAliases mty Env = .ok (r, Env') ∧
      isInstanceOfKnownType r C = true := by
  simp only [LTy.instantiateWithCheck, LTy.resolveAliases_forAll_nil, bind,
    Except.bind] at h
  elim_err h with vr hr
  obtain ⟨mtyR, EnvR⟩ := vr
  elim_err h
  elim_err h with hknown
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hrEq, hEnvEq⟩ := h
  subst hrEq; subst hEnvEq
  exact ⟨hr, by simpa using hknown⟩

/-- A successful instantiation of a nonempty list of schemes instantiates the
    head with a check, then the tail in the resulting environment; the result
    is the head's type followed by the tail's types. -/
private theorem LMonoTySignature.instantiate_go_cons_inv {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    {C : LContext T}
    {t : LTy} {trest : LTys} {Env EnvR : TEnv T.IDMeta} {rtys : LMonoTys}
    (h : LMonoTySignature.instantiate.go C Env (t :: trest) =
      .ok (rtys, EnvR)) :
    ∃ mt EnvA mtrest, LTy.instantiateWithCheck t C Env = .ok (mt, EnvA) ∧
      LMonoTySignature.instantiate.go C EnvA trest = .ok (mtrest, EnvR) ∧
      rtys = mt :: mtrest := by
  simp only [LMonoTySignature.instantiate.go, bind, Except.bind] at h
  elim_err h with v hhd
  obtain ⟨mt, EnvA⟩ := v
  elim_err h with v2 htl
  obtain ⟨mtrest, EnvB⟩ := v2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨mt, EnvA, mtrest, hhd, htl, rfl⟩

/-- On unquantified schemes, the instantiation loop resolves aliases to
    registered instances. -/
private theorem LMonoTySignature.instantiate_go_resolveAliases {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (C : LContext T) (mtys : LMonoTys) :
    ∀ (Env EnvR : TEnv T.IDMeta) (rtys : LMonoTys),
      LMonoTySignature.instantiate.go C Env
          (mtys.map (fun mty => LTy.forAll [] mty))
        = .ok (rtys, EnvR) →
      LMonoTys.resolveAliases mtys Env = .ok (rtys, EnvR) ∧
        rtys.length = mtys.length ∧
        ∀ mty ∈ rtys, isInstanceOfKnownType mty C = true := by
  induction mtys with
  | nil =>
    intro Env EnvR rtys h
    simp only [List.map_nil, LMonoTySignature.instantiate.go, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨hrtys, hEnv⟩ := h
    subst hrtys; subst hEnv
    refine ⟨?_, by simp, by simp⟩
    simp only [LMonoTys.resolveAliases, pure, Except.pure]
  | cons hd tl ih =>
    intro Env EnvR rtys h
    obtain ⟨hdR, EnvA, tlR, hhd, htl, rfl⟩ :=
      LMonoTySignature.instantiate_go_cons_inv h
    obtain ⟨hhdRes, hhdKnown⟩ :=
      LTy.instantiateWithCheck_forAll_nil_inv C hd hdR Env EnvA hhd
    obtain ⟨htlRes, htlLen, htlKnown⟩ := ih EnvA EnvR tlR htl
    refine ⟨?_, by simp [htlLen], ?_⟩
    · simp only [LMonoTys.resolveAliases, bind, Except.bind, hhdRes, htlRes,
        pure, Except.pure]
    · intro mty hmty
      rcases List.mem_cons.mp hmty with rfl | hmty
      · exact hhdKnown
      · exact htlKnown mty hmty

/-- Signature instantiation instantiates parameters and resolves aliases to
    registered instances. -/
theorem LMonoTySignature.instantiate_resolveAliases {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (C : LContext T) (Env EnvR : TEnv T.IDMeta) (tyArgs : List TyIdentifier)
    (sig sig' : @LMonoTySignature T.IDMeta)
    (h : LMonoTySignature.instantiate C Env tyArgs sig = .ok (sig', EnvR)) :
    ∃ (mtysI : LMonoTys) (EnvI : TEnv T.IDMeta),
      LMonoTys.instantiateEnv tyArgs sig.values Env = .ok (mtysI, EnvI) ∧
      LMonoTys.resolveAliases mtysI EnvI = .ok (sig'.values, EnvR) ∧
      ∀ mty ∈ sig'.values, isInstanceOfKnownType mty C = true := by
  simp only [LMonoTySignature.instantiate, bind, Except.bind] at h
  elim_err h with vI hI
  obtain ⟨mtysI, EnvI⟩ := vI
  elim_err h with vG hG
  obtain ⟨newtys, EnvG⟩ := vG
  obtain ⟨hres, hlen, hknown⟩ :=
    LMonoTySignature.instantiate_go_resolveAliases C mtysI EnvI EnvG newtys hG
  obtain ⟨hsig', hEnv⟩ := Prod.mk.inj (Except.ok.inj h)
  dsimp only at hsig'
  subst hEnv
  have hvals : sig'.values = newtys := by
    rw [← hsig', ListMap.values_eq_map_snd ((ListMap.keys sig).zip newtys)]
    refine List.map_snd_zip ?_
    rw [hlen,
      LMonoTys.instantiateEnv_length tyArgs sig.values Env mtysI EnvI hI,
      ListMap.keys.length, ListMap.values_eq_map_snd sig,
      List.length_map (as := sig)]
    exact Nat.le_refl _
  rw [hvals]
  exact ⟨mtysI, EnvI, hI, hres, hknown⟩

/-- Opening a variable scope keeps every alias body alias-free. -/
theorem TEnv.pushEmptyContext_preserves_aliasesResolved
    {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    (Env : TEnv IDMeta)
    (h_resolved : TContext.AliasesResolved Env.context) :
    TContext.AliasesResolved (Env.pushEmptyContext).context := by
  intro a ha
  apply h_resolved a
  simpa only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context] using ha

/-- A successful known-type insertion does not depend on the error message. -/
theorem addKnownTypeWithError_message_irrel {T : LExprParams}
    (C C' : LContext T) (k : KnownType) (f g : Message)
    (h : C.addKnownTypeWithError k f = .ok C') :
    C.addKnownTypeWithError k g = .ok C' := by
  simp only [LContext.addKnownTypeWithError, KnownTypes.addWithError,
    Identifiers.addWithError, bind, Except.bind] at h ⊢
  generalize hgen :
    C.knownTypes.containsThenInsertIfNew k.name k.arity = p at h ⊢
  cases hb : p.fst with
  | true => simp only [hb, reduceIte, reduceCtorEq] at h
  | false => simp only [hb] at h ⊢; exact h

/-- If registering a type succeeds in a context whose `idents` field was
    replaced by `j`, it also succeeds in the original context; the two results
    differ only in `idents`, and the first keeps `j`. -/
theorem addKnownTypeWithError_setIdents {T : LExprParams}
    (C : LContext T) (j : Identifiers T.IDMeta) (k : KnownType) (f : Message)
    (C' : LContext T)
    (h : { C with idents := j }.addKnownTypeWithError k f = .ok C') :
    C.addKnownTypeWithError k f = .ok { C' with idents := C.idents } ∧
      C'.idents = j := by
  simp only [LContext.addKnownTypeWithError, bind, Except.bind] at h ⊢
  elim_err h with ks hks
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- `addFactoryFunction` commutes with setting the `idents` field. -/
theorem addFactoryFunction_setIdents {T : LExprParams} (C : LContext T)
    (f : LFunc T) (v : Identifiers T.IDMeta) :
    ({C with idents := v}).addFactoryFunction f
      = { C.addFactoryFunction f with idents := v } := by
  unfold LContext.addFactoryFunction
  split <;> rfl

/-- Folding `addFactoryFunction` commutes with setting the `idents` field. -/
theorem foldl_addFactoryFunction_setIdents {T : LExprParams} {α : Type}
    (C : LContext T) (l : List α) (g : α → LFunc T) (v : Identifiers T.IDMeta) :
    l.foldl (fun C a => C.addFactoryFunction (g a)) {C with idents := v}
      = { l.foldl (fun C a => C.addFactoryFunction (g a)) C with
          idents := v } := by
  induction l generalizing C with
  | nil => rfl
  | cons a t IH =>
    simp only [List.foldl_cons]
    rw [addFactoryFunction_setIdents, IH]

/-- Pushing a substitution scope keeps the context. -/
theorem TEnv.pushEmptySubstScope_context_eq {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] (Env : TEnv IDMeta) :
    (Env.pushEmptySubstScope).context = Env.context := by
  simp only [TEnv.pushEmptySubstScope, TEnv.context]

/-- Popping a substitution scope keeps the context. -/
theorem TEnv.popSubstScope_context_eq {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] (Env : TEnv IDMeta) :
    (Env.popSubstScope).context = Env.context := by
  simp only [TEnv.popSubstScope, TEnv.context]

/-- Replacing the substitution keeps the context. -/
theorem TEnv.updateSubst_context {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] (Env : TEnv IDMeta) (S : SubstInfo) :
    (Env.updateSubst S).context = Env.context := by
  rfl

/-- Resolving the aliases of a nonempty constructor list resolves the tail
    first, then the head constructor's field types in the environment the tail
    produced; the result is the head with resolved fields followed by the
    resolved tail. -/
private theorem LConstrs.resolveAliases_cons_inv
    {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    {c : LConstr IDMeta} {crest : List (LConstr IDMeta)}
    {Env Env2 : TEnv IDMeta} {constrs' : List (LConstr IDMeta)}
    (h : LConstrs.resolveAliases (c :: crest) Env = .ok (constrs', Env2)) :
    ∃ acc Envc args', LConstrs.resolveAliases crest Env = .ok (acc, Envc) ∧
      LConstrs.resolveAliases.go c.args Envc = .ok (args', Env2) ∧
      constrs' = { c with args := args' } :: acc := by
  simp only [LConstrs.resolveAliases, List.foldrM_cons, bind,
    Except.bind] at h
  elim_err h with v heq
  obtain ⟨acc_crest, Env_crest⟩ := v
  elim_err h with w hgo
  obtain ⟨args', Env'⟩ := w
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨acc_crest, Env_crest, args', heq, hgo, rfl⟩

/-- Resolving the aliases of a nonempty mutual block resolves the tail first,
    then the head datatype's constructors in the environment the tail produced;
    the result is the head datatype, with its name and type parameters and the
    resolved constructors, in front of the resolved tail. -/
theorem MutualDatatype.resolveAliases_cons_inv
    {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    {d : LDatatype IDMeta} {drest : List (LDatatype IDMeta)}
    {Env Env2 : TEnv IDMeta} {block_r : List (LDatatype IDMeta)}
    (h : MutualDatatype.resolveAliases (d :: drest) Env =
      .ok (block_r, Env2)) :
    ∃ acc Envd constrs' d_r,
      MutualDatatype.resolveAliases drest Env = .ok (acc, Envd) ∧
      LConstrs.resolveAliases d.constrs Envd = .ok (constrs', Env2) ∧
      block_r = d_r :: acc ∧ d_r.name = d.name ∧ d_r.typeArgs = d.typeArgs ∧
      d_r.constrs = constrs' := by
  simp only [MutualDatatype.resolveAliases, List.foldrM_cons, bind,
    Except.bind] at h
  elim_err h with v heq
  obtain ⟨acc_drest, Env_drest⟩ := v
  elim_err h with constrs' Env' hcon
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨acc_drest, Env_drest, constrs', _, heq, hcon, rfl, rfl, rfl, rfl⟩

/-- Resolving the aliases of a constructor list leaves the environment
    unchanged. -/
theorem LConstrs.resolveAliases_env_eq
    {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (constrs : List (LConstr IDMeta)) (Env : TEnv IDMeta)
    (constrs' : List (LConstr IDMeta)) (Env' : TEnv IDMeta)
    (h : LConstrs.resolveAliases constrs Env = .ok (constrs', Env')) :
    Env' = Env := by
  induction constrs generalizing constrs' Env' with
  | nil =>
    simp only [LConstrs.resolveAliases, List.foldrM_nil, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | cons c rest ih =>
    obtain ⟨acc, Envc, args', hrest, hgo, -⟩ :=
      LConstrs.resolveAliases_cons_inv h
    simp only [LConstrs.resolveAliases.go, bind, Except.bind] at hgo
    elim_err hgo with tysPair htys
    obtain ⟨tys', Env3⟩ := tysPair
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hgo
    rw [← hgo.2, LMonoTys.resolveAliases_env_eq _ Envc tys' Env3 htys,
      ih acc Envc hrest]

/-- Resolving the aliases of a mutual block leaves the environment unchanged. -/
theorem MutualDatatype.resolveAliases_env_eq {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (block block_r : List (LDatatype IDMeta)) (Env Env_r : TEnv IDMeta)
    (h : MutualDatatype.resolveAliases block Env = .ok (block_r, Env_r)) :
    Env_r = Env := by
  induction block generalizing block_r Env_r with
  | nil =>
    simp only [MutualDatatype.resolveAliases, List.foldrM_nil, pure,
      Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | cons d rest ih =>
    obtain ⟨acc, Envd, constrs', -, hrest, hcon, -⟩ :=
      MutualDatatype.resolveAliases_cons_inv h
    rw [LConstrs.resolveAliases_env_eq d.constrs Envd constrs' Env_r hcon,
      ih acc Envd hrest]

/-- If adding a mutual block succeeds in a context whose `idents` field was
    replaced by `j`, it also succeeds in the original context; the two results
    differ only in `idents`, and the first keeps `j`. -/
theorem addMutualBlock_setIdents {T : LExprParams}
    [DecidableEq T.IDMeta]
    [Inhabited T.IDMeta] [Inhabited T.Metadata] [ToFormat T.IDMeta]
    (C : LContext T) (j : Identifiers T.IDMeta)
    (block : MutualDatatype T.IDMeta) (C' : LContext T)
    (h : { C with idents := j }.addMutualBlock block = .ok C') :
    C.addMutualBlock block = .ok { C' with idents := C.idents } ∧
      C'.idents = j := by
  simp only [LContext.addMutualBlock, bind, Except.bind] at h ⊢
  elim_err h with loopResult hloop
  elim_err h with datatypes hdatatypes
  elim_err h with generated hgenerated
  elim_err h with functions hfunctions
  elim_err h with knownTypes hknownTypes
  simp only [Except.ok.injEq] at h
  subst C'
  split
  · rename_i _ herr
    nomatch herr.symm.trans hloop
  · exact ⟨rfl, rfl⟩

/-- Resolving aliases in a mutual block keeps the datatype names. -/
theorem MutualDatatype.resolveAliases_names_map {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (block : List (LDatatype IDMeta)) :
    ∀ (block_r : List (LDatatype IDMeta)) (Env Env' : TEnv IDMeta),
      MutualDatatype.resolveAliases block Env = .ok (block_r, Env') →
      block_r.map (·.name) = block.map (·.name) := by
  induction block with
  | nil =>
    intro block_r Env Env' h
    simp only [MutualDatatype.resolveAliases, List.foldrM_nil, pure,
      Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rfl
  | cons d ds IH =>
    intro block_r Env Env' h
    obtain ⟨acc, Envd, -, d_r, hds, -, rfl, hname, -⟩ :=
      MutualDatatype.resolveAliases_cons_inv h
    rw [List.map_cons, List.map_cons, hname, IH acc Env Envd hds]

/-- `WellKindedTy` does not read the context's `idents` field. -/
theorem LContext.WellKindedTy_setIdents {T : LExprParams} (C : LContext T)
    (j : Identifiers T.IDMeta) (ty : LMonoTy) :
    ({ C with idents := j }).WellKindedTy ty = C.WellKindedTy ty := by
  cases C <;> rfl

/-- `LMonoTys.openVars` is the pointwise map of `LMonoTy.openVars`. -/
theorem LMonoTys.openVars_eq_map (vars : List TyIdentifier) (vals : LMonoTys)
    (mtys : LMonoTys) :
    LMonoTys.openVars vars vals mtys =
      mtys.map (LMonoTy.openVars vars vals) := by
  induction mtys with
  | nil => rfl
  | cons hd tl ih =>
    show LMonoTy.openVars vars vals hd :: LMonoTys.openVars vars vals tl = _
    rw [ih, List.map_cons]

mutual
/-- Alias-equivalent monotypes have the same free type variables. -/
theorem AliasEquiv.freeVars_iff {aliases : List TypeAlias}
    (hwf : ∀ a ∈ aliases, TypeAlias.WF a) {m m' : LMonoTy}
    (h : AliasEquiv aliases m m') :
    ∀ tv, tv ∈ LMonoTy.freeVars m ↔ tv ∈ LMonoTy.freeVars m' := by
  match h with
  | .refl => exact fun _ => Iff.rfl
  | .expand hexp =>
    obtain ⟨al, hmem, hname, hlen, heq⟩ := hexp
    have hal := hwf al hmem
    subst hname
    intro tv
    rw [heq]
    show tv ∈ LMonoTys.freeVars _ ↔ _
    constructor
    · exact fun htv => LExpr.openVars_freeVars_superset al.typeArgs _ al.type
        hal.typeArgs_nodup hlen hal.typeArgs_used tv htv
    · exact fun htv => LExpr.openVars_freeVars_subset al.typeArgs _ al.type
        (fun tv' h' => hal.fvs_closed tv' h') hlen tv htv
  | .collapse hexp =>
    obtain ⟨al, hmem, hname, hlen, heq⟩ := hexp
    have hal := hwf al hmem
    subst hname
    intro tv
    rw [heq]
    show _ ↔ tv ∈ LMonoTys.freeVars _
    constructor
    · exact fun htv => LExpr.openVars_freeVars_subset al.typeArgs _ al.type
        (fun tv' h' => hal.fvs_closed tv' h') hlen tv htv
    · exact fun htv => LExpr.openVars_freeVars_superset al.typeArgs _ al.type
        hal.typeArgs_nodup hlen hal.typeArgs_used tv htv
  | .cong_tcons hlist =>
    intro tv
    show tv ∈ LMonoTys.freeVars _ ↔ tv ∈ LMonoTys.freeVars _
    exact AliasEquivList.freeVars_iff hwf hlist tv
  | .trans h1 h2 =>
    intro tv
    exact (AliasEquiv.freeVars_iff hwf h1 tv).trans
      (AliasEquiv.freeVars_iff hwf h2 tv)

/-- Alias-equivalent lists of monotypes have the same free type variables. -/
theorem AliasEquivList.freeVars_iff {aliases : List TypeAlias}
    (hwf : ∀ a ∈ aliases, TypeAlias.WF a) {ms ms' : LMonoTys}
    (h : AliasEquivList aliases ms ms') :
    ∀ tv, tv ∈ LMonoTys.freeVars ms ↔ tv ∈ LMonoTys.freeVars ms' := by
  match h with
  | .nil => exact fun _ => Iff.rfl
  | .cons hhd htl =>
    intro tv
    rw [LMonoTys.freeVars_of_cons, LMonoTys.freeVars_of_cons, List.mem_append,
      List.mem_append]
    exact or_congr (AliasEquiv.freeVars_iff hwf hhd tv)
      (AliasEquivList.freeVars_iff hwf htl tv)
end

/-- Erasing a variable from an environment whose stack of variable-type scopes
    is nonempty leaves that stack nonempty. -/
theorem TEnv.eraseFromContext_types_ne_nil {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] (Env : TEnv T.IDMeta)
    (x : T.Identifier)
    (h : Env.context.types ≠ []) :
    (Env.eraseFromContext x).context.types ≠ [] := by
  change Env.genEnv.context.types ≠ [] at h
  cases htypes : Env.genEnv.context.types with
  | nil => exact absurd htypes h
  | cons scope rest =>
    simp only [TEnv.eraseFromContext, TEnv.updateContext, TEnv.context]
    rw [htypes]
    simp only [HMaps.remove]
    exact List.cons_ne_nil _ _

/-- Opening a variable scope gives a nonempty type-scope stack. -/
theorem TEnv.pushEmptyContext_types_ne_nil {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] (Env : TEnv T.IDMeta) :
    (Env.pushEmptyContext).context.types ≠ [] := by
  have h_types : (Env.pushEmptyContext).context.types
      = HMap.empty :: Env.context.types := by
    simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context,
      HMaps.push]
  rw [h_types]
  exact List.cons_ne_nil _ _

/-- Registering a type, when it succeeds, changes only the context's known
    types. -/
theorem addKnownTypeWithError_inv {T : LExprParams}
    (C C' : LContext T) (k : KnownType) (f : Strata.Message)
    (h : C.addKnownTypeWithError k f = .ok C') :
    ∃ kt, C' = { C with knownTypes := kt } := by
  simp only [LContext.addKnownTypeWithError, bind, Except.bind] at h
  cases h_kt : C.knownTypes.addWithError k f with
  | error e => simp only [h_kt, reduceCtorEq] at h
  | ok kt =>
    simp only [h_kt, Except.ok.injEq] at h
    exact ⟨kt, h.symm⟩

/-- A successful `addKnownTypeWithError` leaves `functions` unchanged. -/
theorem addKnownTypeWithError_functions_eq {T : LExprParams}
    (C C' : LContext T) (k : KnownType) (f : Strata.Message)
    (h : C.addKnownTypeWithError k f = .ok C') :
    C'.functions = C.functions := by
  obtain ⟨kt, rfl⟩ := addKnownTypeWithError_inv C C' k f h
  rfl

/-- Registering a type leaves the rigid type variables of a context alone. -/
theorem addKnownTypeWithError_rigidTypeVars {T : LExprParams}
    {C C' : LContext T} {k : KnownType} {msg : Strata.Message}
    (hadd : C.addKnownTypeWithError k msg = .ok C') :
    C'.rigidTypeVars = C.rigidTypeVars := by
  obtain ⟨kt, rfl⟩ := addKnownTypeWithError_inv C C' k msg hadd
  rfl

/-- A successful `addKnownTypeWithError` leaves `datatypes` unchanged. -/
theorem addKnownTypeWithError_datatypes_eq {T : LExprParams}
    (C C' : LContext T) (k : KnownType) (f : Strata.Message)
    (h : C.addKnownTypeWithError k f = .ok C') :
    C'.datatypes = C.datatypes := by
  obtain ⟨kt, rfl⟩ := addKnownTypeWithError_inv C C' k f h
  rfl

/-- Declaring a function changes only the context's functions. -/
theorem addFactoryFunction_inv {T : LExprParams} (C : LContext T)
    (fn : LFunc T) :
    ∃ fs, C.addFactoryFunction fn = { C with functions := fs } := by
  unfold LContext.addFactoryFunction
  split
  · exact ⟨C.functions, rfl⟩
  · exact ⟨_, rfl⟩

/-- Declaring a sequence of functions changes only the context's functions. -/
theorem foldl_addFactoryFunction_inv {T : LExprParams} {α : Type}
    (C : LContext T) (l : List α) (gf : α → LFunc T) :
    ∃ fs, l.foldl (fun C a => C.addFactoryFunction (gf a)) C =
      { C with functions := fs } := by
  induction l generalizing C with
  | nil => exact ⟨C.functions, rfl⟩
  | cons a rest ih =>
    obtain ⟨fs, hfs⟩ := addFactoryFunction_inv C (gf a)
    obtain ⟨fs', hfs'⟩ := ih { C with functions := fs }
    rw [List.foldl_cons, hfs, hfs']
    exact ⟨fs', rfl⟩

/-- A function of `C.addFactoryFunction fn` is `fn` or a function of `C`. -/
theorem mem_addFactoryFunction {T : LExprParams} (C : LContext T)
    (fn lf : LFunc T)
    (hlf : lf ∈ (C.addFactoryFunction fn).functions.toArray) :
    lf ∈ C.functions.toArray ∨ lf = fn := by
  unfold LContext.addFactoryFunction at hlf
  split at hlf
  · exact .inl hlf
  · simp only [Factory.push] at hlf
    rw [Array.mem_push] at hlf
    exact hlf

/-- Registering a type leaves other unregistered names unregistered. -/
theorem knownTypes_addKnownTypeWithError_notContains_of_ne {T : LExprParams}
    (C C' : LContext T) (k : KnownType) (f : Strata.Message) (n : String)
    (h : C.addKnownTypeWithError k f = .ok C')
    (hne : k.name ≠ n)
    (hn : C.knownTypes.containsName n = false) :
    C'.knownTypes.containsName n = false := by
  simp only [LContext.addKnownTypeWithError, KnownTypes.addWithError,
    Identifiers.addWithError, Std.HashMap.containsThenInsertIfNew_fst,
    Std.HashMap.containsThenInsertIfNew_snd, bind, Except.bind] at h
  elim_err h with v hv
  elim_err hv
  simp only [Except.ok.injEq] at hv
  subst hv
  simp only [Except.ok.injEq] at h
  subst h
  simp only [KnownTypes.containsName] at hn ⊢
  simp [Std.HashMap.contains_insertIfNew, hn, hne]

/-- Declaring a function keeps the registered types. -/
theorem addFactoryFunction_knownTypes {T : LExprParams} (C : LContext T)
    (fn : LFunc T) :
    (C.addFactoryFunction fn).knownTypes = C.knownTypes := by
  obtain ⟨fs, hfs⟩ := addFactoryFunction_inv C fn
  rw [hfs]

/-- Declaring functions keeps the registered types. -/
theorem foldl_addFactoryFunction_knownTypes {T : LExprParams} {α : Type}
    (C : LContext T) (l : List α) (gf : α → LFunc T) :
    (l.foldl (fun C a => C.addFactoryFunction (gf a)) C).knownTypes =
      C.knownTypes := by
  obtain ⟨fs, hfs⟩ := foldl_addFactoryFunction_inv C l gf
  rw [hfs]

/-- A type constructor applied to registered instances at the arity `ks`
    records for it is a registered instance. -/
theorem knownInstance_tcons_of_getElem? {ks : KnownTypes} {nm : String}
    {args : LMonoTys} (h : ks[nm]? = some args.length)
    (hargs : ∀ t ∈ args, LMonoTy.knownInstance t ks = true) :
    LMonoTy.knownInstance (.tcons nm args) ks = true := by
  simp only [LMonoTy.knownInstance, Bool.and_eq_true, KnownTypes.contains,
    Identifiers.contains, KnownType.arity, h, beq_self_eq_true, true_and]
  exact LMonoTys.knownInstances_of_forall hargs

/-- A constructor registered at arity zero is a registered instance. -/
theorem knownInstance_nullary (ks : KnownTypes) (nm : String)
    (h : ks[nm]? = some 0) :
    LMonoTy.knownInstance (.tcons nm []) ks = true :=
  knownInstance_tcons_of_getElem? h (fun _ ht => absurd ht List.not_mem_nil)

/-- When `arrow` is registered with two arguments, an arrow between two
    registered instances is a registered instance. -/
theorem knownInstance_arrow (ks : KnownTypes) (t1 t2 : LMonoTy)
    (harrow : ks["arrow"]? = some 2)
    (h1 : LMonoTy.knownInstance t1 ks = true)
    (h2 : LMonoTy.knownInstance t2 ks = true) :
    LMonoTy.knownInstance (.arrow t1 t2) ks = true := by
  have hargs : ∀ t ∈ [t1, t2], LMonoTy.knownInstance t ks = true := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h1
    · exact h2
  exact knownInstance_tcons_of_getElem? harrow hargs

/-- A registered instance `tcons nm args` has `nm` and `args` registered. -/
theorem knownInstance_tcons_inv (ks : KnownTypes) (nm : String)
    (args : LMonoTys)
    (h : LMonoTy.knownInstance (.tcons nm args) ks = true) :
    KnownTypes.contains ks { name := nm, metadata := args.length } = true ∧
      nm ∈ ks ∧ LMonoTys.knownInstances args ks = true := by
  have hsplit :
      KnownTypes.contains ks { name := nm, metadata := args.length } = true ∧
        LMonoTys.knownInstances args ks = true := by
    unfold Lambda.LMonoTy.knownInstance at h; simpa using h
  refine ⟨hsplit.1, ?_, hsplit.2⟩
  have hc := hsplit.1
  unfold KnownTypes.contains Identifiers.contains at hc
  elim_err hc with v hv
  have hsome : (ks[nm]?).isSome = true := by rw [hv]; rfl
  exact Std.HashMap.mem_iff_isSome_getElem?.mpr hsome

/-- A name is registered at an arity exactly when the table maps the name to
    that arity. -/
private theorem KnownTypes.contains_iff_getElem? (ks : KnownTypes)
    (name : String) (n : Nat) :
    ks.contains { name := name, metadata := n } = true ↔
      ks[name]? = some n := by
  simp only [KnownTypes.contains, Identifiers.contains, KnownType.arity]
  cases ks[name]? with
  | none => simp
  | some i =>
    simp only [beq_iff_eq, Option.some.injEq]
    exact eq_comm

/-- A type is a registered instance exactly when every constructor name and
    arity it uses is registered. -/
theorem LMonoTy.knownInstance_iff_getTypeConsArities (ks : KnownTypes)
    (t : LMonoTy) :
    LMonoTy.knownInstance t ks = true ↔
      ∀ ref ∈ getTypeConsArities t,
        ks.contains { name := ref.1, metadata := ref.2 } = true := by
  simp only [LMonoTy.knownInstance_iff_wellKinded, LMonoTy.WellKinded,
    KnownTypes.contains_iff_getElem?, Prod.forall]

mutual
/-- Value lists agreeing on registered-instance entries open a body equally when
    the first opens it to a registered instance. -/
private theorem openVars_eq_of_forall₂ (ks : KnownTypes)
    (vars : List TyIdentifier) (valsA valsB : LMonoTys)
    (hrel : List.Rel₂ (fun a b => LMonoTy.knownInstance a ks = true → b = a)
      valsA valsB)
    (body : LMonoTy)
    (hknown :
      LMonoTy.knownInstance (LMonoTy.openVars vars valsA body) ks = true) :
    LMonoTy.openVars vars valsB body = LMonoTy.openVars vars valsA body := by
  match body with
  | .ftvar x =>
    rcases zip_find?_of_forall₂ vars valsA valsB x hrel with
      ⟨hA, hB⟩ | ⟨_, a, b, hA, hB, hR⟩
    · simp only [LMonoTy.openVars, hA, hB]
    · simp only [LMonoTy.openVars, hA] at hknown
      simp only [LMonoTy.openVars, hA, hB]
      exact hR hknown
  | .bitvec _ => simp only [LMonoTy.openVars]
  | .tcons _ args =>
    simp only [LMonoTy.openVars, LMonoTy.knownInstance,
      Bool.and_eq_true] at hknown
    simp only [LMonoTy.openVars]
    rw [openVarsList_eq_of_forall₂ ks vars valsA valsB hrel args hknown.2]

/-- Value lists agreeing on registered-instance entries open bodies equally when
    the first opens them to registered instances. -/
private theorem openVarsList_eq_of_forall₂ (ks : KnownTypes)
    (vars : List TyIdentifier) (valsA valsB : LMonoTys)
    (hrel : List.Rel₂ (fun a b => LMonoTy.knownInstance a ks = true → b = a)
      valsA valsB)
    (bodies : LMonoTys)
    (hknown : LMonoTys.knownInstances (LMonoTys.openVars vars valsA bodies) ks
      = true) :
    LMonoTys.openVars vars valsB bodies =
      LMonoTys.openVars vars valsA bodies := by
  match bodies with
  | [] => simp only [LMonoTys.openVars]
  | b :: rest =>
    simp only [LMonoTys.openVars, LMonoTys.knownInstances] at hknown
    simp only [LMonoTys.openVars]
    elim_err hknown with hhd
    rw [openVars_eq_of_forall₂ ks vars valsA valsB hrel b hhd,
        openVarsList_eq_of_forall₂ ks vars valsA valsB hrel rest hknown]
end

/-- Lists agreeing on registered-instance entries are equal when the first has
    only those. -/
private theorem eq_of_forall₂_knownInstances (ks : KnownTypes)
    (as bs : LMonoTys)
    (hrel : List.Rel₂ (fun a b => LMonoTy.knownInstance a ks = true → b = a)
      as bs) :
    LMonoTys.knownInstances as ks = true → bs = as := by
  induction hrel with
  | nil => intro _; rfl
  | @cons a b as' bs' hhd _ ih =>
    intro hknown
    simp only [LMonoTys.knownInstances] at hknown
    elim_err hknown with ha
    rw [hhd ha, ih hknown]

mutual
/-- Extending the aliases with fresh ones whose names are unregistered does not
    change a resolution that is a registered instance: if `mty` resolves to a
    registered instance under the smaller aliases, it resolves to the same type
    under the larger ones. -/
theorem LMonoTy.resolveAliases_eq_of_FreshExtension {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (ks : KnownTypes) (mty : LMonoTy)
    (EnvSub EnvSup EnvSub' EnvSup' : TEnv IDMeta) (mtySub mtySup : LMonoTy)
    (hext :
      TypeAlias.FreshExtension EnvSub.context.aliases EnvSup.context.aliases)
    (hfresh : ∀ al ∈ EnvSup.context.aliases, al ∉ EnvSub.context.aliases →
        KnownTypes.containsName ks al.name = false)
    (hsub : LMonoTy.resolveAliases mty EnvSub = .ok (mtySub, EnvSub'))
    (hsup : LMonoTy.resolveAliases mty EnvSup = .ok (mtySup, EnvSup'))
    (hknown : LMonoTy.knownInstance mtySub ks = true) :
    mtySup = mtySub := by
  match mty with
  | .ftvar _ =>
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hsub hsup
    rw [← hsub.1, ← hsup.1]
  | .bitvec _ =>
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hsub hsup
    rw [← hsub.1, ← hsup.1]
  | .tcons name args =>
    simp only [LMonoTy.resolveAliases, bind, Except.bind] at hsub hsup
    elim_err hsub
    rename_i vSub hargsSub
    obtain ⟨argsSub, EnvSubMid⟩ := vSub
    elim_err hsup
    rename_i vSup hargsSup
    obtain ⟨argsSup, EnvSupMid⟩ := vSup
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsub hsup
    have hEnvSubMid : EnvSubMid = EnvSub :=
      LMonoTys.resolveAliases_env_eq args EnvSub argsSub EnvSubMid hargsSub
    have hEnvSupMid : EnvSupMid = EnvSup :=
      LMonoTys.resolveAliases_env_eq args EnvSup argsSup EnvSupMid hargsSup
    rw [hEnvSubMid] at hargsSub hsub
    rw [hEnvSupMid] at hargsSup hsup
    rw [← hsub.1] at hknown ⊢
    rw [← hsup.1]
    have hrel := LMonoTys.resolveAliases_forall₂_of_FreshExtension ks args
      EnvSub EnvSup EnvSub EnvSup argsSub argsSup hext hfresh hargsSub hargsSup
    have hlen : argsSub.length = argsSup.length := List.Rel₂.length_eq hrel
    rcases hfindSub : EnvSub.context.aliases.find?
        (fun a => a.name == name && a.typeArgs.length == argsSub.length) with
      _ | al
    · have hknown' := hknown
      simp only [LMonoTy.tconsAliasSimple, hfindSub, LMonoTy.knownInstance,
        Bool.and_eq_true] at hknown'
      obtain ⟨hcontains, hargsKnown⟩ := hknown'
      have hargsEq : argsSup = argsSub :=
        eq_of_forall₂_knownInstances ks _ _ hrel hargsKnown
      subst hargsEq
      simp only [LMonoTy.tconsAliasSimple, hfindSub]
      rcases hfindSup : EnvSup.context.aliases.find?
          (fun a => a.name == name && a.typeArgs.length == argsSup.length) with
        _ | al
      · simp only [hfindSup]
      · exfalso
        have hpred := List.find?_some hfindSup
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
        have halMem : al ∈ EnvSup.context.aliases :=
          List.mem_of_find?_eq_some hfindSup
        have halNotMem : al ∉ EnvSub.context.aliases := by
          intro hmem
          rw [List.find?_eq_none] at hfindSub
          exact absurd (List.find?_some hfindSup) (hfindSub al hmem)
        have hnoName := hfresh al halMem halNotMem
        have hName := containsName_of_contains ks
          { name := name, metadata := argsSup.length } hcontains
        rw [hpred.1] at hnoName
        simp only [hName] at hnoName
        exact absurd hnoName (by simp)
    · have hfindSup' : EnvSub.context.aliases.find?
          (fun a => a.name == name && a.typeArgs.length == argsSup.length) =
            some al := by
        rw [← hlen]; exact hfindSub
      have hsupSimple :
          LMonoTy.tconsAliasSimple name argsSup EnvSup.context.aliases
            = LMonoTy.tconsAliasSimple name argsSup EnvSub.context.aliases :=
        LMonoTy.tconsAliasSimple_eq_of_FreshExtension name argsSup
          EnvSub.context.aliases EnvSup.context.aliases al hext hfindSup'
      rw [hsupSimple]
      simp only [LMonoTy.tconsAliasSimple, hfindSub, hfindSup']
      simp only [LMonoTy.tconsAliasSimple, hfindSub, TypeAlias.expand] at hknown
      exact openVars_eq_of_forall₂ ks al.typeArgs argsSub argsSup hrel al.type
        hknown

/-- Under a fresh extension with unregistered names, list resolution agrees on
    entries that are registered instances. -/
private theorem LMonoTys.resolveAliases_forall₂_of_FreshExtension
    {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (ks : KnownTypes) (mtys : LMonoTys)
    (EnvSub EnvSup EnvSub' EnvSup' : TEnv IDMeta) (mtysSub mtysSup : LMonoTys)
    (hext :
      TypeAlias.FreshExtension EnvSub.context.aliases EnvSup.context.aliases)
    (hfresh : ∀ al ∈ EnvSup.context.aliases, al ∉ EnvSub.context.aliases →
        KnownTypes.containsName ks al.name = false)
    (hsub : LMonoTys.resolveAliases mtys EnvSub = .ok (mtysSub, EnvSub'))
    (hsup : LMonoTys.resolveAliases mtys EnvSup = .ok (mtysSup, EnvSup')) :
    List.Rel₂ (fun a b => LMonoTy.knownInstance a ks = true → b = a)
      mtysSub mtysSup := by
  match mtys with
  | [] =>
    simp only [LMonoTys.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hsub hsup
    rw [← hsub.1, ← hsup.1]
    exact List.Rel₂.nil
  | mty :: mrest =>
    simp only [LMonoTys.resolveAliases, bind, Except.bind] at hsub hsup
    elim_err hsub
    rename_i vSubHd hhdSub
    obtain ⟨mtySub, EnvSubHd⟩ := vSubHd
    elim_err hsub
    rename_i vSubTl htlSub
    obtain ⟨mrestSub, EnvSubTl⟩ := vSubTl
    elim_err hsup
    rename_i vSupHd hhdSup
    obtain ⟨mtySup, EnvSupHd⟩ := vSupHd
    elim_err hsup
    rename_i vSupTl htlSup
    obtain ⟨mrestSup, EnvSupTl⟩ := vSupTl
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hsub hsup
    have hEnvSubHd : EnvSubHd = EnvSub :=
      LMonoTy.resolveAliases_env_eq mty EnvSub mtySub EnvSubHd hhdSub
    have hEnvSupHd : EnvSupHd = EnvSup :=
      LMonoTy.resolveAliases_env_eq mty EnvSup mtySup EnvSupHd hhdSup
    rw [hEnvSubHd] at hhdSub htlSub
    rw [hEnvSupHd] at hhdSup htlSup
    rw [← hsub.1, ← hsup.1]
    refine List.Rel₂.cons ?_ ?_
    · intro hk
      exact LMonoTy.resolveAliases_eq_of_FreshExtension ks mty EnvSub EnvSup
        EnvSub EnvSup mtySub mtySup hext hfresh hhdSub hhdSup hk
    · exact LMonoTys.resolveAliases_forall₂_of_FreshExtension ks mrest EnvSub
        EnvSup EnvSubTl EnvSupTl mrestSub mrestSup hext hfresh htlSub htlSup
end

/-- Extending the aliases with fresh ones whose names are unregistered does not
    change the resolution of a list of types that resolves to registered
    instances under the smaller aliases. -/
theorem LMonoTys.resolveAliases_eq_of_FreshExtension {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (ks : KnownTypes) (mtys : LMonoTys)
    (EnvSub EnvSup EnvSub' EnvSup' : TEnv IDMeta) (mtysSub mtysSup : LMonoTys)
    (hext :
      TypeAlias.FreshExtension EnvSub.context.aliases EnvSup.context.aliases)
    (hfresh : ∀ al ∈ EnvSup.context.aliases, al ∉ EnvSub.context.aliases →
        KnownTypes.containsName ks al.name = false)
    (hsub : LMonoTys.resolveAliases mtys EnvSub = .ok (mtysSub, EnvSub'))
    (hsup : LMonoTys.resolveAliases mtys EnvSup = .ok (mtysSup, EnvSup'))
    (hknown : ∀ mty ∈ mtysSub, LMonoTy.knownInstance mty ks = true) :
    mtysSup = mtysSub :=
  eq_of_forall₂_knownInstances ks mtysSub mtysSup
    (LMonoTys.resolveAliases_forall₂_of_FreshExtension ks mtys EnvSub EnvSup
      EnvSub' EnvSup' mtysSub mtysSup hext hfresh hsub hsup)
    (LMonoTys.knownInstances_of_forall hknown)

/-- Let the smaller aliases be well formed, `S` rename type variables to type
    variables, and the larger aliases extend the smaller ones with fresh aliases
    whose names are unregistered. If the renamed types resolve under the smaller
    aliases to registered instances, then the original types resolve under the
    smaller aliases to their resolution under the larger ones. -/
theorem LMonoTys.resolveAliases_eq_of_FreshExtension_subst {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (C : LContext T) (S : Subst) (mtys : LMonoTys)
    (EnvSub EnvSup EnvSub' EnvSup' : TEnv T.IDMeta)
    (mtysSubS mtysSup : LMonoTys)
    (haWF : TContext.AliasesWF EnvSub.context)
    (hSftvar : ∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y)
    (hext :
      TypeAlias.FreshExtension EnvSub.context.aliases EnvSup.context.aliases)
    (hfresh : ∀ al ∈ EnvSup.context.aliases, al ∉ EnvSub.context.aliases →
        KnownTypes.containsName C.knownTypes al.name = false)
    (hsubS : LMonoTys.resolveAliases (mtys.map (LMonoTy.subst S)) EnvSub
               = .ok (mtysSubS, EnvSub'))
    (hsup : LMonoTys.resolveAliases mtys EnvSup = .ok (mtysSup, EnvSup'))
    (hknown : ∀ mty ∈ mtysSubS, isInstanceOfKnownType mty C = true) :
    LMonoTys.resolveAliases mtys EnvSub = .ok (mtysSup, EnvSub) := by
  obtain ⟨mtysSub, hsub⟩ := LMonoTys.resolveAliases_isOk mtys EnvSub
  have hcomm : mtysSubS = mtysSub.map (LMonoTy.subst S) :=
    LMonoTys.resolveAliases_subst_comm S mtys EnvSub mtysSub mtysSubS EnvSub
      EnvSub' haWF hSftvar hsub hsubS
  have hk : ∀ mty ∈ mtysSub, LMonoTy.knownInstance mty C.knownTypes = true := by
    intro mty hmty
    simp only [isInstanceOfKnownType] at hknown
    refine knownInstance_of_subst C.knownTypes S mty ?_
    refine hknown (LMonoTy.subst S mty) ?_
    rw [hcomm]
    exact List.mem_map_of_mem hmty
  rw [LMonoTys.resolveAliases_eq_of_FreshExtension C.knownTypes mtys EnvSub
    EnvSup EnvSub EnvSup' mtysSub mtysSup hext hfresh hsub hsup hk]
  exact hsub

/-- Resolving a concatenation concatenates the resolutions. -/
private theorem LMonoTys.resolveAliases_append {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (as bs : LMonoTys) (Env : TEnv IDMeta) (as' bs' : LMonoTys)
    (ha : LMonoTys.resolveAliases as Env = .ok (as', Env))
    (hb : LMonoTys.resolveAliases bs Env = .ok (bs', Env)) :
    LMonoTys.resolveAliases (as ++ bs) Env = .ok (as' ++ bs', Env) := by
  induction as generalizing as' with
  | nil =>
    simp only [LMonoTys.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at ha
    rw [← ha.1]
    simpa using hb
  | cons hd tl ih =>
    obtain ⟨hdR, hhd⟩ := LMonoTy.resolveAliases_isOk hd Env
    obtain ⟨tlR, htl⟩ := LMonoTys.resolveAliases_isOk tl Env
    have hcons :
        LMonoTys.resolveAliases (hd :: tl) Env = .ok (hdR :: tlR, Env) := by
      simp only [LMonoTys.resolveAliases, bind, Except.bind, hhd, htl, pure,
        Except.pure]
    have hasR : as' = hdR :: tlR := by
      rw [hcons] at ha
      simp only [Except.ok.injEq, Prod.mk.injEq] at ha
      exact ha.1.symm
    rw [hasR]
    simp only [List.cons_append, LMonoTys.resolveAliases, bind, Except.bind,
      hhd, ih tlR htl, pure, Except.pure]

/-- A successful resolution of a concatenation splits into resolutions of the
    parts. -/
theorem LMonoTys.resolveAliases_append_inv {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (as bs : LMonoTys) (Env Env' : TEnv IDMeta) (rs : LMonoTys)
    (h : LMonoTys.resolveAliases (as ++ bs) Env = .ok (rs, Env')) :
    ∃ as' bs', LMonoTys.resolveAliases as Env = .ok (as', Env) ∧
      LMonoTys.resolveAliases bs Env = .ok (bs', Env) ∧ rs = as' ++ bs' := by
  obtain ⟨as', has⟩ := LMonoTys.resolveAliases_isOk as Env
  obtain ⟨bs', hbs⟩ := LMonoTys.resolveAliases_isOk bs Env
  refine ⟨as', bs', has, hbs, ?_⟩
  rw [LMonoTys.resolveAliases_append as bs Env as' bs' has hbs] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1.symm

/-- Signature instantiation renames type variables and resolves aliases to
    registered instances. -/
theorem LMonoTySignature.instantiate_resolveAliases_subst {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (C : LContext T) (Env EnvR : TEnv T.IDMeta) (tyArgs : List TyIdentifier)
    (sig sig' : @LMonoTySignature T.IDMeta)
    (h : LMonoTySignature.instantiate C Env tyArgs sig = .ok (sig', EnvR)) :
    ∃ (S : Subst) (EnvI : TEnv T.IDMeta),
      (∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
      EnvI.context = Env.context ∧
      LMonoTys.resolveAliases (sig.values.map (LMonoTy.subst S)) EnvI
        = .ok (sig'.values, EnvR) ∧
      ∀ mty ∈ sig'.values, isInstanceOfKnownType mty C = true := by
  obtain ⟨mtysI, EnvI, hI, hres, hknown⟩ :=
    LMonoTySignature.instantiate_resolveAliases C Env EnvR tyArgs sig sig' h
  obtain ⟨S, hSftvar, hmtysI, hctxI⟩ :=
    LMonoTys.instantiateEnv_subst tyArgs sig.values Env mtysI EnvI hI
  rw [hmtysI] at hres
  exact ⟨S, EnvI, hSftvar, hctxI, hres, hknown⟩

/-- A successful identifier lookup instantiates its scheme and applies the new
    substitution. -/
theorem Identifier.instantiateAndSubst_inv {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (x : T.Identifier) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : Identifier.instantiateAndSubst x C Env = .ok (some (mty, Env'))) :
    ∃ ty mtyR, HMaps.find? Env.context.types x = some ty ∧
      LTy.instantiateWithCheck ty C Env = .ok (mtyR, Env') ∧
      mty = LMonoTy.subst Env'.stateSubstInfo.subst mtyR := by
  simp only [Identifier.instantiateAndSubst] at h
  cases hty : HMaps.find? Env.context.types x with
  | none => rw [hty] at h; exact absurd h (by simp [pure, Except.pure])
  | some ty =>
    rw [hty] at h
    simp only [LTy.instantiateAndSubst, bind, Except.bind, pure,
      Except.pure] at h
    cases hv : LTy.instantiateWithCheck ty C Env with
    | error e => rw [hv] at h; exact absurd h (by simp)
    | ok v =>
      obtain ⟨mtyR, EnvR⟩ := v
      rw [hv] at h
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ty, mtyR, rfl, hv, rfl⟩

/-- Looking up a nonempty identifier list looks up the head, then the tail. -/
theorem Identifier.instantiateAndSubsts_cons_inv {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    {x : T.Identifier} {xs : List T.Identifier}
    {C : LContext T} {Env Env' : TEnv T.IDMeta} {mtys : List LMonoTy}
    (h : Identifier.instantiateAndSubsts (x :: xs) C Env =
      .ok (some (mtys, Env'))) :
    ∃ xty EnvA xtys,
      Identifier.instantiateAndSubst x C Env = .ok (some (xty, EnvA)) ∧
      Identifier.instantiateAndSubsts xs C EnvA = .ok (some (xtys, Env')) ∧
      mtys = xty :: xtys := by
  simp only [Identifier.instantiateAndSubsts, bind, Except.bind, pure,
    Except.pure] at h
  cases hhd : Identifier.instantiateAndSubst x C Env with
  | error e => rw [hhd] at h; exact absurd h (by simp)
  | ok ans =>
    rw [hhd] at h
    match ans with
    | none => exact absurd h (by simp)
    | some (xty, EnvA) =>
      simp only at h
      cases htl : Identifier.instantiateAndSubsts xs C EnvA with
      | error e => rw [htl] at h; exact absurd h (by simp)
      | ok anstl =>
        rw [htl] at h
        match anstl with
        | none => exact absurd h (by simp)
        | some (xtys, EnvB) =>
          simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨xty, EnvA, xtys, rfl, htl, rfl⟩

/-- Looking up an identifier's type keeps the context. -/
private theorem Identifier.instantiateAndSubst_context {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (x : T.Identifier) (C : LContext T) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : Identifier.instantiateAndSubst x C Env = .ok (some (mty, Env'))) :
    Env'.context = Env.context := by
  obtain ⟨ty, mtyR, -, hv, -⟩ :=
    Identifier.instantiateAndSubst_inv x C Env mty Env' h
  exact LExpr.LTy_instantiateWithCheck_context' ty C Env mtyR Env' hv

/-- Looking up identifiers' types keeps the context. -/
theorem Identifier.instantiateAndSubsts_context {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (xs : List T.Identifier) (C : LContext T) (Env : TEnv T.IDMeta)
    (mtys : List LMonoTy) (Env' : TEnv T.IDMeta)
    (h : Identifier.instantiateAndSubsts xs C Env = .ok (some (mtys, Env'))) :
    Env'.context = Env.context := by
  induction xs generalizing Env mtys with
  | nil =>
    simp only [Identifier.instantiateAndSubsts, pure, Except.pure,
      Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
  | cons x xrest ih =>
    obtain ⟨xty, EnvA, xtys, hhd, htl, -⟩ :=
      Identifier.instantiateAndSubsts_cons_inv h
    rw [ih EnvA xtys htl]
    exact Identifier.instantiateAndSubst_context x C Env xty EnvA hhd

/-- When every existing alias body is alias-free, a successful declaration of
    `al` prepends one alias with `al`'s name and type parameters whose body is
    alias-free under the existing aliases and uses only registered type
    constructors. -/
theorem addTypeAlias_stored {T : LExprParams} [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] (al : TypeAlias)
    (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (hres : TContext.AliasesResolved Env.context)
    (h : TEnv.addTypeAlias al C Env = .ok Env') :
    ∃ stored : TypeAlias,
      Env'.context.aliases = stored :: Env.context.aliases ∧
      stored.name = al.name ∧ stored.typeArgs = al.typeArgs ∧
      LMonoTy.aliasFree Env.context.aliases stored.type ∧
      LMonoTy.knownInstance stored.type C.knownTypes = true := by
  obtain ⟨-, -, -, -, -, rhsResolved, EnvA, hra, haliases, -, -, -, hsource⟩ :=
    addTypeAlias_decompose al C Env Env' h
  have haf : LMonoTy.aliasFree Env.context.aliases rhsResolved :=
    resolveAliases_output_aliasFree al.type Env rhsResolved EnvA hra hres
  have hknown : rhsResolved.knownInstance C.knownTypes = true :=
    (LMonoTy.typeCheckSource_ok_inv
      al.type rhsResolved C Env EnvA TyVarAdmissibility.all hsource).2.2
  exact ⟨{ name := al.name, typeArgs := al.typeArgs, type := rhsResolved },
    haliases, rfl, rfl, haf, hknown⟩

/-- If alias bodies are alias-free registered instances, a new synonym keeps
    them registered. -/
theorem aliasBodiesKnown_addTypeAlias {T : LExprParams} [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] (al : TypeAlias)
    (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (hres : TContext.AliasesResolved Env.context)
    (h : TEnv.addTypeAlias al C Env = .ok Env')
    (hold : ∀ a ∈ Env.context.aliases,
      LMonoTy.knownInstance a.type C.knownTypes = true) :
    ∀ a ∈ Env'.context.aliases,
      LMonoTy.knownInstance a.type C.knownTypes = true := by
  obtain ⟨stored, hlist, _, _, _, hstored⟩ :=
    addTypeAlias_stored al C Env Env' hres h
  intro a ha
  rw [hlist] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hstored
  · exact hold a ha

mutual
/-- A registered instance is alias-free for aliases with unregistered names. -/
theorem aliasFree_of_knownInstance (known : KnownTypes)
    (aliases : List TypeAlias)
    (hfresh : ∀ al ∈ aliases, KnownTypes.containsName known al.name = false)
    (mty : LMonoTy) (hkn : LMonoTy.knownInstance mty known = true) :
    LMonoTy.aliasFree aliases mty := by
  match mty with
  | .ftvar _ => simp only [LMonoTy.aliasFree]
  | .bitvec _ => simp only [LMonoTy.aliasFree]
  | .tcons name args =>
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at hkn
    simp only [LMonoTy.aliasFree]
    refine ⟨?_, aliasFrees_of_knownInstances known aliases hfresh args hkn.2⟩
    refine List.find?_eq_none.mpr ?_
    intro al hal
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro hnm
    have hcn : KnownTypes.containsName known name = true :=
      containsName_of_contains known { name := name, metadata := args.length }
        hkn.1
    have hno : KnownTypes.containsName known al.name = false := hfresh al hal
    rw [hnm, hcn] at hno
    exact absurd hno (by simp)

/-- Registered instances are alias-free for aliases with unregistered names. -/
private theorem aliasFrees_of_knownInstances (known : KnownTypes)
    (aliases : List TypeAlias)
    (hfresh : ∀ al ∈ aliases, KnownTypes.containsName known al.name = false)
    (mtys : LMonoTys) (hkn : LMonoTys.knownInstances mtys known = true) :
    LMonoTys.aliasFree aliases mtys := by
  match mtys with
  | [] => simp only [LMonoTys.aliasFree]
  | m :: rest =>
    simp only [LMonoTys.knownInstances] at hkn
    elim_err hkn with hm
    simp only [LMonoTys.aliasFree]
    exact ⟨aliasFree_of_knownInstance known aliases hfresh m hm,
      aliasFrees_of_knownInstances known aliases hfresh rest hkn⟩
end

end -- public section

end Lambda
