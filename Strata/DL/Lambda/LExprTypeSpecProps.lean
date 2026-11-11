/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.KnownTypesProps
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprAnnotRel
import all Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.LExprTProps
import all Strata.DL.Lambda.LExprWFProps
public import Strata.DL.Lambda.LExprTypeEnvProps
import all Strata.DL.Lambda.LExprTypeEnvProps
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LExprProps
public import Strata.DL.Lambda.LTyWFProps
public import Strata.DL.Lambda.LTyWFCheckSound
import all Strata.DL.Lambda.LTyWF
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.LTyUnifyProps
import all Strata.Util.HMap
import all Strata.Util.HMaps
import all Strata.Util.HMapsProps
import all Strata.DL.Lambda.Identifiers
import all Strata.DL.Lambda.IdentifiersProps
import all Strata.DL.Util.Func
import all Strata.Util.ListMap
import all Strata.Util.ListMapProps
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps
import all Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LExprAliasFree
import all Strata.DL.Lambda.TypeFactory
public import Strata.Util.ExceptProps
public import Strata.Util.StringProps
public meta import Init.Grind.Cases

/-! # Properties of Lambda expression typing

Key theorems, by group: `TContext.FindEq_subst_of_closed` and `WellScoped_of_freeVarCheck`
(context agreement and scoping); `Constraints.unify_varsAvoid` and
`Constraints.unify_tailClear` (what unification keeps out of a substitution);
`HasType_of_AnnotInstRewrite` and `HasType_openAll` (typing under re-annotation and under opening
a quantifier prefix); `TContext.dealias_find?` (lookup after alias resolution);
`resolveAux_context_equiv` (the resolver keeps its context up to `Equiv`);
`resolve_resolveAux_init` (what `resolve` runs `resolveAux` from);
`resolveAux_RangeKnown`, `resolveAux_varsAvoid` and `resolveAux_tailClear` (the
substitution and annotations stay registered, avoid given names, and keep older
scopes clear), where the first two also have `resolve` forms
`resolve_RangeKnown` and `resolve_varsAvoid`; and `resolve_HasType_toLMonoTy`
(`resolve` types an expression at its reported monotype). -/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)
open Strata.Util (HMap HMaps)

public section

open LTy

namespace LExpr

variable {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]

section Proofs
attribute [local simp] Pure.pure Except.pure

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta]
  [Std.ToFormat T.IDMeta] [Std.ToFormat (LFunc T)]
  [Std.ToFormat T.Metadata] [Hashable T.IDMeta]


omit [ToString T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- The default environment is well formed. -/
theorem TEnvWF_default : TEnvWF (T := T) (TEnv.default (IDMeta := T.IDMeta)) where
  aliasesWF := by
    intro a ha
    exact absurd ha (by simp [TEnv.default, TEnv.context])
  substFreshForGen := by
    intro v hv n hn
    simp [TEnv.default, SubstInfo.empty, Subst.empty, Subst.freeVars,
      HMaps.keys, HMaps.values] at hv
  ctxFreshForGen := by
    intro v hv n hn
    simp [TEnv.default, TEnv.context, TContext.knownTypeVars, HMaps.values] at hv
  boundVarsNodup := by
    intro y ty h
    simp [TEnv.default, TEnv.context, HMaps.find?] at h
  boundVarsFresh := by
    intro y ty h
    simp [TEnv.default, TEnv.context, HMaps.find?] at h

end Proofs

end LExpr

section TContextEquiv
open LExpr
open Strata.Util (HMap HMaps)
/-! ### Typing-context agreement: `Equiv` (scope by scope) and `FindEq` (whole-stack lookups) -/

variable {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]

/-- `FindEq` contexts give the same lookup for every identifier. -/
theorem TContext.FindEq.find? {Γ Γ' : TContext T.IDMeta} (h : TContext.FindEq Γ Γ')
    (k : Identifier T.IDMeta) : Γ.types.find? k = Γ'.types.find? k := h.1 k

/-- `FindEq` is reflexive. -/
@[refl] theorem TContext.FindEq.refl (Γ : TContext T.IDMeta) : Γ.FindEq Γ :=
  ⟨fun _ => rfl, rfl⟩

/-- `FindEq` is symmetric. -/
theorem TContext.FindEq.symm {Γ Γ' : TContext T.IDMeta} (h : Γ.FindEq Γ') : Γ'.FindEq Γ :=
  ⟨fun k => (h.1 k).symm, h.2.symm⟩

/-- `FindEq` is transitive. -/
theorem TContext.FindEq.trans {Γ Γ' Γ'' : TContext T.IDMeta}
    (h1 : Γ.FindEq Γ') (h2 : Γ'.FindEq Γ'') : Γ.FindEq Γ'' :=
  ⟨fun k => (h1.1 k).trans (h2.1 k), h1.2.trans h2.2⟩

/-- Pushing an empty scope preserves all lookups and aliases. -/
theorem pushEmptyContext_context_FindEq (Env : TEnv T.IDMeta) :
    TContext.FindEq (T := T) (Env.pushEmptyContext).context Env.context := by
  refine ⟨fun k => ?_, rfl⟩
  show ((Env.context.types).push .empty).find? k = (Env.context.types).find? k
  simp only [Strata.Util.HMaps.push, Strata.Util.HMaps.find?, Strata.Util.HMap.find?_empty]

/-- `HasType` does not read the context's `idents` field. -/
theorem HasType_idents_irrel (C : LContext T) (j : Identifiers T.IDMeta)
    (Γ : TContext T.IDMeta) (e : LExpr T.mono) (t : LTy)
    (h : HasType {C with idents := j} Γ e t) : HasType C Γ e t := by
  induction h with
  | tbool_const Γ m b h => exact .tbool_const Γ m b h
  | tint_const Γ m n h => exact .tint_const Γ m n h
  | treal_const Γ m r h => exact .treal_const Γ m r h
  | tstr_const Γ m s h => exact .tstr_const Γ m s h
  | tbitvec_const Γ m n b h => exact .tbitvec_const Γ m n b h
  | tmap_const Γ m k v d es h hw => exact .tmap_const Γ m k v d es h hw
  | tseq_const Γ m a es h hw => exact .tseq_const Γ m a es h hw
  | tvar Γ m x ty h_find => exact .tvar Γ m x ty h_find
  | tvar_annotated Γ m x ty_o ty_s tys ann h_find h_len h_open h_ac =>
    exact .tvar_annotated Γ m x ty_o ty_s tys ann h_find h_len h_open h_ac
  | tabs Γ m name x x_ty e e_ty o h_fresh hx he _ h_o h_valid ih =>
    exact .tabs Γ m name x x_ty e e_ty o h_fresh hx he ih h_o
      (fun t ht => (h_valid t ht).imp fun _ hr =>
        SourceTyWF.of_knownTypes_eq (C := { C with idents := j }) rfl hr)
  | tapp Γ m e1 e2 t1 t2 h1 h2 _ _ ih1 ih2 =>
    exact .tapp Γ m e1 e2 t1 t2 h1 h2 ih1 ih2
  | tinst Γ e ty e_ty x x_ty _ h_open ih =>
    exact .tinst Γ e ty e_ty x x_ty ih h_open
  | tgen Γ e a ty _ h_fresh ih => exact .tgen Γ e a ty ih h_fresh
  | tif Γ m c e1 e2 ty _ _ _ ihc ih1 ih2 => exact .tif Γ m c e1 e2 ty ihc ih1 ih2
  | teq Γ m e1 e2 ty _ _ ih1 ih2 => exact .teq Γ m e1 e2 ty ih1 ih2
  | tquant Γ m k name tr tr_ty x x_ty e o h_fresh hx _ _ h_o h_valid ihe ihtr =>
    exact .tquant Γ m k name tr tr_ty x x_ty e o h_fresh hx ihe ihtr h_o
      (fun t ht => (h_valid t ht).imp fun _ hr =>
        SourceTyWF.of_knownTypes_eq (C := { C with idents := j }) rfl hr)
  | top Γ m f op ty h_find h_type => exact .top Γ m f op ty h_find h_type
  | top_annotated Γ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_ac =>
    exact .top_annotated Γ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_ac
  | talias Γ e mty mty' h_ae _ ih => exact .talias Γ e mty mty' h_ae ih

/-- Resetting the substitution preserves `TEnvWF`. -/
theorem TEnv.updateSubst_globalScope_preserves_TEnvWF
    (Env : TEnv T.IDMeta) (h_env : TEnvWF Env) :
    TEnvWF
      (Env.updateSubst { subst := Subst.empty.push (HMap.empty : SubstOne),
                         isWF := SubstWF_of_pushEmptyScope _ SubstWF_of_empty }) := by
  refine { aliasesWF := h_env.aliasesWF, ctxFreshForGen := h_env.ctxFreshForGen,
           boundVarsNodup := h_env.boundVarsNodup, boundVarsFresh := h_env.boundVarsFresh,
           substFreshForGen := ?_ }
  intro v hv n hn
  simp [TEnv.updateSubst, Subst.empty, Subst.freeVars, HMaps.keys, HMaps.values, HMaps.push] at hv

/-- Pushing the same scope onto two `FindEq` contexts preserves `FindEq`. -/
theorem push_FindEq (Γ Ξ : TContext T.IDMeta)
    (scope : HMap (Identifier T.IDMeta) LTy) (hEq : TContext.FindEq Ξ Γ) :
    TContext.FindEq
      { Ξ with types := Ξ.types.push scope } { Γ with types := Γ.types.push scope } := by
  refine ⟨fun k => ?_, hEq.2⟩
  show (Strata.Util.HMaps.push _ _).find? k = (Strata.Util.HMaps.push _ _).find? k
  simp only [Strata.Util.HMaps.push, Strata.Util.HMaps.find?]
  cases scope.find? k with
  | none => simpa using hEq.find? k
  | some v => rfl

/-- Adding bindings to a pushed empty scope is `FindEq` to pushing them as a scope. -/
theorem push_addInNewestContext_FindEq (Env : TEnv T.IDMeta)
    (scope : HMap (Identifier T.IDMeta) LTy) :
    TContext.FindEq (T := T)
      { Env.context with types := Env.context.types.push scope }
      ((Env.pushEmptyContext).addInNewestContext (T := T) scope).context := by
  refine ⟨fun k => ?_, rfl⟩
  have htys : ((Env.pushEmptyContext).addInNewestContext (T := T) scope).context.types
      = (scope.union HMap.empty) :: Env.context.types := by
    simp only [TEnv.addInNewestContext, TEnv.pushEmptyContext, TEnv.updateContext,
      TEnv.context, Strata.Util.HMaps.push, Strata.Util.HMaps.addInNewest]
  rw [htys]
  simp only [Strata.Util.HMaps.push, Strata.Util.HMaps.find?, HMap.find?_union,
    HMap.find?_empty, Option.none_or]

/-- `AliasesResolved` carries over to `Equiv` contexts. -/
theorem TContext.Equiv.aliasesResolved {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ')
    (h_ar : TContext.AliasesResolved Γ) : TContext.AliasesResolved Γ' := by
  intro a ha
  rw [← h.2]
  rw [← h.2] at ha
  exact h_ar a ha

/-- Popping `Env`'s context preserves `TEnvWF` when the result is `Equiv` to the context of a
    `TEnvWF` environment whose generator counter is at most `Env`'s. -/
theorem popContext_preserves_TEnvWF
    (Env₀ Env : TEnv T.IDMeta)
    (h_orig : LExpr.TEnvWF (T := T) Env₀)
    (h_ego : LExpr.TEnvWF (T := T) Env)
    (hmono : Env₀.genEnv.genState.tyGen ≤ Env.genEnv.genState.tyGen)
    (hEquiv : TContext.Equiv (T := T) (Env.popContext).context Env₀.context) :
    LExpr.TEnvWF (T := T) (Env.popContext) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hEquiv.symm.aliasesWF h_orig.aliasesWF
  · exact h_ego.substFreshForGen
  · have hcf : LExpr.ContextFreshForGen (T := T) Env₀.context Env.genEnv.genState := by
      intro v hv n hn
      exact h_orig.ctxFreshForGen v hv n (Nat.le_trans hmono hn)
    exact hEquiv.symm.ctxFreshForGen hcf
  · exact hEquiv.symm.boundVarsNodup h_orig.boundVarsNodup
  · have hbf : ∀ y ty, Env₀.context.types.find? y = some ty →
        ∀ v, v ∈ LTy.boundVars ty →
          ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
      intro y ty hfind v hv n hn
      exact h_orig.boundVarsFresh y ty hfind v hv n (Nat.le_trans hmono hn)
    exact hEquiv.symm.boundVarsFresh hbf

end TContextEquiv

namespace LExpr

section Proofs
attribute [local simp] Pure.pure Except.pure
variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta]
  [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Installing a unifier preserves `TEnvWF` if no constraint variable is a future generated name. -/
theorem TEnvWF_updateSubst_of_unify
    (Env : TEnv T.IDMeta) (cs : Constraints) (S : SubstInfo)
    (h_env : TEnvWF Env) (h_unify : Constraints.unify cs Env.stateSubstInfo = .ok S)
    (h_fresh_cs : ∀ v, v ∈ Constraints.freeVars cs →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    TEnvWF (Env.updateSubst S) := by
  exact {
    aliasesWF := h_env.aliasesWF
    substFreshForGen := by
      intro v hv n hn
      rcases Constraints.unify_vars_mem h_unify v hv with h_cs | h_S
      · exact h_fresh_cs v h_cs n hn
      · exact h_env.substFreshForGen v h_S n hn
    ctxFreshForGen := h_env.ctxFreshForGen
    boundVarsNodup := h_env.boundVarsNodup
    boundVarsFresh := h_env.boundVarsFresh
  }

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta]
  [ToFormat (LFunc T)] [ToFormat T.Metadata] in
/-- Substituting into a context of closed schemes keeps it `FindEq` to the original. -/
theorem TContext.FindEq_subst_of_closed (Γ : TContext T.IDMeta) (S : Subst)
    (h : ∀ y ty, Γ.types.find? y = some ty → LTy.freeVars ty = []) :
    TContext.FindEq (T := T) Γ (TContext.subst Γ S) := by
  refine ⟨fun k => ?_, by rw [TContext.subst_aliases]⟩
  cases hf : HMaps.find? Γ.types k with
  | none =>
    cases hf' : HMaps.find? (TContext.subst Γ S).types k with
    | none => rfl
    | some ty' =>
      obtain ⟨ty0, h0, -⟩ := TContext_types_subst_find_reverse Γ.types S k ty' hf'
      rw [h0] at hf; exact absurd hf (by simp)
  | some ty =>
    have hclosed := h k ty hf
    have hsub : HMaps.find? (TContext.subst Γ S).types k = some (LTy.subst S ty) :=
      TContext_types_subst_find Γ.types S k ty hf
    have hid : LTy.subst S ty = ty := by
      cases ty with
      | forAll vs mty =>
        simp only [LTy.freeVars] at hclosed
        simp only [LTy.subst]
        congr 1
        refine LMonoTy.subst_no_key_free _ mty ?_
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro k' hk' hmem
        have hnotvs : k' ∉ vs := subst_go_key_not_in_removed S vs k' hk'
        have hfv : k' ∈ (LMonoTy.freeVars mty).removeAll vs := by
          simp only [List.removeAll, List.mem_filter, hmem, true_and, Bool.not_eq_true']
          simpa [List.elem_eq_mem] using hnotvs
        rw [hclosed] at hfv
        exact absurd hfv (by simp)
    rw [hsub, hid]

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Substituting into a context storing only closed schemes gives an `Equiv` context. -/
private theorem TContext.subst_closed_Equiv (Env : TEnv T.IDMeta) (S : Subst)
    (h_check : checkContextTypesClosed Env) :
    (TContext.subst Env.context S).Equiv Env.context := by
  refine ⟨?_, TContext.subst_aliases Env.context S⟩
  show HMaps.Equiv (Env.context.types.mapValues (LTy.subst S)) Env.context.types
  apply HMaps.mapValues_fix_Equiv
  intro ty h_mem
  have h_fv : LTy.freeVars ty = [] :=
    (checkContextTypesClosed_iff_values Env).mp h_check ty h_mem
  cases ty with
  | forAll xs body =>
    show LTy.forAll xs (LMonoTy.subst (LTy.subst.go xs S) body) = LTy.forAll xs body
    have h_body : LMonoTy.subst (LTy.subst.go xs S) body = body := by
      apply subst_go_eq_self_of_irrelevant_keys
      intro k _ hk_not_xs hk_fv
      have h_rem : k ∈ (LMonoTy.freeVars body).removeAll xs := by
        simp only [List.removeAll, List.mem_filter, List.elem_eq_mem,
          Bool.not_eq_true', decide_eq_false_iff_not]
        exact ⟨hk_fv, hk_not_xs⟩
      rw [show (LMonoTy.freeVars body).removeAll xs = LTy.freeVars (LTy.forAll xs body) from rfl,
        h_fv] at h_rem
      exact absurd h_rem List.not_mem_nil
    rw [h_body]

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- Resolving a well-scoped expression in a context storing only closed schemes gives input typing
    at the reported monotype and keeps the context closed. -/
theorem resolve_HasType_toLMonoTy
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h_res : e.resolve C Env = .ok (e_typed, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions)
    (h_ws : WellScoped e Env.context)
    (h_check : checkContextTypesClosed Env) :
    HasType C Env.context e (.forAll [] e_typed.toLMonoTy) ∧ checkContextTypesClosed Env' := by
  have ⟨h_ht, _, h_check', _⟩ :=
    resolve_HasType e e_typed C Env Env' h_res h_envwf h_fwf h_ws h_check
  exact ⟨HasType_Equiv h_ht (TContext.subst_closed_Equiv Env Env'.stateSubstInfo.subst h_check),
    h_check'⟩

/-! ### Alias-equivalent scope stacks, and scoping from `freeVarCheck` -/

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)]
  [ToFormat T.Metadata] in
/-- Binding a name to one scheme in two alias-equivalent stacks (`ScopeRel`) keeps them so. -/
theorem ScopeRel.insert {aliases : List TypeAlias}
    {tsD tsR : HMaps (Identifier T.IDMeta) LTy} (h : ScopeRel (T := T) aliases tsD tsR)
    (x : Identifier T.IDMeta) (t : LTy) :
    ScopeRel (T := T) aliases (tsD.insert x t) (tsR.insert x t) := by
  intro k
  by_cases hk : k = x
  · subst hk
    refine Or.inl ?_
    rw [HMaps.find?_insert_self, HMaps.find?_insert_self]
  · rw [HMaps.find?_insert_ne _ k x t hk, HMaps.find?_insert_ne _ k x t hk]
    exact h k

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)]
  [ToFormat T.Metadata] in
/-- Alias-equivalent scope stacks (`ScopeRel`) agree on which type variables are fresh. -/
private theorem ScopeRel.isFresh {Γ : TContext T.IDMeta} {tsD tsR : HMaps (Identifier T.IDMeta) LTy}
    (hwf : ∀ a ∈ Γ.aliases, TypeAlias.WF a) (h : ScopeRel (T := T) Γ.aliases tsD tsR)
    {tx : TyIdentifier} (hfr : TContext.isFresh (T := T) tx { Γ with types := tsR }) :
    TContext.isFresh (T := T) tx { Γ with types := tsD } := by
  intro x ty hfind
  have hfind' : tsD.find? x = some ty := hfind
  rcases h x with heq | ⟨d, r, hd, hr, hae⟩
  · have hfind_R : tsR.find? x = some ty := by rw [← heq]; exact hfind'
    exact hfr x ty hfind_R
  · rw [hd] at hfind'
    have hty : ty = LTy.forAll [] d := by injection hfind' with hty; exact hty.symm
    subst hty
    have hnotin : tx ∉ LTy.freeVars (LTy.forAll [] r) := hfr x _ hr
    intro hmem
    have hmemd : tx ∈ LMonoTy.freeVars d := by
      simpa [LTy.freeVars, List.removeAll] using hmem
    have hmemr : tx ∈ LMonoTy.freeVars r := (AliasEquiv.freeVars_iff hwf hae tx).mp hmemd
    have hmemr' : tx ∈ LTy.freeVars (LTy.forAll [] r) := by
      simpa [LTy.freeVars, List.removeAll] using hmemr
    exact hnotin hmemr'

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)]
  [ToFormat T.Metadata] in
/-- Typing derivations carry over between alias-equivalent scope stacks (`ScopeRel`). -/
theorem HasType_ScopeRel (C : LContext T) (ΓR : TContext T.IDMeta)
    (e : LExpr T.mono) (t : LTy) (h : HasType C ΓR e t) :
    ∀ tsD, (∀ a ∈ ΓR.aliases, TypeAlias.WF a) → ScopeRel (T := T) ΓR.aliases tsD ΓR.types →
      HasType C { ΓR with types := tsD } e t := by
  induction h with
  | tbool_const Γ m b hk => exact fun tsD _ _ => .tbool_const _ m b hk
  | tint_const Γ m n hk => exact fun tsD _ _ => .tint_const _ m n hk
  | treal_const Γ m r hk => exact fun tsD _ _ => .treal_const _ m r hk
  | tstr_const Γ m s hk => exact fun tsD _ _ => .tstr_const _ m s hk
  | tbitvec_const Γ m n b hk => exact fun tsD _ _ => .tbitvec_const _ m n b hk
  | tmap_const Γ m k v d es hk hw => exact fun tsD _ _ => .tmap_const _ m k v d es hk hw
  | tseq_const Γ m a es hk hw => exact fun tsD _ _ => .tseq_const _ m a es hk hw
  | tvar Γ m x ty h_find =>
    intro tsD hwf hrel
    rcases hrel x with heq | ⟨d, r, hd, hr, hae⟩
    · exact .tvar _ m x ty (heq.trans h_find)
    · have hty : ty = LTy.forAll [] r := Option.some_inj.mp (h_find.symm.trans hr)
      rw [hty]
      exact .talias _ _ d r hae (.tvar _ m x (LTy.forAll [] d) hd)
  | tvar_annotated Γ m x ty_o ty_s tys ann h_find h_len h_open h_ac =>
    intro tsD hwf hrel
    rcases hrel x with heq | ⟨d, r, hd, hr, hae⟩
    · exact .tvar_annotated _ m x ty_o ty_s tys ann (heq.trans h_find) h_len h_open h_ac
    · have hty : ty_o = LTy.forAll [] r := Option.some_inj.mp (h_find.symm.trans hr)
      have hbv_r : (LTy.forAll [] r).boundVars = [] := by simp [LTy.boundVars]
      have hbv_d : (LTy.forAll [] d).boundVars = [] := by simp [LTy.boundVars]
      have hsr : ty_s = r := by
        rw [← h_open, hty]
        exact openFull_of_boundVars_nil (LTy.forAll [] r) hbv_r _
      have hacd : AnnotCompat Γ.aliases ann d := by
        obtain ⟨σ, hσ⟩ := h_ac
        exact ⟨σ, AliasEquiv.trans (hsr ▸ hσ) (AliasEquiv.symm hae)⟩
      have hlen_d : ([] : List LMonoTy).length = (LTy.forAll [] d).boundVars.length := by
        rw [hbv_d]; rfl
      have hbase : HasType C { Γ with types := tsD } (.fvar m x (some ann)) (.forAll [] d) :=
        .tvar_annotated _ m x (LTy.forAll [] d) d [] ann hd hlen_d
          (openFull_of_boundVars_nil (LTy.forAll [] d) hbv_d _) hacd
      rw [hsr]
      exact .talias _ _ d r hae hbase
  | tabs Γ m name x x_ty e e_ty o h_fresh hx he _ h_o h_valid ih =>
    intro tsD hwf hrel
    exact .tabs _ m name x x_ty e e_ty o h_fresh hx he
      (ih (tsD.insert x.fst x_ty) hwf (hrel.insert x.fst x_ty)) h_o h_valid
  | tapp Γ m e1 e2 t1 t2 h1 h2 _ _ ih1 ih2 =>
    intro tsD hwf hrel
    exact .tapp _ m e1 e2 t1 t2 h1 h2 (ih1 tsD hwf hrel) (ih2 tsD hwf hrel)
  | tinst Γ e ty e_ty x x_ty _ h_open ih =>
    intro tsD hwf hrel
    exact .tinst _ e ty e_ty x x_ty (ih tsD hwf hrel) h_open
  | tgen Γ e a ty _ h_fresh ih =>
    intro tsD hwf hrel
    exact .tgen _ e a ty (ih tsD hwf hrel) (ScopeRel.isFresh (Γ := Γ) hwf hrel h_fresh)
  | tif Γ m c e1 e2 ty _ _ _ ihc ih1 ih2 =>
    intro tsD hwf hrel
    exact .tif _ m c e1 e2 ty (ihc tsD hwf hrel) (ih1 tsD hwf hrel) (ih2 tsD hwf hrel)
  | teq Γ m e1 e2 ty _ _ ih1 ih2 =>
    intro tsD hwf hrel
    exact .teq _ m e1 e2 ty (ih1 tsD hwf hrel) (ih2 tsD hwf hrel)
  | tquant Γ m k name tr tr_ty x x_ty e o h_fresh hx _ _ h_o h_valid ihe ihtr =>
    intro tsD hwf hrel
    exact .tquant _ m k name tr tr_ty x x_ty e o h_fresh hx
      (ihe (tsD.insert x.fst x_ty) hwf (hrel.insert x.fst x_ty))
      (ihtr (tsD.insert x.fst x_ty) hwf (hrel.insert x.fst x_ty)) h_o h_valid
  | top Γ m f op ty h_find h_type => exact fun tsD _ _ => .top _ m f op ty h_find h_type
  | top_annotated Γ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_ac =>
    exact fun tsD _ _ => .top_annotated _ m f op ty_o ty_s tys ann h_find h_type h_len h_open h_ac
  | talias Γ e mty mty' h_ae _ ih =>
    intro tsD hwf hrel
    exact .talias _ e mty mty' h_ae (ih tsD hwf hrel)

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)]
  [ToFormat T.Metadata] in
/-- Pushing alias-equivalent signatures onto one stack gives alias-equivalent stacks. -/
theorem scopeRel_push (Γ : TContext T.IDMeta) (sigD sigR : @LMonoTySignature T.IDMeta)
    (h_keys : sigD.keys = sigR.keys)
    (h_vals : AliasEquivList Γ.aliases sigD.values sigR.values) :
    ScopeRel (T := T) Γ.aliases
      (Γ.types.push (HMap.ofList (sigD.map (fun q => (q.1, LTy.forAll [] q.2)))))
      (Γ.types.push (HMap.ofList (sigR.map (fun q => (q.1, LTy.forAll [] q.2))))) := by
  have hpair : List.Rel₂ (fun q qR => q.1 = qR.1 ∧ AliasEquiv Γ.aliases q.2 qR.2) sigD sigR :=
    ListMap.forall₂_pair_of_keys_values sigD sigR h_keys h_vals.forall₂
  intro x
  have hD := HMap.find?_ofList_map_snd sigD (fun m => LTy.forAll [] m) x
  have hR := HMap.find?_ofList_map_snd sigR (fun m => LTy.forAll [] m) x
  rcases List.findSome?_pair_rel x hpair.reverse with ⟨h1, h2⟩ | ⟨d, r, h1, h2, hae⟩
  · rw [← HMap.find?_ofList_findSome? sigD x] at h1
    rw [← HMap.find?_ofList_findSome? sigR x] at h2
    rw [h1, Option.map_none] at hD
    rw [h2, Option.map_none] at hR
    refine Or.inl ?_
    rw [HMaps.find?_push_of_none _ _ x hD, HMaps.find?_push_of_none _ _ x hR]
  · rw [← HMap.find?_ofList_findSome? sigD x] at h1
    rw [← HMap.find?_ofList_findSome? sigR x] at h2
    rw [h1, Option.map_some] at hD
    rw [h2, Option.map_some] at hR
    exact Or.inr ⟨d, r, HMaps.find?_push_of_some _ _ x _ hD,
      HMaps.find?_push_of_some _ _ x _ hR, hae⟩

omit [ToString T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)]
  [ToFormat T.Metadata] in
/-- Replacing a newest monomorphic scope by an alias-equivalent one preserves typing. -/
theorem HasType_pushScope_aliasEquiv (C : LContext T) (Γ : TContext T.IDMeta)
    (sigD sigR : @LMonoTySignature T.IDMeta) (e : LExpr T.mono) (mty : LMonoTy)
    (h_aliasesWF : TContext.AliasesWF Γ)
    (h_keys : sigD.keys = sigR.keys)
    (h_vals : AliasEquivList Γ.aliases sigD.values sigR.values)
    (h : HasType C
      { Γ with types := Γ.types.push (HMap.ofList (sigR.map (fun q => (q.1, LTy.forAll [] q.2)))) }
      e (.forAll [] mty)) :
    HasType C
      { Γ with types := Γ.types.push (HMap.ofList (sigD.map (fun q => (q.1, LTy.forAll [] q.2)))) }
      e (.forAll [] mty) :=
  HasType_ScopeRel C _ e _ h _ h_aliasesWF (scopeRel_push Γ sigD sigR h_keys h_vals)

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- A successful `freeVarCheck` implies `WellScoped`. -/
theorem WellScoped_of_freeVarCheck (Env : TEnv T.IDMeta) (e : LExpr T.mono)
    (msg : Unit → Std.Format) {u : Unit} (h : Env.freeVarCheck e msg = .ok u) :
    WellScoped e Env.context := by
  have h_filter : ((LExpr.freeVars e).map Prod.fst).filter
      (fun v => (Env.context.types.find? v).isNone) = [] := by
    unfold TEnv.freeVarCheck at h
    simp only at h
    split at h
    · assumption
    · simp at h
  intro x hx
  have hx_map : x.1 ∈ (LExpr.freeVars e).map Prod.fst := List.mem_map.mpr ⟨x, hx, rfl⟩
  by_cases h_in : x.1 ∈ Env.context.knownVars
  · exact h_in
  · exfalso
    have h_none : Env.context.types.find? x.1 = none :=
      Strata.Util.HMaps.not_mem_keys_find?_none _ _ h_in
    have h_mem : x.1 ∈ ((LExpr.freeVars e).map Prod.fst).filter
        (fun v => (Env.context.types.find? v).isNone) := by
      simp only [List.mem_filter, h_none, Option.isNone_none]
      exact ⟨hx_map, trivial⟩
    rw [h_filter] at h_mem
    exact absurd h_mem List.not_mem_nil

end Proofs

---------------------------------------------------------------------
end LExpr

/-- Pushing an empty context preserves `TEnvWF`. -/
theorem pushEmptyContext_preserves_TEnvWF {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] (Env : TEnv T.IDMeta)
    (h_env : LExpr.TEnvWF (T := T) Env) :
    LExpr.TEnvWF (T := T) (Env.pushEmptyContext) := by
  have h_types : (Env.pushEmptyContext).context.types
      = HMap.empty :: Env.context.types := by
    simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, HMaps.push]
  have h_find_eq : ∀ y, (Env.pushEmptyContext).context.types.find? y
      = Env.context.types.find? y := by
    intro y
    rw [h_types]
    simp only [HMaps.find?, HMap.find?_empty]
  have h_ktv : TContext.knownTypeVars (Env.pushEmptyContext).context
      = TContext.knownTypeVars Env.context := by
    simp only [TContext.knownTypeVars, h_types, HMaps.values, HMap.values_empty,
      List.nil_append]
  obtain ⟨hAW, hSF, hCF, hBN, hBF⟩ := h_env
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hAW
  · exact hSF
  · intro v hv n hn
    rw [h_ktv] at hv
    exact hCF v hv n hn
  · intro y ty h_find
    rw [h_find_eq] at h_find
    exact hBN y ty h_find
  · intro y ty h_find v hv n hn
    rw [h_find_eq] at h_find
    exact hBF y ty h_find v hv n hn

/-! ### Environment operations that preserve `TEnvWF` -/

/-- Replacing the type scopes with one empty scope preserves `TEnvWF`. -/
theorem LExpr.TEnvWF.updateContext_emptyScope {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] (Env : TEnv T.IDMeta)
    (h_envwf : LExpr.TEnvWF (T := T) Env) :
    LExpr.TEnvWF (T := T) (Env.updateContext { Env.context with types := [HMap.empty] }) := by
  have h_ty_none : ∀ (y : Identifier T.IDMeta) (ty : LTy),
      HMaps.find? ([HMap.empty] : HMaps (Identifier T.IDMeta) LTy) y ≠ some ty := by
    intro y ty hf
    simp only [HMaps.find?, HMap.find?_empty] at hf
    have h_not_some : (none : Option LTy) ≠ some ty := by simp
    exact absurd hf h_not_some
  have h_ktv_empty : TContext.knownTypeVars
      (⟨[HMap.empty], Env.context.aliases⟩ : TContext T.IDMeta) = [] := by
    simp only [TContext.knownTypeVars, HMaps.values, HMap.values_empty,
      List.flatMap_nil, List.append_nil]
  refine ⟨h_envwf.aliasesWF, h_envwf.substFreshForGen, ?_, ?_, ?_⟩
  · intro v hv n hn
    rw [show (Env.updateContext { Env.context with types := [HMap.empty] }).context
      = (⟨[HMap.empty], Env.context.aliases⟩ : TContext T.IDMeta) from rfl,
      h_ktv_empty] at hv
    exact absurd hv List.not_mem_nil
  · intro y ty hf
    exact absurd hf (h_ty_none y ty)
  · intro y ty hf
    exact absurd hf (h_ty_none y ty)

/-- Pushing an empty substitution scope preserves `TEnvWF`. -/
theorem pushEmptySubstScope_preserves_TEnvWF {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] (Env : TEnv T.IDMeta)
    (h_env : LExpr.TEnvWF (T := T) Env) :
    LExpr.TEnvWF (T := T) Env.pushEmptySubstScope := by
  refine { aliasesWF := h_env.aliasesWF, ctxFreshForGen := h_env.ctxFreshForGen,
           boundVarsNodup := h_env.boundVarsNodup, boundVarsFresh := h_env.boundVarsFresh,
           substFreshForGen := ?_ }
  intro v hv n hn
  refine h_env.substFreshForGen v ?_ n hn
  simpa only [TEnv.pushEmptySubstScope, Subst.freeVars, HMaps.push, HMaps.keys, HMaps.values,
    HMap.keys_empty, HMap.values_empty, List.nil_append] using hv

/-- Popping a substitution scope preserves `TEnvWF`. -/
theorem popSubstScope_preserves_TEnvWF {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] (Env : TEnv T.IDMeta)
    (h_env : LExpr.TEnvWF (T := T) Env) :
    LExpr.TEnvWF (T := T) Env.popSubstScope := by
  refine { aliasesWF := h_env.aliasesWF, ctxFreshForGen := h_env.ctxFreshForGen,
           boundVarsNodup := h_env.boundVarsNodup, boundVarsFresh := h_env.boundVarsFresh,
           substFreshForGen := ?_ }
  intro v hv n hn
  refine h_env.substFreshForGen v ?_ n hn
  have hkeys : HMaps.keys (HMaps.pop Env.stateSubstInfo.subst)
      ⊆ HMaps.keys Env.stateSubstInfo.subst := by
    cases hsub : Env.stateSubstInfo.subst with
    | nil => simp [HMaps.pop, HMaps.keys]
    | cons m rest =>
      show HMaps.keys rest ⊆ HMaps.keys (m :: rest)
      simp only [HMaps.keys]
      exact List.subset_append_right _ _
  have hfv : Subst.freeVars (HMaps.pop Env.stateSubstInfo.subst)
      ⊆ Subst.freeVars Env.stateSubstInfo.subst := by
    cases hsub : Env.stateSubstInfo.subst with
    | nil => simp [HMaps.pop, Subst.freeVars, HMaps.values]
    | cons m rest =>
      show Subst.freeVars rest ⊆ Subst.freeVars (m :: rest)
      simp only [Subst.freeVars, HMaps.values, List.flatMap_append]
      exact List.subset_append_right _ _
  simp only [TEnv.popSubstScope] at hv
  rcases hv with hk | hf
  · exact Or.inl (hkeys hk)
  · exact Or.inr (hfv hf)

/-- Pushing a scope whose schemes have no type variables preserves `TEnvWF`. -/
theorem pushEmptyContext_addInNewestContext_preserves_TEnvWF {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (Env : TEnv T.IDMeta) (map : HMap T.Identifier LTy)
    (h_env : LExpr.TEnvWF (T := T) Env)
    (h_map : ∀ ty ∈ map.values, LTy.freeVars ty = [] ∧ LTy.boundVars ty = []) :
    LExpr.TEnvWF (T := T) ((Env.pushEmptyContext).addInNewestContext (T := T) map) := by
  have htys : ((Env.pushEmptyContext).addInNewestContext (T := T) map).context.types
      = (map.union HMap.empty) :: Env.context.types := by
    simp only [TEnv.addInNewestContext, TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context,
      HMaps.push, HMaps.addInNewest]
  have haliases : ((Env.pushEmptyContext).addInNewestContext (T := T) map).context.aliases
      = Env.context.aliases := by
    simp only [TEnv.addInNewestContext, TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
  have hgen : ((Env.pushEmptyContext).addInNewestContext (T := T) map).genEnv.genState
      = Env.genEnv.genState := by
    simp only [TEnv.addInNewestContext, TEnv.pushEmptyContext, TEnv.updateContext]
  have hsub : ((Env.pushEmptyContext).addInNewestContext (T := T) map).stateSubstInfo
      = Env.stateSubstInfo := by
    simp only [TEnv.addInNewestContext, TEnv.pushEmptyContext, TEnv.updateContext]
  have hfind : ∀ y ty,
      HMaps.find? ((Env.pushEmptyContext).addInNewestContext (T := T) map).context.types y
        = some ty →
      (ty ∈ map.values ∨ Env.context.types.find? y = some ty) := by
    intro y ty hy
    rw [htys] at hy
    simp only [HMaps.find?] at hy
    rw [HMap.union_empty] at hy
    split at hy
    · exact Or.inr hy
    · rename_i w hw
      simp only [Option.some.injEq] at hy
      subst hy
      exact Or.inl (HMap.find?_mem_values map hw)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [haliases] at ha
    exact h_env.aliasesWF a ha
  · rw [hsub, hgen]; exact h_env.substFreshForGen
  · intro v hv n hn
    rw [hgen] at hn
    simp only [TContext.knownTypeVars, htys, HMaps.values, List.flatMap_append,
      List.mem_append] at hv
    rcases hv with hnew | hold
    · exfalso
      rw [List.mem_flatMap] at hnew
      obtain ⟨ty, hty, hvty⟩ := hnew
      rw [HMap.union_empty] at hty
      rw [(h_map ty hty).1] at hvty
      exact absurd hvty (by simp)
    · have hold_ktv : v ∈ TContext.knownTypeVars Env.context := by
        simpa only [TContext.knownTypeVars] using hold
      exact h_env.ctxFreshForGen v hold_ktv n hn
  · intro y ty hy
    rcases hfind y ty hy with hnew | hold
    · rw [(h_map ty hnew).2]; exact List.nodup_nil
    · exact h_env.boundVarsNodup y ty hold
  · intro y ty hy v hv n hn
    rw [hgen] at hn
    rcases hfind y ty hy with hnew | hold
    · rw [(h_map ty hnew).2] at hv; exact absurd hv (by simp)
    · exact h_env.boundVarsFresh y ty hold v hv n hn

/-- Registering a type alias preserves `TEnvWF`. -/
theorem addTypeAlias_preserves_TEnvWF {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (alias : TypeAlias) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (hwf : LExpr.TEnvWF (T := T) Env)
    (h : TEnv.addTypeAlias alias C Env = .ok Env') :
    LExpr.TEnvWF (T := T) Env' := by
  obtain ⟨hnodup, hclosed, hused, -, -, storedTy, EnvR, hresolve, haliases, htypes, -⟩ :=
    addTypeAlias_decompose alias C Env Env' h
  have hEnvR : EnvR = Env :=
    LMonoTy.resolveAliases_env_eq alias.type Env storedTy EnvR hresolve
  subst EnvR
  have hequiv : AliasEquiv Env.context.aliases alias.type storedTy :=
    LExpr.resolveAliases_aliasEquiv (T := T) (Γ := Env.context) alias.type Env storedTy Env
      hresolve rfl
  have hfvs := AliasEquiv.freeVars_iff hwf.aliasesWF hequiv
  have hstate := TEnv.addTypeAlias_stateSubstInfo alias C Env Env' h
  have hgen := TEnv.addTypeAlias_genState alias C Env Env' h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [haliases] at ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact { fvs_eq := fun tv => (hfvs tv).symm.trans ⟨hclosed tv, hused tv⟩
              typeArgs_nodup := hnodup }
    · exact hwf.aliasesWF a ha
  · simpa only [hstate, hgen] using hwf.substFreshForGen
  · intro v hv n hn
    have hv_old : v ∈ TContext.knownTypeVars Env.context := by
      simpa only [TContext.knownTypeVars, htypes] using hv
    have hn_old : n ≥ Env.genEnv.genState.tyGen := by simpa only [hgen] using hn
    exact hwf.ctxFreshForGen v hv_old n hn_old
  · intro y ty hy
    have hy_old : Env.context.types.find? y = some ty := by
      simpa only [htypes] using hy
    exact hwf.boundVarsNodup y ty hy_old
  · intro y ty hy v hv n hn
    have hy_old : Env.context.types.find? y = some ty := by
      simpa only [htypes] using hy
    have hn_old : n ≥ Env.genEnv.genState.tyGen := by simpa only [hgen] using hn
    exact hwf.boundVarsFresh y ty hy_old v hv n hn_old

mutual
/-- A registered instance resolves to itself when no alias name is registered. -/
theorem SourceTyResolves.self_of_knownInstance {aliases : List TypeAlias} {ks : KnownTypes}
    (hfresh : ∀ al ∈ aliases, KnownTypes.containsName ks al.name = false)
    (mty : LMonoTy) (hkn : LMonoTy.knownInstance mty ks = true) :
    SourceTyResolves aliases mty mty := by
  match mty with
  | .ftvar _ => exact SourceTyResolves.ftvar
  | .bitvec _ => exact SourceTyResolves.bitvec
  | .tcons name args =>
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at hkn
    refine SourceTyResolves.tcons (SourceTysResolve.self_of_knownInstances hfresh args hkn.2) ?_
    refine List.find?_eq_none.mpr ?_
    intro al hal
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro hnm
    have hcn : KnownTypes.containsName ks name = true :=
      containsName_of_contains ks { name := name, metadata := args.length } hkn.1
    have hno : KnownTypes.containsName ks al.name = false := hfresh al hal
    rw [hnm, hcn] at hno
    exact absurd hno (by simp)
termination_by sizeOf mty

/-- Registered instances resolve to themselves when no alias name is registered. -/
private theorem SourceTysResolve.self_of_knownInstances {aliases : List TypeAlias} {ks : KnownTypes}
    (hfresh : ∀ al ∈ aliases, KnownTypes.containsName ks al.name = false)
    (mtys : LMonoTys) (hkn : LMonoTys.knownInstances mtys ks = true) :
    SourceTysResolve aliases mtys mtys := by
  match mtys with
  | [] => exact SourceTysResolve.nil
  | m :: rest =>
    simp only [LMonoTys.knownInstances] at hkn
    elim_err hkn with hm
    exact SourceTysResolve.cons (SourceTyResolves.self_of_knownInstance hfresh m hm)
      (SourceTysResolve.self_of_knownInstances hfresh rest hkn)
termination_by sizeOf mtys
end

/-- A registered instance is a valid source type resolving to itself under the unrestricted
    policy when no alias name is registered. -/
theorem SourceTyWF.self_of_knownInstance {T : LExprParams} {C : LContext T}
    {aliases : List TypeAlias}
    (hfresh : ∀ al ∈ aliases, KnownTypes.containsName C.knownTypes al.name = false)
    {mty : LMonoTy} (hkn : LMonoTy.knownInstance mty C.knownTypes = true) :
    SourceTyWF C TyVarAdmissibility.all aliases mty mty :=
  ⟨SourceTyResolves.self_of_knownInstance hfresh mty hkn, ResolvedTyWF.of_knownInstance hkn⟩

/-- After a substitution, a source type whose resolution keeps its free variables stays valid under
    the unrestricted policy when the substituted resolution is a registered instance. -/
theorem SourceTyWF.subst_of_knownInstance {T : LExprParams} {C : LContext T}
    {aliases : List TypeAlias} (hwf : ∀ a ∈ aliases, TypeAlias.WF a)
    (hfresh : ∀ al ∈ aliases, KnownTypes.containsName C.knownTypes al.name = false)
    (S : Subst) {t r : LMonoTy} (hres : SourceTyResolves aliases t r)
    (hfv : ∀ v ∈ LMonoTy.freeVars t, v ∈ LMonoTy.freeVars r)
    (hkn : LMonoTy.knownInstance (LMonoTy.subst S r) C.knownTypes = true) :
    SourceTyWF C TyVarAdmissibility.all aliases (LMonoTy.subst S t) (LMonoTy.subst S r) := by
  have hS : ∀ v ∈ LMonoTy.freeVars t,
      SourceTyResolves aliases (LMonoTy.subst S (.ftvar v)) (LMonoTy.subst S (.ftvar v)) :=
    fun v hv => SourceTyResolves.self_of_knownInstance hfresh _
      (knownInstance_subst_ftvar_of_mem C.knownTypes S r hkn v (hfv v hv))
  exact ⟨SourceTyResolves.subst (fun al hal => (hwf al hal).fvs_closed) S hres hS,
    ResolvedTyWF.of_knownInstance hkn⟩

/-- A source type stays valid under the unrestricted variable policy after a substitution whose
    resolved result is a registered instance. -/
theorem SourceTyWF.subst_of_resolves_knownInstance {T : LExprParams} {C : LContext T}
    {aliases : List TypeAlias} (hwf : ∀ a ∈ aliases, TypeAlias.WF a)
    (hfresh : ∀ al ∈ aliases, KnownTypes.containsName C.knownTypes al.name = false)
    (S : Subst) {t r : LMonoTy} (hres : SourceTyResolves aliases t r)
    (hkn : LMonoTy.knownInstance (LMonoTy.subst S r) C.knownTypes = true) :
    ∃ r', SourceTyWF C TyVarAdmissibility.all aliases (LMonoTy.subst S t) r' := by
  let g : TyIdentifier → LMonoTy := fun v =>
    if v ∈ LMonoTy.freeVars r then LMonoTy.subst S (.ftvar v)
    else Classical.choose (SourceTyResolves.exists aliases (LMonoTy.subst S (.ftvar v)))
  let τ : Subst := [LExpr.buildSubstFromFunction (LMonoTy.freeVars t ++ LMonoTy.freeVars r) g]
  have hτ : ∀ v, v ∈ LMonoTy.freeVars t ++ LMonoTy.freeVars r →
      LMonoTy.subst τ (.ftvar v) = g v := by
    intro v hv
    apply LMonoTy.subst_ftvar_of_some
    rw [Strata.Util.HMaps.find?_single_scope]
    exact LExpr.find?_buildSubstFromFunction _ _ v hv
  have hS : ∀ v ∈ LMonoTy.freeVars t,
      SourceTyResolves aliases (LMonoTy.subst S (.ftvar v)) (LMonoTy.subst τ (.ftvar v)) := by
    intro v hv
    rw [hτ v (List.mem_append_left _ hv)]
    by_cases hvr : v ∈ LMonoTy.freeVars r
    · simp only [g, hvr, ite_true]
      exact SourceTyResolves.self_of_knownInstance hfresh _
        (knownInstance_subst_ftvar_of_mem C.knownTypes S r hkn v hvr)
    · simp only [g, hvr, ite_false]
      exact Classical.choose_spec (SourceTyResolves.exists aliases (LMonoTy.subst S (.ftvar v)))
  have hres' := SourceTyResolves.subst₂ (fun al hal => (hwf al hal).fvs_closed) S τ hres hS
  have hτr : LMonoTy.subst τ r = LMonoTy.subst S r := by
    apply agree_on_freeVars_implies_subst_eq
    intro v hv
    rw [hτ v (List.mem_append_right _ hv)]
    simp only [g, hv, ite_true]
  rw [hτr] at hres'
  exact ⟨_, hres', ResolvedTyWF.of_knownInstance hkn⟩

/-! ### The resolver keeps its substitution's range registered -/

namespace LExpr

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]

omit [ToString T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- `inferConst` reports a registered type when literal types are registered. -/
private theorem inferConst_knownInstance
    (C : LContext T) (Env : TEnv T.IDMeta) (c : LConst) (ty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferConst C Env c = .ok (ty, Env'))
    (hlit : LiteralTysKnown C) :
    LMonoTy.knownInstance ty C.knownTypes = true ∧ Env' = Env := by
  simp only [inferConst] at h
  elim_err h with hname
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hname
  obtain ⟨⟨hknown, -⟩, hp | hk⟩ := hname
  · exact ⟨h1 ▸ hlit c hp hknown, h2.symm⟩
  · exact ⟨h1 ▸ hk, h2.symm⟩

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- Unifying an instantiated annotation with a registered type keeps the range registered. -/
private theorem instantiateAnnot_unify_RangeKnown
    (C : LContext T) (Env1 Env2 : TEnv T.IDMeta) (ann ann' ty : LMonoTy) (cs : Constraints)
    (S : SubstInfo)
    (h_inst : LMonoTy.instantiateWithCheck ann C Env1 = .ok (ann', Env2))
    (h_unify : (Constraints.unify cs Env2.stateSubstInfo).mapError format = .ok S)
    (hcs : cs = [(ann', ty)] ∨ cs = [(ty, ann')])
    (h_ty : LMonoTy.knownInstance ty C.knownTypes = true)
    (hS : Subst.RangeKnown Env1.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown (TEnv.updateSubst Env2 S).stateSubstInfo.subst C.knownTypes := by
  have h_ann : LMonoTy.knownInstance ann' C.knownTypes = true :=
    LMonoTy_instantiateWithCheck_knownInstance ann C Env1 ann' Env2 h_inst
  have h_S2 : Subst.RangeKnown Env2.stateSubstInfo.subst C.knownTypes := by
    rw [(LMonoTy_instantiateWithCheck_subst_knownInstance ann C Env1 ann' Env2 h_inst).1]
    exact hS
  simp only [TEnv.updateSubst]
  refine Constraints.unify_RangeKnown C.knownTypes cs Env2.stateSubstInfo S
    (unify_of_mapError h_unify) h_S2 ?_
  intro p hp
  rcases hcs with rfl | rfl
  · rw [List.mem_singleton] at hp
    subst hp
    exact ⟨h_ann, h_ty⟩
  · rw [List.mem_singleton] at hp
    subst hp
    exact ⟨h_ty, h_ann⟩

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- `inferFVar` reports a registered type and keeps the range registered. -/
private theorem inferFVar_RangeKnown
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty, Env'))
    (hS : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes ∧
    LMonoTy.knownInstance ty C.knownTypes = true := by
  obtain ⟨tyScheme, Env1, -, h_inst, h_rest⟩ := inferFVar_ok_inv C Env x fty ty Env' h
  obtain ⟨h_subst, h_ty⟩ :=
    LTy_instantiateWithCheck_subst_knownInstance tyScheme C Env ty Env1 h_inst
  have h_S1 : Subst.RangeKnown Env1.stateSubstInfo.subst C.knownTypes := by
    rw [h_subst]; exact hS
  rcases h_rest with rfl | ⟨ann, ann', Env2, S, h_inst2, h_mapError, rfl⟩
  · exact ⟨h_S1, h_ty⟩
  · exact ⟨instantiateAnnot_unify_RangeKnown C Env1 Env2 ann ann' ty _ S h_inst2
      h_mapError (.inl rfl) h_ty h_S1, h_ty⟩

end LExpr

/-! ### Type variables a substitution and a scope avoid -/

section AnnotsAvoid

variable {T : LExprParams} {ps : List TyIdentifier}

/-- A free-variable occurrence's annotation avoids `ps` when the occurrence does. -/
theorem LExpr.AnnotsAvoid.of_fvar {m : T.Metadata} {x : T.Identifier} {ty : Option LMonoTy}
    (h : LExpr.AnnotsAvoid (.fvar m x ty) ps) :
    ∀ a ∈ ty.toList, ∀ v ∈ LMonoTy.freeVars a, v ∉ ps := by
  intro a ha
  refine h a ?_
  simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, List.append_nil]
  exact ha

/-- An expression whose annotations are those of `a` followed by those of `b` avoids `ps` iff
    both `a` and `b` do. -/
private theorem LExpr.AnnotsAvoid.append_iff {e a b : LExpr T.mono}
    (hfv : LExpr.fvarAnnotations e = LExpr.fvarAnnotations a ++ LExpr.fvarAnnotations b)
    (hbd : LExpr.binderAnnotations e = LExpr.binderAnnotations a ++ LExpr.binderAnnotations b) :
    LExpr.AnnotsAvoid e ps ↔ LExpr.AnnotsAvoid a ps ∧ LExpr.AnnotsAvoid b ps := by
  simp only [LExpr.AnnotsAvoid, hfv, hbd, List.mem_append]
  constructor
  · intro h
    exact ⟨fun t ht => ht.elim (fun ht => h t (Or.inl (Or.inl ht)))
        (fun ht => h t (Or.inr (Or.inl ht))),
      fun t ht => ht.elim (fun ht => h t (Or.inl (Or.inr ht)))
        (fun ht => h t (Or.inr (Or.inr ht)))⟩
  · intro ⟨ha, hb⟩ t ht
    rcases ht with (ht | ht) | (ht | ht)
    · exact ha t (Or.inl ht)
    · exact hb t (Or.inl ht)
    · exact ha t (Or.inr ht)
    · exact hb t (Or.inr ht)

/-- Both sides of an application avoid `ps` when it does. -/
theorem LExpr.AnnotsAvoid.of_app {m : T.Metadata} {a b : LExpr T.mono}
    (h : LExpr.AnnotsAvoid (.app m a b) ps) : LExpr.AnnotsAvoid a ps ∧ LExpr.AnnotsAvoid b ps :=
  (LExpr.AnnotsAvoid.append_iff rfl rfl).mp h

/-- Both sides of an equation avoid `ps` when it does. -/
theorem LExpr.AnnotsAvoid.of_eq {m : T.Metadata} {a b : LExpr T.mono}
    (h : LExpr.AnnotsAvoid (.eq m a b) ps) : LExpr.AnnotsAvoid a ps ∧ LExpr.AnnotsAvoid b ps :=
  (LExpr.AnnotsAvoid.append_iff rfl rfl).mp h

/-- The parts of a conditional avoid `ps` when it does. -/
theorem LExpr.AnnotsAvoid.of_ite {m : T.Metadata} {c a b : LExpr T.mono}
    (h : LExpr.AnnotsAvoid (.ite m c a b) ps) :
    LExpr.AnnotsAvoid c ps ∧ LExpr.AnnotsAvoid a ps ∧ LExpr.AnnotsAvoid b ps := by
  simp only [LExpr.AnnotsAvoid, LExpr.fvarAnnotations, LExpr.binderAnnotations,
    List.mem_append] at h ⊢
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rcases ht with ht | ht
    · exact h t (Or.inl (Or.inl (Or.inl ht)))
    · exact h t (Or.inr (Or.inl (Or.inl ht)))
  · rcases ht with ht | ht
    · exact h t (Or.inl (Or.inl (Or.inr ht)))
    · exact h t (Or.inr (Or.inl (Or.inr ht)))
  · rcases ht with ht | ht
    · exact h t (Or.inl (Or.inr ht))
    · exact h t (Or.inr (Or.inr ht))

/-- The binder annotation and body of an abstraction avoid `ps` when it does. -/
theorem LExpr.AnnotsAvoid.of_abs {m : T.Metadata} {name : String} {ty : Option LMonoTy}
    {b : LExpr T.mono} (h : LExpr.AnnotsAvoid (.abs m name ty b) ps) :
    (∀ a ∈ ty.toList, ∀ v ∈ LMonoTy.freeVars a, v ∉ ps) ∧ LExpr.AnnotsAvoid b ps := by
  simp only [LExpr.AnnotsAvoid, LExpr.fvarAnnotations, LExpr.binderAnnotations,
    List.mem_append] at h ⊢
  exact ⟨fun a ha => h a (Or.inr (Or.inl ha)),
    fun t ht => ht.elim (fun ht => h t (Or.inl ht)) (fun ht => h t (Or.inr (Or.inr ht)))⟩

/-- The binder annotation, triggers and body of a quantifier avoid `ps` when it does. -/
theorem LExpr.AnnotsAvoid.of_quant {m : T.Metadata} {k : QuantifierKind} {name : String}
    {ty : Option LMonoTy} {tr b : LExpr T.mono}
    (h : LExpr.AnnotsAvoid (.quant m k name ty tr b) ps) :
    (∀ a ∈ ty.toList, ∀ v ∈ LMonoTy.freeVars a, v ∉ ps) ∧ LExpr.AnnotsAvoid tr ps ∧
      LExpr.AnnotsAvoid b ps := by
  simp only [LExpr.AnnotsAvoid, LExpr.fvarAnnotations, LExpr.binderAnnotations,
    List.mem_append] at h ⊢
  refine ⟨fun a ha => h a (Or.inr (Or.inl (Or.inl ha))), fun t ht => ?_, fun t ht => ?_⟩
  · rcases ht with ht | ht
    · exact h t (Or.inl (Or.inl ht))
    · exact h t (Or.inr (Or.inl (Or.inr ht)))
  · rcases ht with ht | ht
    · exact h t (Or.inl (Or.inr ht))
    · exact h t (Or.inr (Or.inr ht))

end AnnotsAvoid

/-- A context equivalent to one avoiding `ps` avoids `ps`. -/
theorem TContext.VarsAvoid.of_equiv {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ Γ' : TContext T.IDMeta} {ps : List TyIdentifier} (h : Γ'.Equiv Γ)
    (hΓ : TContext.VarsAvoid Γ ps) : TContext.VarsAvoid Γ' ps :=
  fun v hv => hΓ v ((h.mem_knownTypeVars v).mp hv)

/-- A substitution avoiding `ps` keeps a type's free variables avoiding `ps`. -/
theorem LMonoTy.subst_varsAvoid {ps : List TyIdentifier} {S : Subst} {t : LMonoTy}
    (hS : Subst.VarsAvoid S ps) (ht : ∀ v ∈ LMonoTy.freeVars t, v ∉ ps) :
    ∀ v ∈ LMonoTy.freeVars (LMonoTy.subst S t), v ∉ ps := by
  intro v hv
  rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S t hv) with hv | hv
  · exact ht v hv
  · exact hS v (Or.inr hv)

/-- A constraint list's free variables avoid `ps` when every side does. -/
theorem Constraints.freeVars_varsAvoid {ps : List TyIdentifier} :
    ∀ {cs : Constraints}, (∀ c ∈ cs, (∀ v ∈ LMonoTy.freeVars c.1, v ∉ ps) ∧
      ∀ v ∈ LMonoTy.freeVars c.2, v ∉ ps) →
    ∀ v ∈ Constraints.freeVars cs, v ∉ ps
  | [], _, v, hv => by simp only [Constraints.freeVars, List.not_mem_nil] at hv
  | c :: cs, h, v, hv => by
    simp only [Constraints.freeVars, Constraint.freeVars, List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · exact (h c List.mem_cons_self).1 v hv
    · exact (h c List.mem_cons_self).2 v hv
    · exact Constraints.freeVars_varsAvoid (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) v hv

/-- Unification keeps a substitution avoiding `ps` when every constraint side avoids it. -/
theorem Constraints.unify_varsAvoid {ps : List TyIdentifier} {cs : Constraints}
    {S S' : SubstInfo} (h : Constraints.unify cs S = .ok S') (hS : Subst.VarsAvoid S.subst ps)
    (hcs : ∀ v ∈ Constraints.freeVars cs, v ∉ ps) : Subst.VarsAvoid S'.subst ps := by
  intro v hv
  rcases LExpr.Constraints.unify_vars_mem h v hv with hvc | hvS
  · exact hcs v hvc
  · exact hS v hvS

/-! ### Substitutions whose older scopes bind nothing -/

/-- A substitution with no keys has no values. -/
theorem SubstClear.values_eq_nil {S : Subst} (h : SubstClear S) : HMaps.values S = [] := by
  induction S with
  | nil => rfl
  | cons m rest ih =>
    simp only [SubstClear, HMaps.keys, List.append_eq_nil_iff] at h
    have hmv : m.values = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr fun v hv => ?_
      obtain ⟨k, hk⟩ := (HMap.mem_values_iff_find? m v).mp hv
      have hmem := HMap.find?_mem_keys m hk
      rw [h.1] at hmem
      exact absurd hmem List.not_mem_nil
    simp only [HMaps.values, hmv, ih h.2, List.nil_append]

/-- A substitution that binds nothing avoids every list of names. -/
theorem SubstClear.varsAvoid {S : Subst} (h : SubstClear S) (ps : List TyIdentifier) :
    Subst.VarsAvoid S ps := by
  intro v hv
  rcases hv with hv | hv
  · rw [h] at hv
    exact absurd hv List.not_mem_nil
  · simp only [Subst.freeVars, h.values_eq_nil, List.flatMap_nil, List.not_mem_nil] at hv

/-- The empty list of scopes binds nothing. -/
theorem SubstClear.nil : SubstClear ([] : Subst) :=
  (rfl : HMaps.keys ([] : Subst) = [])

/-- Pushing an empty scope onto a substitution binding nothing keeps it binding nothing. -/
theorem SubstClear.push_empty {S : Subst} (h : SubstClear S) :
    SubstClear (HMaps.push S (HMap.empty : SubstOne)) := by
  simp only [SubstClear, HMaps.push, HMaps.keys, HMap.keys_empty, List.nil_append]
  exact h

/-- Pushing any scope onto a substitution that binds nothing leaves older scopes binding nothing. -/
theorem TailClear.push {S : Subst} (h : SubstClear S) (m : SubstOne) :
    TailClear (HMaps.push S m) := h

/-- Applying a one-scope substitution to all bound types keeps older scopes binding nothing. -/
private theorem TailClear.apply {S : Subst} (h : TailClear S) (m : SubstOne) :
    TailClear (Subst.apply m S) := by
  have hpop : HMaps.pop (Subst.apply m S) = HMaps.mapValues (LMonoTy.subst [m]) (HMaps.pop S) := by
    cases S <;> rfl
  unfold TailClear
  rw [hpop]
  refine List.eq_nil_iff_forall_not_mem.mpr fun k hk => ?_
  rw [HMaps.mem_keys_mapValues_iff] at hk
  rw [h] at hk
  exact absurd hk List.not_mem_nil

/-- Inserting a binding keeps the scopes below the newest one binding nothing. -/
private theorem TailClear.insert {S : Subst} (h : TailClear S) (x : TyIdentifier) (ty : LMonoTy) :
    TailClear (HMaps.insert S x ty) := by
  unfold HMaps.insert
  split
  · exact h
  · rename_i sty hfind
    cases S with
    | nil => simp only [HMaps.find?, reduceCtorEq] at hfind
    | cons m rest =>
      simp only [HMaps.update]
      split
      · rename_i hm
        simp only [HMaps.find?, hm] at hfind
        have hmem := HMaps.find?_mem_keys rest hfind
        have hrest : HMaps.keys rest = [] := h
        rw [hrest] at hmem
        exact absurd hmem List.not_mem_nil
      · exact h

/-- Removing a key keeps the scopes below the newest one binding nothing. -/
private theorem TailClear.remove {S : Subst} (h : TailClear S) (x : TyIdentifier) :
    TailClear (HMaps.remove S x) := by
  have hpop : HMaps.pop (HMaps.remove S x) = HMaps.remove (HMaps.pop S) x := by
    cases S <;> rfl
  unfold TailClear
  rw [hpop]
  refine List.eq_nil_iff_forall_not_mem.mpr fun k hk => ?_
  have hk' := HMaps.keys_remove_subset _ x k hk
  rw [h] at hk'
  exact absurd hk' List.not_mem_nil

/-- Unification keeps the substitution's scopes below the newest one binding nothing. -/
theorem Constraints.unify_tailClear {cs : Constraints} {S S' : SubstInfo}
    (h : Constraints.unify cs S = .ok S') (hS : TailClear S.subst) : TailClear S'.subst := by
  have hboth := Constraint.unify_preserves TailClear (fun _ => True) SubstClear.nil
    (fun _ _ _ hS _ => (hS.apply _).insert _ _)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
  simp only [Constraints.unify, bind, Except.bind] at h
  elim_err h with relS h_core
  simp only [Except.ok.injEq] at h
  subst h
  exact hboth.2 cs S relS h_core hS (fun _ _ => trivial)

/-! ### Avoiding type variables through checking steps -/

/-- Dropping a binding keeps a substitution avoiding `ps`. -/
private theorem Subst.VarsAvoid.remove {ps : List TyIdentifier} {S : Subst}
    (hS : Subst.VarsAvoid S ps)
    (k : TyIdentifier) : Subst.VarsAvoid (HMaps.remove S k) ps := by
  intro v hv
  refine hS v ?_
  rcases hv with hv | hv
  · exact Or.inl (HMaps.keys_remove_subset S k v hv)
  · simp only [Subst.freeVars, List.mem_flatMap] at hv ⊢
    obtain ⟨t, ht, hvt⟩ := hv
    exact Or.inr ⟨t, HMaps.values_remove_subset S k t ht, hvt⟩

/-- Dropping several bindings keeps a substitution avoiding `ps`. -/
private theorem Subst.VarsAvoid.removeKeys {ps : List TyIdentifier} {S : Subst}
    (hS : Subst.VarsAvoid S ps) (R : List TyIdentifier) :
    Subst.VarsAvoid (Subst.removeKeys S R) ps := by
  intro v hv
  refine hS v ?_
  rcases hv with hv | hv
  · exact Or.inl (Subst.keys_removeKeys_subset S R v hv).1
  · simp only [Subst.freeVars, List.mem_flatMap] at hv ⊢
    obtain ⟨t, ht, hvt⟩ := hv
    exact Or.inr ⟨t, Subst.values_removeKeys_subset S R t ht, hvt⟩

/-- `renameAfter S ρ` avoids `ps` when `S` does and `ρ` touches no name in `ps`. -/
private theorem Subst.VarsAvoid.renameAfter {ps : List TyIdentifier} {S ρ : Subst}
    (hS : Subst.VarsAvoid S ps) (hρ : Subst.VarsAvoid ρ ps) :
    Subst.VarsAvoid (Subst.renameAfter S ρ) ps := by
  intro v hv
  rw [Subst.renameAfter] at hv
  rcases hv with hv | hv
  · rw [HMaps.keys_append, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hS v (Or.inl ((HMaps.mem_keys_mapValues_iff _ S v).mp hv))
    · exact hρ v (Or.inl hv)
  · simp only [Subst.freeVars, HMaps.values_append, List.flatMap_append, List.mem_append,
      List.mem_flatMap] at hv
    rcases hv with ⟨t, ht, hvt⟩ | ⟨t, ht, hvt⟩
    · obtain ⟨u, hu, rfl⟩ := (HMaps.mem_values_mapValues _ S t).mp ht
      refine LMonoTy.subst_varsAvoid hρ (fun w hw => hS w (Or.inr ?_)) v hvt
      simp only [Subst.freeVars, List.mem_flatMap]
      exact ⟨u, hu, hw⟩
    · have hvρ : v ∈ Subst.freeVars ρ := by
        simp only [Subst.freeVars, List.mem_flatMap]
        exact ⟨t, ht, hvt⟩
      exact hρ v (Or.inr hvρ)

/-- `Subst.ofRenaming ρ` avoids `ps` when no name in `ρ` is in `ps`. -/
private theorem Subst.ofRenaming_varsAvoid {ps : List TyIdentifier}
    (ρ : List (TyIdentifier × TyIdentifier))
    (h : ∀ p ∈ ρ, p.1 ∉ ps ∧ p.2 ∉ ps) : Subst.VarsAvoid (Subst.ofRenaming ρ) ps := by
  intro v hv
  rcases hv with hv | hv
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (Subst.mem_keys_ofRenaming hv)
    exact (h p hp).1
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (Subst.mem_freeVars_ofRenaming hv)
    exact (h p hp).2

/-- The ambient substitution avoids `ps` when `S` does and no generated variable is in `ps`. -/
theorem ambientSubst_varsAvoid {ps : List TyIdentifier} (gen : TyIdentifier → Bool) (S : Subst)
    (hgen : ∀ g, gen g = true → g ∉ ps) (hS : Subst.VarsAvoid S ps) :
    Subst.VarsAvoid (ambientSubst gen S) ps := by
  unfold ambientSubst
  split
  · exact hS
  · refine (hS.renameAfter (Subst.ofRenaming_varsAvoid _ ?_)).removeKeys _
    intro p hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
    exact ⟨hgen g (ambientTargets_generated hg),
      hS _ (Or.inl (mem_ambientKeys (ambientRep_spec hg).1).1)⟩

section VarsAvoidEnv

variable {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta] {ps : List TyIdentifier}

/-- Adding schemes avoiding `ps` to the newest scope keeps a context avoiding `ps`. -/
private theorem TContext.VarsAvoid.addInNewest {Γ : TContext T.IDMeta}
    (hΓ : TContext.VarsAvoid Γ ps)
    (m : HMap T.Identifier LTy) (hm : ∀ ty ∈ m.values, ∀ v ∈ LTy.freeVars ty, v ∉ ps) :
    TContext.VarsAvoid { Γ with types := Γ.types.addInNewest m } ps := by
  intro v hv
  simp only [TContext.knownTypeVars, List.mem_flatMap] at hv
  obtain ⟨w, hw, hvw⟩ := hv
  have hold : w ∈ Γ.types.values → v ∉ ps := by
    intro hw'
    refine hΓ v ?_
    simp only [TContext.knownTypeVars, List.mem_flatMap]
    exact ⟨w, hw', hvw⟩
  generalize Γ.types = ts at hw hold
  cases ts with
  | nil =>
    simp only [HMaps.addInNewest, HMaps.values, List.append_nil] at hw
    exact hm w hw v hvw
  | cons scope rest =>
    rw [HMaps.addInNewest_cons] at hw
    simp only [HMaps.values, List.mem_append] at hw hold
    rcases hw with hw | hw
    · rw [HMap.mem_values_iff_find?] at hw
      obtain ⟨k, hk⟩ := hw
      rw [HMap.find?_union] at hk
      cases hs : scope.find? k with
      | some u =>
        rw [hs] at hk
        simp only [Option.some_or, Option.some.injEq] at hk
        subst hk
        exact hold (Or.inl (HMap.find?_mem_values scope hs))
      | none =>
        rw [hs] at hk
        simp only [Option.none_or] at hk
        exact hm w (HMap.find?_mem_values _ hk) v hvw
    · exact hold (Or.inr hw)

/-- Adding schemes avoiding `ps` to the newest scope keeps an environment avoiding `ps`. -/
theorem TEnv.VarsAvoid.addInNewestContext {Env : TEnv T.IDMeta} (hE : TEnv.VarsAvoid Env ps)
    (m : HMap T.Identifier LTy) (hm : ∀ ty ∈ m.values, ∀ v ∈ LTy.freeVars ty, v ∉ ps) :
    TEnv.VarsAvoid (Env.addInNewestContext m) ps :=
  ⟨hE.1, hE.2.addInNewest m hm⟩

/-- Opening a variable scope keeps an environment avoiding `ps`. -/
theorem TEnv.VarsAvoid.pushEmptyContext {Env : TEnv T.IDMeta} (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Env.pushEmptyContext ps := by
  refine ⟨by rw [TEnv.pushEmptyContext_stateSubstInfo]; exact hE.1, ?_⟩
  intro v hv
  refine hE.2 v ?_
  simpa [TContext.knownTypeVars, TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context,
    HMaps.push, HMaps.values, HMap.values_empty] using hv

/-- Closing the newest variable scope keeps an environment avoiding `ps`. -/
theorem TEnv.VarsAvoid.popContext {Env : TEnv T.IDMeta} (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Env.popContext ps := by
  refine ⟨by rw [TEnv.popContext_stateSubstInfo]; exact hE.1, ?_⟩
  intro v hv
  refine hE.2 v ?_
  simp only [TContext.knownTypeVars, List.mem_flatMap] at hv ⊢
  obtain ⟨w, hw, hvw⟩ := hv
  refine ⟨w, ?_, hvw⟩
  have hpop : ∀ ts : HMaps T.Identifier LTy, w ∈ HMaps.values (HMaps.pop ts) →
      w ∈ HMaps.values ts := by
    intro ts h
    cases ts with
    | nil => simp [HMaps.pop, HMaps.values] at h
    | cons scope rest =>
      simp only [HMaps.pop] at h
      simp only [HMaps.values, List.mem_append]
      exact Or.inr h
  exact hpop _ hw

end VarsAvoidEnv

/-- Every name generated by `genTyVars` has the generator's form. -/
private theorem TGenEnv.genTyVars_genName {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    [ToFormat IDMeta] (n : Nat) (Env : TGenEnv IDMeta) (tvs : List TyIdentifier)
    (Env' : TGenEnv IDMeta) (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    ∀ tv ∈ tvs, ∃ k : Nat, tv = TState.tyPrefix ++ toString k := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp only [TGenEnv.genTyVars, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact fun tv htv => absurd htv List.not_mem_nil
  | succ m ih =>
    simp only [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    elim_err h with v1 h_gen1
    obtain ⟨tv1, Env1⟩ := v1
    elim_err h with v2 h_rest
    obtain ⟨rest, Env2⟩ := v2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro tv htv
    rcases List.mem_cons.mp htv with rfl | htv
    · simp only [TGenEnv.genTyVar] at h_gen1
      elim_err h_gen1
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_gen1
      refine ⟨Env.genState.tyGen, ?_⟩
      rw [← h_gen1.1]
      rfl
    · dsimp only at h_rest
      exact ih Env1 rest Env2 h_rest tv htv

namespace LExpr

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- Instantiating every free variable of a list of types leaves only generated free variables. -/
private theorem LMonoTys.instantiateEnv_freeVars_genName
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (mtys', Env'))
    (h_closed : ∀ tv ∈ LMonoTys.freeVars mtys, tv ∈ ids) :
    ∀ tv ∈ LMonoTys.freeVars mtys', ∃ k : Nat, tv = TState.tyPrefix ++ toString k := by
  intro tv h_tv
  unfold LMonoTys.instantiateEnv at h
  generalize h_inst : LMonoTys.instantiate ids mtys Env.genEnv = result at h
  match result, h_inst with
  | .error _, _ => simp at h
  | .ok (a, gE), h_inst =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [LMonoTys.instantiate, Bind.bind, Except.bind] at h_inst
    elim_err h_inst with v1 h_gen
    obtain ⟨freshtvs, genEnv1⟩ := v1
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
    obtain ⟨h_eq, -⟩ := h_inst
    rw [← h_eq] at h_tv
    have h_len : freshtvs.length = ids.length := TGenEnv.genTyVars_length _ _ _ _ h_gen
    exact TGenEnv.genTyVars_genName _ _ _ _ h_gen tv
      (LMonoTys.freeVars_subst_closed ids freshtvs h_len mtys h_closed tv h_tv)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- Every free variable of a checked annotation instantiation is a generated name. -/
private theorem LMonoTy_instantiateWithCheck_freeVars_genName
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy)
    (Env' : TEnv T.IDMeta) (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v ∈ LMonoTy.freeVars mty, ∃ k : Nat, v = TState.tyPrefix ++ toString k := by
  obtain ⟨mty_ie, Env_ie, Env_ra, h_ie, h_ra⟩ :=
    LMonoTy.instantiateWithCheck_decompose mty_in C Env mty Env' h
  have h_ctx : Env_ie.context = Env.context :=
    LMonoTys.instantiateEnv_context _ _ Env _ Env_ie h_ie
  intro v hv
  have hv_ie := LMonoTy_resolveAliases_freeVars_subset mty_ie Env_ie mty Env_ra h_ra
    (h_ctx ▸ h_aw) v hv
  have h_closed : ∀ tv ∈ LMonoTys.freeVars [mty_in], tv ∈ LMonoTy.freeVars mty_in := by
    intro tv htv
    simpa only [LMonoTys.freeVars, List.append_nil] using htv
  have hv' : v ∈ LMonoTys.freeVars [mty_ie] := by
    simp only [LMonoTys.freeVars, List.append_nil]
    exact hv_ie
  exact LMonoTys.instantiateEnv_freeVars_genName _ _ Env _ Env_ie h_ie h_closed v hv'

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- Every free variable of a checked scheme instantiation is free in the scheme or generated. -/
private theorem LTy_instantiateWithCheck_freeVars
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v ∈ LMonoTy.freeVars mty,
      v ∈ LTy.freeVars ty ∨ ∃ k : Nat, v = TState.tyPrefix ++ toString k := by
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h with v1 h_res
  obtain ⟨mty0, Env1⟩ := v1
  elim_errs h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hmty, -⟩ := h
  subst hmty
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_res
  elim_err h_res with v2 h_inst
  obtain ⟨mtyI, genEnv'⟩ := v2
  have h_ctx : ({ Env with genEnv := genEnv' } : TEnv T.IDMeta).context = Env.context :=
    LTy.instantiate_context ty Env.genEnv mtyI genEnv' h_inst
  intro v hv
  have hvI := LMonoTy_resolveAliases_freeVars_subset mtyI _ mty0 Env1 h_res (h_ctx ▸ h_aw) v hv
  obtain ⟨vars, body⟩ := ty
  cases vars with
  | nil =>
    simp only [LTy.instantiate, Except.ok.injEq, Prod.mk.injEq] at h_inst
    obtain ⟨rfl, -⟩ := h_inst
    left
    simp only [LTy.freeVars, List.removeAll, List.mem_filter, List.elem_nil, Bool.not_false,
      and_true]
    exact hvI
  | cons x xs =>
    simp only [LTy.instantiate, Bind.bind, Except.bind] at h_inst
    elim_err h_inst with v3 h_gen
    obtain ⟨freshtvs, Env2⟩ := v3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
    obtain ⟨rfl, -⟩ := h_inst
    have h_len : freshtvs.length = (x :: xs).length := TGenEnv.genTyVars_length _ _ _ _ h_gen
    rcases LMonoTy.mem_freeVars_subst _ body v hvI with h_sub | ⟨h_body, h_none⟩
    · right
      exact TGenEnv.genTyVars_genName _ _ _ _ h_gen v
        (Subst.freeVars_zip_ftvar (x :: xs) freshtvs h_len h_sub)
    · left
      have h_bound : v ∉ x :: xs := by
        intro h_bound
        have hlen' : (x :: xs).length ≤ (List.map LMonoTy.ftvar freshtvs).length := by
          simp only [List.length_map, h_len, Nat.le_refl]
        have hsome := Subst.find?_ofZip_isSome_of_mem hlen' h_bound
        simp only [Subst.ofZip, h_none, Option.isSome_none, Bool.false_eq_true] at hsome
      simp only [LTy.freeVars, List.removeAll, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.elem_eq_mem, decide_eq_false_iff_not]
      exact ⟨h_body, h_bound⟩

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- A signature instantiation leaves only generated free variables when parameters cover them. -/
theorem LMonoTySignature_instantiate_freeVars_genName
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (tyArgs : List TyIdentifier)
    (sig sig' : @LMonoTySignature T.IDMeta)
    (h : LMonoTySignature.instantiate C Env tyArgs sig = .ok (sig', Env'))
    (h_aw : TContext.AliasesWF Env.context)
    (h_closed : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ tyArgs) :
    ∀ v ∈ LMonoTys.freeVars sig'.values, ∃ k : Nat, v = TState.tyPrefix ++ toString k := by
  obtain ⟨mtysI, EnvI, hinst, hres, -⟩ :=
    LMonoTySignature.instantiate_resolveAliases C Env Env' tyArgs sig sig' h
  have h_ctx : EnvI.context = Env.context :=
    LMonoTys.instantiateEnv_context tyArgs sig.values Env mtysI EnvI hinst
  intro v hv
  exact LMonoTys.instantiateEnv_freeVars_genName tyArgs sig.values Env mtysI EnvI hinst h_closed v
    (LMonoTys_resolveAliases_freeVars_subset mtysI EnvI sig'.values Env' hres (h_ctx ▸ h_aw) v hv)

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- For `ps` without generated names, `instantiateAndSubsts` keeps types and environment avoiding
    `ps`. -/
theorem Identifier.instantiateAndSubsts_varsAvoid {ps : List TyIdentifier}
    (xs : List T.Identifier) (C : LContext T) (Env : TEnv T.IDMeta)
    (mtys : List LMonoTy) (Env' : TEnv T.IDMeta)
    (h : Identifier.instantiateAndSubsts xs C Env = .ok (some (mtys, Env')))
    (h_aw : TContext.AliasesWF Env.context) (hgen : NoGenName ps)
    (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Env' ps ∧ ∀ t ∈ mtys, ∀ v ∈ LMonoTy.freeVars t, v ∉ ps := by
  induction xs generalizing Env mtys with
  | nil =>
    simp only [Identifier.instantiateAndSubsts, pure, Except.pure, Except.ok.injEq,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hE, fun _ ht => absurd ht List.not_mem_nil⟩
  | cons x xrest ih =>
    obtain ⟨xty, EnvA, xtys, hhd, htl, rfl⟩ := Identifier.instantiateAndSubsts_cons_inv h
    obtain ⟨ty, mtyR, hfind, hinst, rfl⟩ := Identifier.instantiateAndSubst_inv x C Env xty EnvA hhd
    have hctxA : EnvA.context = Env.context :=
      LTy_instantiateWithCheck_context' ty C Env mtyR EnvA hinst
    have hSA : EnvA.stateSubstInfo = Env.stateSubstInfo :=
      (LTy_instantiateWithCheck_subst_knownInstance ty C Env mtyR EnvA hinst).1
    have hEA : TEnv.VarsAvoid EnvA ps := ⟨hSA ▸ hE.1, hctxA ▸ hE.2⟩
    obtain ⟨hE', hrest⟩ := ih EnvA xtys htl (hctxA ▸ h_aw) hEA
    refine ⟨hE', ?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · refine LMonoTy.subst_varsAvoid hEA.1 ?_
      intro v hv
      rcases LTy_instantiateWithCheck_freeVars ty C Env mtyR EnvA hinst h_aw v hv with
        hv | ⟨k, rfl⟩
      · exact hE.2 v (TContext.mem_knownTypeVars_of_find hfind hv)
      · exact hgen k
    · exact hrest t ht

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- Every free variable of the binder type `typeBoundVar` assigns is a generated name. -/
private theorem typeBoundVar_xty_genName
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v ∈ LMonoTy.freeVars xty, ∃ k : Nat, v = TState.tyPrefix ++ toString k := by
  intro v hv
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v_gen h_lift; obtain ⟨xv_raw, Env_g⟩ := v_gen
  have h_ctx_g := liftGenEnv_context Env xv_raw Env_g h_lift
  cases bty with
  | some bty_val =>
    simp only at h
    elim_err h
    rename_i bty_mty Env_inst h_ic
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact LMonoTy_instantiateWithCheck_freeVars_genName bty_val C Env_g _ Env_inst h_ic
      (h_ctx_g ▸ h_aw) v hv
  | none =>
    simp only at h
    elim_err h
    rename_i v_tg h_tg; obtain ⟨xtyid, Env_ty⟩ := v_tg
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv
    exact ⟨_, genTyVar_name_eq Env_g _ Env_ty h_tg⟩

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- For `ps` without generated names, `typeBoundVar` keeps the environment and binder type
    avoiding `ps`. -/
private theorem typeBoundVar_varsAvoid {ps : List TyIdentifier}
    (C : LContext T) (Env : TEnv T.IDMeta) (bty : Option LMonoTy)
    (xv : T.Identifier) (xty : LMonoTy) (Env1 : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env1))
    (h_aw : TContext.AliasesWF Env.context) (hgen : NoGenName ps)
    (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Env1 ps ∧ ∀ v ∈ LMonoTy.freeVars xty, v ∉ ps := by
  have hxty : ∀ v ∈ LMonoTy.freeVars xty, v ∉ ps := by
    intro v hv
    obtain ⟨k, rfl⟩ := typeBoundVar_xty_genName C Env bty xv xty Env1 h h_aw v hv
    exact hgen k
  refine ⟨⟨?_, ?_⟩, hxty⟩
  · rw [(typeBoundVar_subst_knownInstance C Env bty xv xty Env1 h).1]
    exact hE.1
  · intro v hv
    simp only [TContext.knownTypeVars, List.mem_flatMap] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    rw [typeBoundVar_types_addInNewest C Env bty xv xty Env1 h] at hw
    rcases HMaps.mem_values_addInNewest_single _ xv _ w hw with hw | rfl
    · refine hE.2 v ?_
      simp only [TContext.knownTypeVars, List.mem_flatMap]
      exact ⟨w, hw, hvw⟩
    · simp only [LTy.freeVars, List.removeAll, List.mem_filter, List.elem_nil, Bool.not_false,
        and_true] at hvw
      exact hxty v hvw

omit [ToString T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- For `ps` without generated names, typing a free variable keeps the substitution and type
    avoiding `ps`. -/
private theorem inferFVar_varsAvoid {ps : List TyIdentifier}
    (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy)
    (ty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty, Env'))
    (h_aw : TContext.AliasesWF Env.context) (hgen : NoGenName ps)
    (hE : TEnv.VarsAvoid Env ps) :
    Subst.VarsAvoid Env'.stateSubstInfo.subst ps ∧ ∀ v ∈ LMonoTy.freeVars ty, v ∉ ps := by
  obtain ⟨tyScheme, Env1, h_find, h_inst, h_rest⟩ := inferFVar_ok_inv C Env x fty ty Env' h
  have h_ty : ∀ v ∈ LMonoTy.freeVars ty, v ∉ ps := by
    intro v hv
    rcases LTy_instantiateWithCheck_freeVars tyScheme C Env ty Env1 h_inst h_aw v hv with
      hv | ⟨k, rfl⟩
    · exact hE.2 v (TContext.mem_knownTypeVars_of_find h_find hv)
    · exact hgen k
  have h_S1 : Subst.VarsAvoid Env1.stateSubstInfo.subst ps := by
    rw [(LTy_instantiateWithCheck_subst_knownInstance tyScheme C Env ty Env1 h_inst).1]
    exact hE.1
  rcases h_rest with rfl | ⟨ann, ann', Env2, S, h_inst2, h_unify, rfl⟩
  · exact ⟨h_S1, h_ty⟩
  · have h_aw1 : TContext.AliasesWF Env1.context :=
      (LTy_instantiateWithCheck_context' tyScheme C Env ty Env1 h_inst) ▸ h_aw
    have h_ann : ∀ v ∈ LMonoTy.freeVars ann', v ∉ ps := by
      intro v hv
      obtain ⟨k, rfl⟩ :=
        LMonoTy_instantiateWithCheck_freeVars_genName ann C Env1 ann' Env2 h_inst2 h_aw1 v hv
      exact hgen k
    have h_S2 : Subst.VarsAvoid Env2.stateSubstInfo.subst ps := by
      rw [(LMonoTy_instantiateWithCheck_subst_knownInstance ann C Env1 ann' Env2 h_inst2).1]
      exact h_S1
    refine ⟨?_, h_ty⟩
    simp only [TEnv.updateSubst]
    refine Constraints.unify_varsAvoid (unify_of_mapError h_unify) h_S2
      (Constraints.freeVars_varsAvoid ?_)
    intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact ⟨h_ann, h_ty⟩

omit [ToString T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] in
/-- Typing a free variable keeps the scopes below the newest one binding nothing. -/
private theorem inferFVar_tailClear (C : LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier)
    (fty : Option LMonoTy) (ty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : inferFVar C Env x fty = .ok (ty, Env'))
    (hS : TailClear Env.stateSubstInfo.subst) : TailClear Env'.stateSubstInfo.subst := by
  obtain ⟨tyScheme, Env1, -, h_inst, h_rest⟩ := inferFVar_ok_inv C Env x fty ty Env' h
  have h_S1 : TailClear Env1.stateSubstInfo.subst := by
    rw [(LTy_instantiateWithCheck_subst_knownInstance tyScheme C Env ty Env1 h_inst).1]
    exact hS
  rcases h_rest with rfl | ⟨ann, ann', Env2, S, h_inst2, h_unify, rfl⟩
  · exact h_S1
  · have h_S2 : TailClear Env2.stateSubstInfo.subst := by
      rw [(LMonoTy_instantiateWithCheck_subst_knownInstance ann C Env1 ann' Env2 h_inst2).1]
      exact h_S1
    exact Constraints.unify_tailClear (unify_of_mapError h_unify) h_S2

end LExpr

/-! ### Scopes that store only monotypes -/

/-- Inserting an unquantified scheme into a monotype-only scope keeps it monotype-only. -/
theorem MonoScope.insert {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    {Γ : TContext IDMeta} (h_mono : MonoScope Γ)
    {z : Identifier IDMeta} {tz : LTy} (h_bv : LTy.boundVars tz = []) :
    MonoScope { Γ with types := Γ.types.insert z tz } := by
  intro z' tz' h_find
  simp only at h_find
  by_cases hz : z' = z
  · subst hz
    rw [HMaps.find?_insert_self] at h_find
    injection h_find with heq
    exact heq ▸ h_bv
  · rw [HMaps.find?_insert_ne _ _ _ _ hz] at h_find
    exact h_mono z' tz' h_find

/-- A lookup in a monotype-only scope finds an unquantified scheme. -/
theorem MonoScope.find?_forAll {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    {Γ : TContext IDMeta} (h_mono : MonoScope Γ) {z : Identifier IDMeta} {tz : LTy}
    (h_find : Γ.types.find? z = some tz) : ∃ mty, tz = .forAll [] mty := by
  cases tz with
  | forAll vars mty =>
    have h_vars : vars = [] := h_mono z _ h_find
    subst h_vars
    exact ⟨mty, rfl⟩

/-- In a monotype-only scope, every substitution key is fresh for the polymorphic entries. -/
theorem polyKeysFresh_of_MonoScope {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (S : Subst) (Γ : TContext T.IDMeta) (h_mono : MonoScope Γ) :
    LExpr.Subst.polyKeysFresh (T := T) S Γ := by
  intro a _ x ty hfind hbv
  exact absurd (h_mono x ty hfind) hbv

/-- In a monotype-only scope, a stored scheme is its opened monotype, quantifying nothing. -/
private theorem forAll_nil_openFull_eq {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    {Γ : TContext IDMeta} (h_mono : MonoScope Γ)
    {z : Identifier IDMeta} {ty_o : LTy} {ty_s : LMonoTy} {tys : LMonoTys}
    (h_find : Γ.types.find? z = some ty_o)
    (h_open : LTy.openFull ty_o tys = ty_s) :
    LTy.forAll [] ty_s = ty_o := by
  have hbv : LTy.boundVars ty_o = [] := h_mono z ty_o h_find
  have h1 : LTy.openFull ty_o tys = LTy.toMonoTypeUnsafe ty_o :=
    openFull_of_boundVars_nil ty_o hbv tys
  rw [← h_open, h1]
  cases ty_o with
  | forAll vs mm =>
    simp only [LTy.boundVars] at hbv
    subst hbv
    rfl

/-- A bare type variable is a compatible annotation for any monotype. -/
theorem annotCompat_ftvar (aliases : List TypeAlias) (v : TyIdentifier) (mty : LMonoTy) :
    LExpr.AnnotCompat aliases (.ftvar v) mty := by
  refine ⟨HMap.single v mty, ?_⟩
  have hsubst : LMonoTy.subst [HMap.single v mty] (LMonoTy.ftvar v) = mty := by
    rw [LMonoTy.subst_unfold]
    simp only [HMaps.find?_single_scope, HMap.find?_single_self]
  rw [hsubst]
  exact AliasEquiv.refl

/-- Every expression is an annotation rewrite of itself. -/
private theorem AnnotRewrite.refl {T : LExprParams} (e : LExpr T.mono) : AnnotRewrite e e := by
  induction e with
  | const m c => exact .const m c
  | op m o ty => exact .op m o ty
  | bvar m i => exact .bvar m i
  | fvar m z a => exact .fvar m z (AnnotStep.keep a)
  | abs m name ty b ih => exact .abs m name rfl ih
  | quant m kd name ty tr b ihtr ihb => exact .quant m kd name rfl ihtr ihb
  | app m f e ihf ihe => exact .app m ihf ihe
  | ite m c t e ihc iht ihe => exact .ite m ihc iht ihe
  | eq m e1 e2 ih1 ih2 => exact .eq m ih1 ih2

/-- Opening annotation-related expressions with one name keeps them related when the injected
    annotations are. -/
private theorem AnnotRel.varOpen {T : LExprParams} {fv bd : Option LMonoTy → Option LMonoTy → Prop}
    {b b' : LExpr T.mono} (h : AnnotRel fv bd b b')
    {x x' : IdentT LMonoTy T.IDMeta} (h_name : x.1 = x'.1) (h_ann : fv x.2 x'.2) :
    ∀ k : Nat, AnnotRel fv bd (LExpr.varOpen k x b) (LExpr.varOpen k x' b') := by
  induction h with
  | const m c => intro k; exact .const m c
  | op m o ty => intro k; exact .op m o ty
  | bvar m i =>
    intro k
    simp only [LExpr.varOpen, LExpr.substK]
    split
    · rw [h_name]
      exact .fvar m x'.1 h_ann
    · exact .bvar m i
  | fvar m z hstep => intro k; exact .fvar m z hstep
  | abs m name hty hb ih => intro k; exact .abs m name hty (ih (k + 1))
  | quant m kd name hty htr hb ihtr ihb =>
    intro k; exact .quant m kd name hty (ihtr (k + 1)) (ihb (k + 1))
  | app m hf he ihf ihe => intro k; exact .app m (ihf k) (ihe k)
  | ite m hc ht he ihc iht ihe => intro k; exact .ite m (ihc k) (iht k) (ihe k)
  | eq m h1 h2 ih1 ih2 => intro k; exact .eq m (ih1 k) (ih2 k)

/-- Over a monotype-only scope, `AnnotRewrite` (dropping a free-variable annotation or making it a
    type variable) preserves typing. -/
private theorem HasType_of_AnnotRewrite {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta} {e : LExpr T.mono} {ty : LTy}
    (h : LExpr.HasType C Γ e ty) :
    MonoScope Γ → ∀ e' : LExpr T.mono, AnnotRewrite e e' → LExpr.HasType C Γ e' ty := by
  induction h with
  | tbool_const Γ' m b hk =>
    intro _ E' hr; cases hr; exact LExpr.HasType.tbool_const Γ' m b hk
  | tint_const Γ' m n hk =>
    intro _ E' hr; cases hr; exact LExpr.HasType.tint_const Γ' m n hk
  | treal_const Γ' m r hk =>
    intro _ E' hr; cases hr; exact LExpr.HasType.treal_const Γ' m r hk
  | tstr_const Γ' m s hk =>
    intro _ E' hr; cases hr; exact LExpr.HasType.tstr_const Γ' m s hk
  | tbitvec_const Γ' m n b hk =>
    intro _ E' hr; cases hr; exact LExpr.HasType.tbitvec_const Γ' m n b hk
  | tmap_const Γ' m k v d es hk hw =>
    intro _ E' hr; cases hr; exact LExpr.HasType.tmap_const Γ' m k v d es hk hw
  | tseq_const Γ' m a es hk hw =>
    intro _ E' hr; cases hr; exact LExpr.HasType.tseq_const Γ' m a es hk hw
  | tvar Γ' m z tz h_find =>
    intro h_mono E' hr
    cases hr with
    | fvar _ _ hstep =>
      cases hstep with
      | keep => exact LExpr.HasType.tvar Γ' m z tz h_find
      | drop => exact LExpr.HasType.tvar Γ' m z tz h_find
      | tyvar v =>
        have hbv : LTy.boundVars tz = [] := h_mono z tz h_find
        have h_open : LTy.openFull tz [] = LTy.toMonoTypeUnsafe tz :=
          openFull_of_boundVars_nil tz hbv _
        have heq : LTy.forAll [] (LTy.toMonoTypeUnsafe tz) = tz :=
          forAll_nil_openFull_eq h_mono h_find h_open
        rw [← heq]
        have hlen : ([] : List LMonoTy).length = tz.boundVars.length := by
          rw [hbv]; rfl
        exact LExpr.HasType.tvar_annotated Γ' m z tz _ [] _ h_find hlen
          h_open (annotCompat_ftvar Γ'.aliases v _)
  | tvar_annotated Γ' m z ty_o ty_s tys ann h_find h_len h_open h_ac =>
    intro h_mono E' hr
    have heq : LTy.forAll [] ty_s = ty_o := forAll_nil_openFull_eq h_mono h_find h_open
    cases hr with
    | fvar _ _ hstep =>
      cases hstep with
      | keep =>
        exact LExpr.HasType.tvar_annotated Γ' m z ty_o ty_s tys ann h_find h_len h_open h_ac
      | drop =>
        rw [heq]
        exact LExpr.HasType.tvar Γ' m z ty_o h_find
      | tyvar v =>
        exact LExpr.HasType.tvar_annotated Γ' m z ty_o ty_s tys _ h_find h_len h_open
          (annotCompat_ftvar Γ'.aliases v ty_s)
  | tabs Γ' m name x x_ty _ e_ty o _ hx he _ ho h_valid ih =>
    intro h_mono E' hr
    cases hr with
    | abs _ _ hty hb =>
      subst hty
      rename_i b'
      obtain ⟨v, hv⟩ := exists_fresh_ftvar x.1 b'
      have h_mono_ins : MonoScope { Γ' with
          types := Γ'.types.insert x.1 x_ty } :=
        h_mono.insert (List.isEmpty_iff.mp hx)
      have h_body' : LExpr.HasType C { Γ' with
            types := Γ'.types.insert x.1 x_ty }
          (LExpr.varOpen 0 ((x.1, some (LMonoTy.ftvar v)) : IdentT LMonoTy T.IDMeta) b')
          e_ty :=
        ih h_mono_ins _ (AnnotRel.varOpen (x := x)
          (x' := (x.1, some (LMonoTy.ftvar v))) hb rfl (AnnotStep.tyvar x.2 v) 0)
      exact LExpr.HasType.tabs Γ' m name (x.1, some (LMonoTy.ftvar v)) x_ty b' e_ty o
        hv hx he h_body' ho h_valid
  | tapp Γ' m _ _ t1 t2 h1 h2 _ _ ih1 ih2 =>
    intro h_mono E' hr
    cases hr with
    | app _ hf he2 =>
      exact LExpr.HasType.tapp Γ' m _ _ t1 t2 h1 h2 (ih1 h_mono _ hf) (ih2 h_mono _ he2)
  | tinst Γ' _ ty0 e_ty a a_ty _ h_open ih =>
    intro h_mono E' hr
    exact LExpr.HasType.tinst Γ' E' ty0 e_ty a a_ty (ih h_mono E' hr) h_open
  | tgen Γ' _ a ty0 _ h_fresh ih =>
    intro h_mono E' hr
    exact LExpr.HasType.tgen Γ' E' a ty0 (ih h_mono E' hr) h_fresh
  | tif Γ' m _ _ _ ty0 _ _ _ ihc ih1 ih2 =>
    intro h_mono E' hr
    cases hr with
    | ite _ hrc hr1 hr2 =>
      exact LExpr.HasType.tif Γ' m _ _ _ ty0 (ihc h_mono _ hrc) (ih1 h_mono _ hr1)
        (ih2 h_mono _ hr2)
  | teq Γ' m _ _ ty0 _ _ ih1 ih2 =>
    intro h_mono E' hr
    cases hr with
    | eq _ hr1 hr2 =>
      exact LExpr.HasType.teq Γ' m _ _ ty0 (ih1 h_mono _ hr1) (ih2 h_mono _ hr2)
  | tquant Γ' m kd name _ tr_ty x x_ty _ o _ hx _ _ ho h_valid ih_body ih_tr =>
    intro h_mono E' hr
    cases hr with
    | quant _ _ _ hty htr hb =>
      subst hty
      rename_i tr' b'
      obtain ⟨v, hv⟩ := exists_fresh_ftvar x.1 b'
      have h_mono_ins : MonoScope { Γ' with
          types := Γ'.types.insert x.1 x_ty } :=
        h_mono.insert (List.isEmpty_iff.mp hx)
      have h_body' : LExpr.HasType C { Γ' with
            types := Γ'.types.insert x.1 x_ty }
          (LExpr.varOpen 0 ((x.1, some (LMonoTy.ftvar v)) : IdentT LMonoTy T.IDMeta) b')
          (.forAll [] LMonoTy.bool) :=
        ih_body h_mono_ins _ (AnnotRel.varOpen (x := x)
          (x' := (x.1, some (LMonoTy.ftvar v))) hb rfl (AnnotStep.tyvar x.2 v) 0)
      have h_tr' : LExpr.HasType C { Γ' with
            types := Γ'.types.insert x.1 x_ty }
          (LExpr.varOpen 0 ((x.1, some (LMonoTy.ftvar v)) : IdentT LMonoTy T.IDMeta) tr')
          tr_ty :=
        ih_tr h_mono_ins _ (AnnotRel.varOpen (x := x)
          (x' := (x.1, some (LMonoTy.ftvar v))) htr rfl (AnnotStep.tyvar x.2 v) 0)
      exact LExpr.HasType.tquant Γ' m kd name tr' tr_ty (x.1, some (LMonoTy.ftvar v)) x_ty b' o
        hv hx h_body' h_tr' ho h_valid
  | top Γ' m f op ty0 h_get h_ty =>
    intro _ E' hr
    cases hr with
    | op => exact LExpr.HasType.top Γ' m f op ty0 h_get h_ty
  | top_annotated Γ' m f op ty_o ty_s tys ann h_get h_ty h_len h_open h_ac =>
    intro _ E' hr
    cases hr with
    | op =>
      exact LExpr.HasType.top_annotated Γ' m f op ty_o ty_s tys ann h_get h_ty h_len h_open h_ac
  | talias Γ' _ mty mty' h_ae _ ih =>
    intro h_mono E' hr
    exact LExpr.HasType.talias Γ' E' mty mty' h_ae (ih h_mono E' hr)

/-! ## Annotations replaced by instances of themselves -/

/-- An annotation is compatible with every type its instance is compatible with. -/
private theorem annotCompat_of_subst {aliases : List TypeAlias} {t ty : LMonoTy} (ρ : SubstOne)
    (h : LExpr.AnnotCompat aliases (LMonoTy.subst [ρ] t) ty) : LExpr.AnnotCompat aliases t ty := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨LExpr.buildSubstFromFunction (LMonoTy.freeVars t)
    (fun v => LMonoTy.subst [σ] (LMonoTy.subst [ρ] (.ftvar v))), ?_⟩
  have hagree : ∀ v ∈ LMonoTy.freeVars t,
      LMonoTy.subst [LExpr.buildSubstFromFunction (LMonoTy.freeVars t)
          (fun v => LMonoTy.subst [σ] (LMonoTy.subst [ρ] (.ftvar v)))] (.ftvar v) =
        LMonoTy.subst [σ] (LMonoTy.subst [ρ] (.ftvar v)) := by
    intro v hv
    apply LMonoTy.subst_ftvar_of_some
    rw [HMaps.find?_single_scope]
    exact LExpr.find?_buildSubstFromFunction _ _ v hv
  rw [← LMonoTy.subst_subst_of_pointwise [ρ] [σ] _ t (fun v hv => (hagree v hv).symm)]
  exact hσ

/-- An absent annotation instantiates only an absent one. -/
private theorem AnnotInstantiates.none_left {a : Option LMonoTy} (h : AnnotInstantiates none a) :
    a = none := by
  rcases h with ⟨-, ha⟩ | ⟨_, _, -, hcontra⟩
  · exact ha
  · cases hcontra

/-- Only an absent annotation instantiates an absent one. -/
private theorem AnnotInstantiates.none_right {a' : Option LMonoTy} (h : AnnotInstantiates a' none) :
    a' = none := by
  rcases h with ⟨ha', -⟩ | ⟨_, _, hcontra, -⟩
  · exact ha'
  · cases hcontra

/-- Every present annotation instantiates a bare type variable. -/
private theorem AnnotInstantiates.ftvar (t : LMonoTy) (v : TyIdentifier) :
    AnnotInstantiates (some t) (some (.ftvar v)) := by
  refine Or.inr ⟨.ftvar v, HMap.single v t, rfl, ?_⟩
  have hsubst : LMonoTy.subst [HMap.single v t] (LMonoTy.ftvar v) = t := by
    rw [LMonoTy.subst_unfold]
    simp only [HMaps.find?_single_scope, HMap.find?_single_self]
  rw [hsubst]

/-- Each free variable of `e` occurs in `e'` with an annotation instantiating its own. -/
private theorem AnnotInstRewrite.mem_freeVars {T : LExprParams} {e' e : LExpr T.mono}
    (h : AnnotInstRewrite e' e) :
    ∀ p ∈ LExpr.freeVars e, ∃ a', AnnotInstantiates a' p.2 ∧ (p.1, a') ∈ LExpr.freeVars e' := by
  induction h with
  | const | op | bvar =>
    intro p hp
    simp only [LExpr.freeVars, List.not_mem_nil] at hp
  | fvar m z hstep =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_singleton] at hp ⊢
    subst hp
    exact ⟨_, hstep, rfl⟩
  | abs m name hty hb ih =>
    intro p hp
    simp only [LExpr.freeVars] at hp ⊢
    exact ih p hp
  | quant m kd name hty htr hb ihtr ihb =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_append] at hp ⊢
    rcases hp with hp | hp
    · obtain ⟨a', ha', hmem⟩ := ihtr p hp
      exact ⟨a', ha', Or.inl hmem⟩
    · obtain ⟨a', ha', hmem⟩ := ihb p hp
      exact ⟨a', ha', Or.inr hmem⟩
  | app m hf he ihf ihe =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_append] at hp ⊢
    rcases hp with hp | hp
    · obtain ⟨a', ha', hmem⟩ := ihf p hp
      exact ⟨a', ha', Or.inl hmem⟩
    · obtain ⟨a', ha', hmem⟩ := ihe p hp
      exact ⟨a', ha', Or.inr hmem⟩
  | ite m hc ht he ihc iht ihe =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_append] at hp ⊢
    rcases hp with (hp | hp) | hp
    · obtain ⟨a', ha', hmem⟩ := ihc p hp
      exact ⟨a', ha', Or.inl (Or.inl hmem)⟩
    · obtain ⟨a', ha', hmem⟩ := iht p hp
      exact ⟨a', ha', Or.inl (Or.inr hmem)⟩
    · obtain ⟨a', ha', hmem⟩ := ihe p hp
      exact ⟨a', ha', Or.inr hmem⟩
  | eq m h1 h2 ih1 ih2 =>
    intro p hp
    simp only [LExpr.freeVars, List.mem_append] at hp ⊢
    rcases hp with hp | hp
    · obtain ⟨a', ha', hmem⟩ := ih1 p hp
      exact ⟨a', ha', Or.inl hmem⟩
    · obtain ⟨a', ha', hmem⟩ := ih2 p hp
      exact ⟨a', ha', Or.inr hmem⟩

/-- If `b'` is `b` with annotations replaced by instances of them, a name fresh for `b'` with
    annotation `a'` is fresh for `b` under some annotation `a` that `a'` instantiates. -/
private theorem AnnotInstRewrite.exists_fresh {T : LExprParams} {b' b : LExpr T.mono}
    (h : AnnotInstRewrite b' b) (x : IdentT LMonoTy T.IDMeta) (hfresh : LExpr.fresh x b') :
    ∃ a, AnnotInstantiates x.2 a ∧ LExpr.fresh ((x.1, a) : IdentT LMonoTy T.IDMeta) b := by
  obtain ⟨y, ann⟩ := x
  cases ann with
  | none =>
    refine ⟨none, Or.inl ⟨rfl, rfl⟩, ?_⟩
    intro hmem
    obtain ⟨a', ha', hmem'⟩ := h.mem_freeVars _ hmem
    have hnone : a' = none := AnnotInstantiates.none_right ha'
    rw [hnone] at hmem'
    exact hfresh hmem'
  | some t =>
    obtain ⟨v, hv⟩ := exists_fresh_ftvar y b
    exact ⟨some (.ftvar v), AnnotInstantiates.ftvar t v, hv⟩

/-- Binder conditions of the abstraction and quantifier rules carry from an annotation's instance
    to the annotation. -/
private theorem binderAnnot_of_instantiates {T : LExprParams} {C : LContext T}
    {aliases : List TypeAlias} {o' o : Option LMonoTy} {xty : LMonoTy}
    (hty : AnnotInstantiates o' o)
    (ho : o' = none ∨ ∃ t, o' = some t ∧ LExpr.AnnotCompat aliases t xty)
    (h_valid : ∀ t, o' = some t → ∃ r, SourceTyWF C TyVarAdmissibility.all aliases t r) :
    (o = none ∨ ∃ t, o = some t ∧ LExpr.AnnotCompat aliases t xty) ∧
      (∀ t, o = some t → ∃ r, SourceTyWF C TyVarAdmissibility.all aliases t r) := by
  rcases hty with ⟨rfl, rfl⟩ | ⟨t, ρ, rfl, rfl⟩
  · exact ⟨ho, h_valid⟩
  · refine ⟨?_, ?_⟩
    · rcases ho with hcontra | ⟨t', ht', hcompat⟩
      · cases hcontra
      · cases ht'
        exact Or.inr ⟨t, rfl, annotCompat_of_subst ρ hcompat⟩
    · intro t' ht'
      cases ht'
      obtain ⟨r, hr⟩ := h_valid _ rfl
      exact SourceTyWF.of_subst [ρ] hr

/-- If `e'` is `e` with annotations replaced by instances, `e` has every type `e'` has. -/
theorem HasType_of_AnnotInstRewrite {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta} {e' : LExpr T.mono} {ty : LTy}
    (h : LExpr.HasType C Γ e' ty) :
    ∀ e : LExpr T.mono, AnnotInstRewrite e' e → LExpr.HasType C Γ e ty := by
  induction h with
  | tbool_const Γ' m b hk =>
    intro E hr; cases hr; exact LExpr.HasType.tbool_const Γ' m b hk
  | tint_const Γ' m n hk =>
    intro E hr; cases hr; exact LExpr.HasType.tint_const Γ' m n hk
  | treal_const Γ' m r hk =>
    intro E hr; cases hr; exact LExpr.HasType.treal_const Γ' m r hk
  | tstr_const Γ' m s hk =>
    intro E hr; cases hr; exact LExpr.HasType.tstr_const Γ' m s hk
  | tbitvec_const Γ' m n b hk =>
    intro E hr; cases hr; exact LExpr.HasType.tbitvec_const Γ' m n b hk
  | tmap_const Γ' m k v d es hk hw =>
    intro E hr; cases hr; exact LExpr.HasType.tmap_const Γ' m k v d es hk hw
  | tseq_const Γ' m a es hk hw =>
    intro E hr; cases hr; exact LExpr.HasType.tseq_const Γ' m a es hk hw
  | tvar Γ' m z tz h_find =>
    intro E hr
    cases hr with
    | fvar _ _ hstep =>
      rw [AnnotInstantiates.none_left hstep]
      exact LExpr.HasType.tvar Γ' m z tz h_find
  | tvar_annotated Γ' m z ty_o ty_s tys _ h_find h_len h_open h_ac =>
    intro E hr
    cases hr with
    | fvar _ _ hstep =>
      rcases hstep with ⟨hcontra, -⟩ | ⟨t, ρ, rfl, hann⟩
      · cases hcontra
      · cases hann
        exact LExpr.HasType.tvar_annotated Γ' m z ty_o ty_s tys t h_find h_len h_open
          (annotCompat_of_subst ρ h_ac)
  | tabs Γ' m name x x_ty _ e_ty _ h_efresh hx he _ ho h_valid ih =>
    intro E hr
    cases hr with
    | abs _ _ hty hb =>
      rename_i osrc bsrc
      obtain ⟨a, ha, hfresh⟩ := AnnotInstRewrite.exists_fresh hb x h_efresh
      have h_body' : LExpr.HasType C { Γ' with types := Γ'.types.insert x.1 x_ty }
          (LExpr.varOpen 0 ((x.1, a) : IdentT LMonoTy T.IDMeta) bsrc) e_ty :=
        ih _ (AnnotRel.varOpen hb (x := x) (x' := (x.1, a)) rfl ha 0)
      obtain ⟨ho', h_valid'⟩ := binderAnnot_of_instantiates hty ho h_valid
      exact LExpr.HasType.tabs Γ' m name (x.1, a) x_ty bsrc e_ty osrc hfresh hx he h_body' ho'
        h_valid'
  | tapp Γ' m _ _ t1 t2 h1 h2 _ _ ih1 ih2 =>
    intro E hr
    cases hr with
    | app _ hf he2 =>
      exact LExpr.HasType.tapp Γ' m _ _ t1 t2 h1 h2 (ih1 _ hf) (ih2 _ he2)
  | tinst Γ' _ ty0 e_ty a a_ty _ h_open ih =>
    intro E hr
    exact LExpr.HasType.tinst Γ' E ty0 e_ty a a_ty (ih E hr) h_open
  | tgen Γ' _ a ty0 _ h_fresh ih =>
    intro E hr
    exact LExpr.HasType.tgen Γ' E a ty0 (ih E hr) h_fresh
  | tif Γ' m _ _ _ ty0 _ _ _ ihc ih1 ih2 =>
    intro E hr
    cases hr with
    | ite _ hrc hr1 hr2 =>
      exact LExpr.HasType.tif Γ' m _ _ _ ty0 (ihc _ hrc) (ih1 _ hr1) (ih2 _ hr2)
  | teq Γ' m _ _ ty0 _ _ ih1 ih2 =>
    intro E hr
    cases hr with
    | eq _ hr1 hr2 =>
      exact LExpr.HasType.teq Γ' m _ _ ty0 (ih1 _ hr1) (ih2 _ hr2)
  | tquant Γ' m kd name _ tr_ty x x_ty _ _ h_efresh hx _ _ ho h_valid ih_body ih_tr =>
    intro E hr
    cases hr with
    | quant _ _ _ hty htr hb =>
      rename_i osrc trsrc bsrc
      obtain ⟨ho', h_valid'⟩ := binderAnnot_of_instantiates hty ho h_valid
      obtain ⟨a, ha, hfresh⟩ := AnnotInstRewrite.exists_fresh hb x h_efresh
      have h_body' : LExpr.HasType C { Γ' with types := Γ'.types.insert x.1 x_ty }
          (LExpr.varOpen 0 ((x.1, a) : IdentT LMonoTy T.IDMeta) bsrc)
          (.forAll [] LMonoTy.bool) :=
        ih_body _ (AnnotRel.varOpen hb (x := x) (x' := (x.1, a)) rfl ha 0)
      have h_tr' : LExpr.HasType C { Γ' with types := Γ'.types.insert x.1 x_ty }
          (LExpr.varOpen 0 ((x.1, a) : IdentT LMonoTy T.IDMeta) trsrc) tr_ty :=
        ih_tr _ (AnnotRel.varOpen htr (x := x) (x' := (x.1, a)) rfl ha 0)
      exact LExpr.HasType.tquant Γ' m kd name trsrc tr_ty (x.1, a) x_ty bsrc osrc
        hfresh hx h_body' h_tr' ho' h_valid'
  | top Γ' m f op ty0 h_get h_ty =>
    intro E hr
    cases hr with
    | op => exact LExpr.HasType.top Γ' m f op ty0 h_get h_ty
  | top_annotated Γ' m f op ty_o ty_s tys ann h_get h_ty h_len h_open h_ac =>
    intro E hr
    cases hr with
    | op =>
      exact LExpr.HasType.top_annotated Γ' m f op ty_o ty_s tys ann h_get h_ty h_len h_open h_ac
  | talias Γ' _ mty mty' h_ae _ ih =>
    intro E hr
    exact LExpr.HasType.talias Γ' E mty mty' h_ae (ih E hr)

/-! ## Re-choosing the annotation an opening injects -/

/-- Over a monotype-only scope, changing an opening's annotation to `none` or a type variable
    preserves typing. -/
private theorem HasType_varOpen_annotStep {T : LExprParams} [DecidableEq T.IDMeta]
    [Hashable T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta}
    (h_mono : MonoScope Γ) {k : Nat} {y : Identifier T.IDMeta} {a a' : Option LMonoTy}
    (h_step : AnnotStep a a') {e : LExpr T.mono} {ty : LTy}
    (h : LExpr.HasType C Γ (LExpr.varOpen k ((y, a) : IdentT LMonoTy T.IDMeta) e) ty) :
    LExpr.HasType C Γ (LExpr.varOpen k ((y, a') : IdentT LMonoTy T.IDMeta) e) ty :=
  HasType_of_AnnotRewrite h h_mono _
    (AnnotRel.varOpen (x := (y, a)) (x' := (y, a')) (AnnotRewrite.refl e) rfl h_step k)

/-- Over a monotype-only scope, re-annotating an opening with a type variable preserves typing. -/
theorem HasType_varOpen_ftvar {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta}
    (h_mono : MonoScope Γ) {k : Nat} {y : Identifier T.IDMeta} {a : Option LMonoTy}
    (v : TyIdentifier) {e : LExpr T.mono} {ty : LTy}
    (h : LExpr.HasType C Γ (LExpr.varOpen k ((y, a) : IdentT LMonoTy T.IDMeta) e) ty) :
    LExpr.HasType C Γ
      (LExpr.varOpen k ((y, some (LMonoTy.ftvar v)) : IdentT LMonoTy T.IDMeta) e) ty :=
  HasType_varOpen_annotStep h_mono (AnnotStep.tyvar a v) h

/-- Over a monotype-only scope, a body typed with `x` opened at a monotype keeps its type when `x`
    is re-annotated by some type variable outside `vs` keeping `x` fresh for `target`. -/
theorem HasType_varOpen_reopen {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta}
    (h_mono : MonoScope Γ) {x : IdentT LMonoTy T.IDMeta} {x_ty : LTy}
    (hx : LTy.isMonoType x_ty) {e : LExpr T.mono} {e_ty : LTy}
    (h_body : LExpr.HasType C { Γ with
        types := Γ.types.insert x.1 x_ty }
      (LExpr.varOpen 0 x e) e_ty)
    (target : LExpr T.mono) (vs : List TyIdentifier) :
    ∃ v : TyIdentifier,
      LExpr.fresh ((x.1, some (LMonoTy.ftvar v)) : IdentT LMonoTy T.IDMeta) target ∧ v ∉ vs ∧
      LExpr.HasType C { Γ with
          types := Γ.types.insert x.1 x_ty }
        (LExpr.varOpen 0 ((x.1, some (LMonoTy.ftvar v)) : IdentT LMonoTy T.IDMeta) e) e_ty := by
  obtain ⟨v, hfresh, hvs⟩ := exists_fresh_ftvar_avoiding x.1 target vs
  exact ⟨v, hfresh, hvs,
    HasType_varOpen_ftvar (h_mono.insert (List.isEmpty_iff.mp hx)) v h_body⟩

/-! ## Instantiating a whole quantifier prefix at once -/

/-- Opening a derivable scheme's whole prefix with names absent from the prefix is derivable. -/
private theorem HasType_openAll_rename {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono)
    (vars : List TyIdentifier) :
    ∀ (fs : List TyIdentifier) (mty : LMonoTy),
      fs.length = vars.length → vars.Nodup → (∀ f ∈ fs, f ∉ vars) →
      LExpr.HasType C Γ e (.forAll vars mty) →
      LExpr.HasType C Γ e
        (.forAll [] (LMonoTy.subst (Subst.ofZip vars (fs.map LMonoTy.ftvar)) mty)) := by
  induction vars with
  | nil =>
    intro fs mty _ _ _ h
    rw [LMonoTy.subst_ofZip_eq_self mty (fun x _ => by simp)]
    exact h
  | cons a rest ih =>
    intro fs mty h_len h_nd h_disj h
    cases fs with
    | nil => simp only [List.length_nil, List.length_cons] at h_len; omega
    | cons f fs' =>
      have h_a_rest : a ∉ rest := (List.nodup_cons.mp h_nd).1
      have h_f_notmem : f ∉ a :: rest := h_disj f (List.mem_cons_self ..)
      have h_f_rest : f ∉ rest := fun hc => h_f_notmem (List.mem_cons_of_mem a hc)
      have h_step : LExpr.HasType C Γ e
          (.forAll rest (LMonoTy.subst (Subst.singleton a (LMonoTy.ftvar f)) mty)) :=
        LExpr.HasType.tinst Γ e (.forAll (a :: rest) mty) _ a (.ftvar f) h
          (LTy.open_cons_of_not_mem (.ftvar f) mty h_a_rest).symm
      have h_len' : fs'.length = rest.length := by
        simp only [List.length_cons] at h_len; omega
      have h_disj' : ∀ g ∈ fs', g ∉ rest := by
        intro g hg hc
        exact h_disj g (List.mem_cons_of_mem f hg) (List.mem_cons_of_mem a hc)
      have hih := ih fs' (LMonoTy.subst (Subst.singleton a (LMonoTy.ftvar f)) mty)
        h_len' (List.nodup_cons.mp h_nd).2 h_disj' h_step
      have hcomp : LMonoTy.subst (Subst.ofZip (a :: rest) ((f :: fs').map LMonoTy.ftvar)) mty
          = LMonoTy.subst (Subst.ofZip rest (fs'.map LMonoTy.ftvar))
              (LMonoTy.subst (Subst.singleton a (LMonoTy.ftvar f)) mty) := by
        rw [List.map_cons]
        refine LMonoTy.subst_ofZip_cons mty h_a_rest ?_
        intro x hx
        rw [show LMonoTy.freeVars (LMonoTy.ftvar f) = [f] from rfl] at hx
        rw [List.mem_singleton.mp hx]
        exact h_f_rest
      rw [hcomp]
      exact hih

/-- Opening a derivable scheme's whole prefix at one monotype per binder is derivable. -/
theorem HasType_openAll {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono)
    (vars : List TyIdentifier) (mty : LMonoTy) (vals : List LMonoTy)
    (h : LExpr.HasType C Γ e (.forAll vars mty))
    (h_len : vals.length = vars.length) (h_nd : vars.Nodup) :
    LExpr.HasType C Γ e (.forAll [] (LMonoTy.subst (Subst.ofZip vars vals) mty)) := by
  obtain ⟨fs, h_fs_len, h_fs_nd, hfs_avoid⟩ := String.exists_freshStrings vars.length
    (TContext.knownTypeVars Γ ++ (vars ++ (LMonoTy.freeVars mty ++ LMonoTys.freeVars vals)))
  have h_fs_vars : ∀ f ∈ fs, f ∉ vars :=
    fun f hf hc => hfs_avoid f hf (List.mem_append_right _ (List.mem_append_left _ hc))
  have h_fs_mty : ∀ f ∈ fs, f ∉ LMonoTy.freeVars mty :=
    fun f hf hc => hfs_avoid f hf (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hc)))
  have h_fs_vals : ∀ f ∈ fs, f ∉ LMonoTys.freeVars vals :=
    fun f hf hc => hfs_avoid f hf (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hc)))
  have h_fs_fresh : ∀ f ∈ fs, TContext.isFresh (T := T) f Γ :=
    fun f hf => TContext.isFresh_of_not_mem_knownTypeVars
      (fun hc => hfs_avoid f hf (List.mem_append_left _ hc))
  have h_renamed := HasType_openAll_rename C Γ e vars fs mty h_fs_len h_nd h_fs_vars h
  have h_wf : SubstWF (Subst.ofZip fs vals) := by
    simp only [SubstWF, List.all_eq_true, decide_eq_true_eq]
    intro k hk hmem
    simp only [Subst.freeVars, List.mem_flatMap] at hmem
    obtain ⟨w, hw, hkw⟩ := hmem
    exact h_fs_vals k (Subst.mem_keys_ofZip hk)
      (LMonoTys.freeVars_mem_subset (Subst.mem_values_ofZip hw) hkw)
  have h_keys_fresh : ∀ k ∈ HMaps.keys (Subst.ofZip fs vals),
      k ∈ LMonoTy.freeVars (LMonoTy.subst (Subst.ofZip vars (fs.map LMonoTy.ftvar)) mty) →
      TContext.isFresh (T := T) k Γ :=
    fun k hk _ => h_fs_fresh k (Subst.mem_keys_ofZip hk)
  have h_final := LExpr.HasType_subst_fresh_all C Γ e _ _ h_renamed h_keys_fresh h_wf
  rwa [LMonoTy.subst_ofZip_launder mty h_fs_len h_len h_fs_nd h_fs_mty] at h_final

/-- `LTy.openFull` of a derivable scheme is derivable. -/
theorem HasType_openFull {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (C : LContext T) (Γ : TContext T.IDMeta) (e : LExpr T.mono)
    (ty : LTy) (vals : List LMonoTy)
    (h : LExpr.HasType C Γ e ty)
    (h_len : vals.length = ty.boundVars.length) (h_nd : ty.boundVars.Nodup) :
    LExpr.HasType C Γ e (.forAll [] (LTy.openFull ty vals)) := by
  cases ty with
  | forAll vars mty =>
    rw [LTy.openFull_eq_subst_ofZip]
    exact HasType_openAll C Γ e vars mty vals h h_len h_nd

/-! ## Signatures and closed contexts -/

/-- Pointwise lookup agreement preserves membership in a known-type table. -/
theorem containsName_of_getElem?_agree {ks ks' : KnownTypes}
    (h : ∀ x : String, ks'[x]? = ks[x]?) (n : String)
    (hn : KnownTypes.containsName ks n = true) : KnownTypes.containsName ks' n = true := by
  rw [KnownTypes.containsName_eq_true_iff_mem, Std.HashMap.mem_iff_isSome_getElem?, h n,
    ← Std.HashMap.mem_iff_isSome_getElem?, ← KnownTypes.containsName_eq_true_iff_mem]
  exact hn

/-- A well-formed factory reports closed type schemes with distinct binders. -/
theorem factory_type_nodup_closed {T : LExprParams} [DecidableEq T.IDMeta]
    {C : LContext T} {nm : String} {f : LFunc T} {ty0 : LTy}
    (h_fwf : FactorySigWF C.functions)
    (h_get : C.functions[nm]? = some f)
    (h_ty : f.type = .ok ty0) :
    (LTy.boundVars ty0).Nodup ∧
      ∀ x ∈ LMonoTy.freeVars (LTy.toMonoTypeUnsafe ty0), x ∈ LTy.boundVars ty0 := by
  have h_wf : LFuncSigWF f := h_fwf.lfuncs_wf f (Factory.getElem?_is_some_implies_mem h_get)
  have h_fv : LTy.freeVars ty0 = [] := LExpr.LFunc.type_freeVars_eq_nil f ty0 h_ty h_wf
  have h_bv : LTy.boundVars ty0 = f.typeArgs :=
    LExpr.LFunc.type_boundVars_eq_typeArgs f ty0 h_ty
  refine ⟨h_bv ▸ h_wf.typeArgs_nodup, ?_⟩
  cases ty0 with
  | forAll vars mty =>
    have h_removeAll : (LMonoTy.freeVars mty).removeAll vars = [] := by
      simpa only [LTy.freeVars] using h_fv
    intro x hx
    by_cases hc : x ∈ vars
    · exact hc
    · have hmem : x ∈ (LMonoTy.freeVars mty).removeAll vars := by
        simp only [List.removeAll, List.mem_filter]
        exact ⟨hx, by simp [hc]⟩
      rw [h_removeAll] at hmem
      exact absurd hmem (by simp)

open LExpr

variable {T : LExprParams} [Std.ToFormat T.IDMeta]

omit [Std.ToFormat T.IDMeta] in
/-- Substitution preserves a monotype-only context. -/
theorem MonoScope_subst [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (Γ : TContext T.IDMeta) (S : Subst) (hmono : MonoScope Γ) :
    MonoScope (TContext.subst Γ S) := by
  intro z tz hz
  obtain ⟨ty0, h0, heq⟩ := TContext_types_subst_find_reverse Γ.types S z tz hz
  rw [heq, LTy_subst_boundVars]
  exact hmono z ty0 h0

/-! ## Alias resolution against a type scope -/

/-- `TContext.resolveTy` computes the declarative alias resolution. -/
theorem TContext.resolveTy_sourceTyResolves [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (Γ : TContext T.IDMeta) (mty : LMonoTy) :
    SourceTyResolves Γ.aliases mty (Γ.resolveTy mty) :=
  LMonoTy.resolveAliases_sourceTyResolves mty _ _ _ (TContext.resolveTy_resolveAliases Γ mty)

/-- The alias resolver returns the resolution `resolveTy` computes in its context. -/
theorem TContext.resolveTy_of_resolveAliases [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {mty r : LMonoTy} {Env Env' : TEnv T.IDMeta}
    (h : LMonoTy.resolveAliases mty Env = .ok (r, Env')) : r = Env.context.resolveTy mty :=
  SourceTyResolves.unique (LMonoTy.resolveAliases_sourceTyResolves mty Env r Env' h)
    (TContext.resolveTy_sourceTyResolves Env.context mty)

/-- `resolveTy` computes the declarative alias resolution of each type of a list. -/
private theorem TContext.resolveTy_sourceTysResolve [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (Γ : TContext T.IDMeta) (mtys : LMonoTys) :
    SourceTysResolve Γ.aliases mtys (mtys.map Γ.resolveTy) := by
  induction mtys with
  | nil => exact SourceTysResolve.nil
  | cons t ts ih => exact SourceTysResolve.cons (TContext.resolveTy_sourceTyResolves Γ t) ih

/-- The list alias resolver resolves each type as `resolveTy` does in its context. -/
theorem TContext.resolveTys_of_resolveAliases [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {mtys rs : LMonoTys} {Env Env' : TEnv T.IDMeta}
    (h : LMonoTys.resolveAliases mtys Env = .ok (rs, Env')) :
    rs = mtys.map Env.context.resolveTy :=
  SourceTysResolve.unique (LMonoTys.resolveAliases_sourceTysResolve mtys Env rs Env' h)
    (TContext.resolveTy_sourceTysResolve Env.context mtys)

/-- With well-formed aliases, alias resolution commutes with a renaming of type variables. -/
theorem TContext.resolveTy_subst_renaming [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ : TContext T.IDMeta} (h : TContext.AliasesWF Γ) (S : Subst)
    (hS : ∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y) (t : LMonoTy) :
    Γ.resolveTy (LMonoTy.subst S t) = LMonoTy.subst S (Γ.resolveTy t) := by
  refine SourceTyResolves.unique (TContext.resolveTy_sourceTyResolves Γ _) ?_
  refine SourceTyResolves.subst (fun al hal => (h al hal).fvs_closed) S
    (TContext.resolveTy_sourceTyResolves Γ t) ?_
  intro v _
  obtain ⟨y, hy⟩ := hS v
  rw [hy]
  exact SourceTyResolves.ftvar

/-- Alias resolution against a context depends only on its aliases. -/
theorem TContext.resolveTy_congr [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ Γ' : TContext T.IDMeta} (h : Γ.aliases = Γ'.aliases) : Γ.resolveTy = Γ'.resolveTy := by
  funext mty
  have h2 := TContext.resolveTy_sourceTyResolves Γ' mty
  rw [← h] at h2
  exact SourceTyResolves.unique (TContext.resolveTy_sourceTyResolves Γ mty) h2

/-- Alias-resolving a scheme against a context depends only on its aliases. -/
theorem TContext.resolveScheme_congr [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ Γ' : TContext T.IDMeta} (h : Γ.aliases = Γ'.aliases) :
    Γ.resolveScheme = Γ'.resolveScheme := by
  funext ty
  obtain ⟨vs, mty⟩ := ty
  rw [TContext.resolveScheme_forAll, TContext.resolveScheme_forAll, TContext.resolveTy_congr h]

/-- A lookup in `Γ.dealias` finds the alias resolution of what `Γ` finds. -/
theorem TContext.dealias_find? [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (Γ : TContext T.IDMeta) (x : Identifier T.IDMeta) :
    Γ.dealias.types.find? x = (Γ.types.find? x).map Γ.resolveScheme := by
  simp only [TContext.dealias, TContext.resolveTypes, Strata.Util.HMaps.find?_mapValues]

/-- `dealias` keeps contexts lookup-equal. -/
theorem TContext.FindEq.dealias [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ Γ' : TContext T.IDMeta} (h : Γ.FindEq Γ') : TContext.FindEq Γ.dealias Γ'.dealias := by
  refine ⟨fun k => ?_, rfl⟩
  rw [TContext.dealias_find?, TContext.dealias_find?, h.find? k,
    TContext.resolveScheme_congr h.2]

omit [Std.ToFormat T.IDMeta] in
/-- A scope with the same lookups as a monotype-only scope is monotype-only. -/
theorem MonoScope_of_findEq [DecidableEq T.IDMeta] [Hashable T.IDMeta] {Γ Δ : TContext T.IDMeta}
    (hEq : TContext.FindEq Δ Γ) (h_mono : MonoScope Γ) : MonoScope Δ := by
  intro z tz hfind
  refine h_mono z tz ?_
  rw [← hEq.find? z]
  exact hfind

/-- Looking up a variable in a substituted scope stack returns the substitution applied to the
    scheme found in the original stack. -/
theorem TContext_subst_find? {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    (Δ : TContext IDMeta) (S : Subst) (x : Identifier IDMeta) :
    (TContext.subst Δ S).types.find? x = (Δ.types.find? x).map (LTy.subst S) :=
  Strata.Util.HMaps.find?_mapValues _ _ x

/-- A scope stores only unquantified schemes exactly when its substituted image does. -/
theorem MonoScope_subst_iff {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    (Γ : TContext IDMeta) (S : Subst) :
    MonoScope (TContext.subst Γ S) ↔ MonoScope Γ := by
  constructor
  · intro h z tz hfind
    have hs : (TContext.subst Γ S).types.find? z = some (LTy.subst S tz) := by
      rw [TContext_subst_find?, hfind, Option.map_some]
    rw [← LTy_subst_boundVars S tz]
    exact h z (LTy.subst S tz) hs
  · intro h z tz hfind
    rw [TContext_subst_find?] at hfind
    obtain ⟨tz0, hfind0, rfl⟩ := Option.map_eq_some_iff.mp hfind
    rw [LTy_subst_boundVars]
    exact h z tz0 hfind0

/-- A scope stores only unquantified schemes exactly when its resolved form does. -/
theorem MonoScope_dealias_iff {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    [Std.ToFormat IDMeta] (Γ : TContext IDMeta) :
    MonoScope Γ.dealias ↔ MonoScope Γ := by
  have hbv : ∀ t : LTy, LTy.boundVars (Γ.resolveScheme t) = LTy.boundVars t := by
    intro t
    obtain ⟨vs, mty⟩ := t
    rw [TContext.resolveScheme_forAll]
    rfl
  constructor
  · intro h z tz hfind
    have hs : Γ.dealias.types.find? z = some (Γ.resolveScheme tz) := by
      rw [TContext.dealias_find? (T := { Metadata := Unit, IDMeta := IDMeta }), hfind,
        Option.map_some]
    rw [← hbv tz]
    exact h z _ hs
  · intro h z tz hfind
    rw [TContext.dealias_find? (T := { Metadata := Unit, IDMeta := IDMeta })] at hfind
    obtain ⟨tz0, hfind0, rfl⟩ := Option.map_eq_some_iff.mp hfind
    rw [hbv]
    exact h z tz0 hfind0

/-- Resolving against a fresh extension of the aliases by unregistered names leaves the resolution
    of a type unchanged when that resolution is a registered instance. -/
theorem TContext.resolveTy_eq_of_FreshExtension [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ Γ' : TContext T.IDMeta} {ks : KnownTypes} {mty : LMonoTy}
    (hext : TypeAlias.FreshExtension Γ.aliases Γ'.aliases)
    (hfresh : ∀ al ∈ Γ'.aliases, al ∉ Γ.aliases → KnownTypes.containsName ks al.name = false)
    (hk : LMonoTy.knownInstance (Γ.resolveTy mty) ks = true) :
    Γ'.resolveTy mty = Γ.resolveTy mty :=
  LMonoTy.resolveAliases_eq_of_FreshExtension ks mty
    { genEnv := { context := Γ, genState := TState.init } }
    { genEnv := { context := Γ', genState := TState.init } } _ _ _ _ hext hfresh
    (TContext.resolveTy_resolveAliases Γ mty) (TContext.resolveTy_resolveAliases Γ' mty) hk

/-- Freshly extending the aliases of a type scope by unregistered names, keeping its types, keeps
    the lookups of the alias-resolved scope when every stored type resolves to a registered
    instance. -/
theorem TContext.dealias_FindEq_of_FreshExtension [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ Γ' : TContext T.IDMeta} {ks : KnownTypes}
    (htypes : Γ'.types = Γ.types) (hext : TypeAlias.FreshExtension Γ.aliases Γ'.aliases)
    (hfresh : ∀ al ∈ Γ'.aliases, al ∉ Γ.aliases → KnownTypes.containsName ks al.name = false)
    (hk : ∀ x vs mty, Γ.types.find? x = some (.forAll vs mty) →
      LMonoTy.knownInstance (Γ.resolveTy mty) ks = true) :
    TContext.FindEq Γ.dealias Γ'.dealias := by
  refine ⟨fun x => ?_, rfl⟩
  rw [TContext.dealias_find?, TContext.dealias_find?, htypes]
  cases hx : Γ.types.find? x with
  | none => rfl
  | some t =>
    obtain ⟨vs, mty⟩ := t
    simp only [Option.map_some, TContext.resolveScheme_forAll]
    rw [TContext.resolveTy_eq_of_FreshExtension hext hfresh (hk x vs mty hx)]

/-- `dealias` keeps contexts equivalent. -/
theorem TContext.Equiv.dealias [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ Γ' : TContext T.IDMeta} (h : Γ.Equiv Γ') : TContext.Equiv Γ.dealias Γ'.dealias := by
  refine ⟨?_, rfl⟩
  simp only [TContext.dealias, TContext.resolveTypes]
  rw [TContext.resolveScheme_congr h.2]
  exact Strata.Util.HMaps.mapValues_equiv _ h.1

/-- A registered instance resolves to itself when no alias name is registered. -/
theorem TContext.resolveTy_of_knownInstance [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ : TContext T.IDMeta} {ks : KnownTypes}
    (hfresh : ∀ al ∈ Γ.aliases, KnownTypes.containsName ks al.name = false)
    {mty : LMonoTy} (hkn : LMonoTy.knownInstance mty ks = true) : Γ.resolveTy mty = mty :=
  SourceTyResolves.unique (TContext.resolveTy_sourceTyResolves Γ mty)
    (SourceTyResolves.self_of_knownInstance hfresh mty hkn)

/-- A function whose input and output types are registered instances is unchanged by resolving
    its signature, when no alias name is registered. -/
private theorem LFunc.resolveSig_of_knownInstance [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ : TContext T.IDMeta} {ks : KnownTypes}
    (hfresh : ∀ al ∈ Γ.aliases, KnownTypes.containsName ks al.name = false) {f : LFunc T}
    (hkn : ∀ ty ∈ f.output :: f.inputs.values, LMonoTy.knownInstance ty ks = true) :
    LFunc.resolveSig Γ f = f := by
  have hout := TContext.resolveTy_of_knownInstance hfresh (hkn f.output List.mem_cons_self)
  have hvals : ∀ t ∈ f.inputs.values, Γ.resolveTy t = t := fun t ht =>
    TContext.resolveTy_of_knownInstance hfresh (hkn t (List.mem_cons_of_mem _ ht))
  have hins : Γ.resolveSig f.inputs = f.inputs := by
    simp only [TContext.resolveSig, ListMap.keys_eq_map_fst]
    rw [ListMap.values_eq_map_snd] at hvals ⊢
    generalize f.inputs = sig at hvals ⊢
    induction sig with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hvals ⊢
      rw [hvals.1, ih hvals.2]
  unfold LFunc.resolveSig
  rw [hout, hins]

/-- A table whose signatures are fixed for `A` is unchanged by resolving its signatures
    against `A`. -/
theorem LContext.resolveTable_eq_self [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {A : List TypeAlias} {C : LContext T} (hsig : FactorySigsFixed A C.functions) :
    C.resolveTable A = C := by
  have hmap : C.functions.map (LFunc.resolveSig ({ aliases := A } : TContext T.IDMeta))
      (fun _ => rfl) = C.functions := by
    refine Factory.map_eq_self _ _ _ fun f hf => ?_
    obtain ⟨ks, -, hfresh, hsigf⟩ := hsig f hf
    exact LFunc.resolveSig_of_knownInstance (Γ := { aliases := A }) hfresh hsigf
  simp only [LContext.resolveTable, hmap]

/-- When the signatures of `F` are fixed for the aliases of `Γ`, alias resolution against `Γ`
    leaves the body of each function's type scheme unchanged. -/
theorem FactorySigsFixed.resolveTy_body [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ : TContext T.IDMeta} {F : Factory T} (h : FactorySigsFixed Γ.aliases F) {f : LFunc T}
    (hf : f ∈ F.toArray) {xs : List TyIdentifier} {body : LMonoTy}
    (hty : f.type = .ok (.forAll xs body)) : Γ.resolveTy body = body := by
  obtain ⟨ks, harrow, hfresh, hsigf⟩ := h f hf
  exact TContext.resolveTy_of_knownInstance hfresh (LFunc.body_knownInstance harrow hsigf hty)

/-- With well-formed aliases, alias resolution against a context adds no free type variable. -/
theorem TContext.resolveTy_freeVars_subset [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ : TContext T.IDMeta} (h : TContext.AliasesWF Γ) (mty : LMonoTy) :
    ∀ v ∈ LMonoTy.freeVars (Γ.resolveTy mty), v ∈ LMonoTy.freeVars mty :=
  LMonoTy_resolveAliases_freeVars_subset mty _ _ _ (TContext.resolveTy_resolveAliases Γ mty) h

/-- With well-formed aliases, alias-resolving a scheme against a context adds no free type
    variable. -/
theorem TContext.resolveScheme_freeVars_subset [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {Γ : TContext T.IDMeta} (h : TContext.AliasesWF Γ) (ty : LTy) :
    ∀ v ∈ LTy.freeVars (Γ.resolveScheme ty), v ∈ LTy.freeVars ty := by
  obtain ⟨vs, mty⟩ := ty
  intro v hv
  rw [TContext.resolveScheme_forAll] at hv
  simp only [LTy.freeVars, List.removeAll, List.mem_filter] at hv ⊢
  exact ⟨TContext.resolveTy_freeVars_subset h mty v hv.1, hv.2⟩

/-- Instantiating a scheme gives its body under a substitution whose range is registered in every
    table. -/
private theorem LTy.instantiate_eq_subst [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {genEnv genEnv' : TGenEnv T.IDMeta} {xs : List TyIdentifier} {body mty : LMonoTy}
    (h : LTy.instantiate (.forAll xs body) genEnv = .ok (mty, genEnv')) :
    ∃ σ : Subst, mty = LMonoTy.subst σ body ∧ ∀ ks, Subst.RangeKnown σ ks := by
  have h_range : ∀ (l : List (TyIdentifier × LMonoTy)), (∀ p ∈ l, ∃ v, p.2 = .ftvar v) →
      ∀ ks, Subst.RangeKnown (Strata.Util.HMaps.ofScopes [l]) ks := by
    intro l hl ks t ht
    simp only [Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil, HMaps.values,
      List.append_nil] at ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (HMap.mem_values_ofList _ t ht)
    obtain ⟨v, hv⟩ := hl p hp
    rw [hv]
    rfl
  cases xs with
  | nil =>
    simp only [LTy.instantiate, Except.ok.injEq, Prod.mk.injEq] at h
    refine ⟨Strata.Util.HMaps.ofScopes [[]], ?_,
      h_range [] (fun p hp => absurd hp List.not_mem_nil)⟩
    rw [subst_ofScopes_nilScope]
    exact h.1.symm
  | cons x rest =>
    simp only [LTy.instantiate, Bind.bind, Except.bind] at h
    elim_err h with v1 h_gen
    obtain ⟨freshtvs, genEnv1⟩ := v1
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    refine ⟨_, h.1.symm, h_range _ ?_⟩
    intro p hp
    obtain ⟨tv, -, htv⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    exact ⟨tv, htv.symm⟩

/-- Checked instantiation of a scheme returns an instance of the scheme's body with the aliases of
    the context resolved, when every alias is well formed. -/
theorem LTy.instantiateWithCheck_eq_subst_resolveTy [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) {xs : List TyIdentifier} {body ty : LMonoTy}
    (h : LTy.instantiateWithCheck (.forAll xs body) C Env = .ok (ty, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∃ σ : Subst, ty = LMonoTy.subst σ (Env.context.resolveTy body) := by
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h with v1 h_res
  obtain ⟨mty, Env1⟩ := v1
  dsimp only [Bool.not_eq_eq_eq_not, Bool.not_true, pure, Except.pure] at h
  elim_err h
  elim_err h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_res
  elim_err h_res with v2 h_inst
  obtain ⟨mty0, genEnv1⟩ := v2
  dsimp only at h_res
  obtain ⟨σ, rfl, hσ⟩ := LTy.instantiate_eq_subst h_inst
  have h_ctx := LTy.instantiate_context _ _ _ _ h_inst
  have h_src := LMonoTy.resolveAliases_sourceTyResolves _ _ _ _ h_res
  simp only [TEnv.context, h_ctx] at h_src
  have hclosed : ∀ al ∈ Env.context.aliases, ∀ tv ∈ LMonoTy.freeVars al.type,
      tv ∈ al.typeArgs := fun al hal => (h_aw al hal).fvs_closed
  have hself : ∀ v ∈ LMonoTy.freeVars body, SourceTyResolves Env.context.aliases
      (LMonoTy.subst σ (.ftvar v)) (LMonoTy.subst σ (.ftvar v)) := by
    intro v _
    have hempty : ∀ al ∈ Env.context.aliases,
        KnownTypes.containsName (∅ : KnownTypes) al.name = false := by
      intro al _
      simp only [KnownTypes.containsName, Std.HashMap.contains_empty]
    have hvar : LMonoTy.knownInstance (.ftvar v) ∅ = true := by
      simp only [LMonoTy.knownInstance]
    have hkn : LMonoTy.knownInstance (LMonoTy.subst σ (.ftvar v)) ∅ = true :=
      knownInstance_subst ∅ σ (.ftvar v) (hσ ∅) hvar
    exact SourceTyResolves.self_of_knownInstance hempty _ hkn
  exact ⟨σ, SourceTyResolves.unique h_src (SourceTyResolves.subst₂ hclosed σ σ
    (TContext.resolveTy_sourceTyResolves Env.context body) hself)⟩

end -- public section

public section

namespace LExpr

section Proofs
attribute [local simp] Pure.pure Except.pure
variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]

/-! ### Context preservation by `resolveAux` -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- A successful `resolveAux` from a nonempty stack ends with a nonempty `Equiv` stack. -/
private theorem resolveAux_context_types_ne_equiv (C : LContext T) :
    ∀ (e : LExpr T.mono) (Env Env' : TEnv T.IDMeta) (et : LExprT T.mono),
      resolveAux C Env e = .ok (et, Env') →
      Env.context.types ≠ [] →
      Env'.context.types ≠ [] ∧ Env'.context.Equiv Env.context := by
  have hOfEq : ∀ (E E' : TEnv T.IDMeta), E'.context = E.context →
      E.context.types ≠ [] → E'.context.types ≠ [] ∧ E'.context.Equiv E.context := by
    intro E E' hEq hne
    rw [hEq]
    exact ⟨hne, TContext.Equiv.refl _⟩
  exact resolveAux_preserves C
    (fun E E' => E.context.types ≠ [] →
      E'.context.types ≠ [] ∧ E'.context.Equiv E.context)
    (fun E => hOfEq E E rfl)
    (fun _ _ _ h12 h23 hne =>
      ⟨(h23 (h12 hne).1).1, (h23 (h12 hne).1).2.trans (h12 hne).2⟩)
    (fun scheme E mty E' hinst =>
      hOfEq E E' (LTy_instantiateWithCheck_context scheme C E mty E' hinst))
    (fun ann E mty E' hinst =>
      hOfEq E E' (LMonoTy_instantiateWithCheck_context ann C E mty E' hinst))
    (fun E x fty mty E' hinfer => hOfEq E E' (inferFVar_context C E x fty mty E' hinfer))
    (fun E n E' hgen => hOfEq E E' (TEnv.genTyVar_context E n E' hgen))
    (fun _ E _ _ => hOfEq E _ rfl)
    (fun _ E _ _ _ _ => hOfEq E _ rfl)
    (fun E bty xv xty E1 E2 hboundOk h12 hne =>
      ⟨TEnv.eraseFromContext_types_ne_nil E2 xv
          (h12 (typeBoundVar_context_types_ne_nil C E bty xv xty E1 hboundOk)).1,
        eraseFromContext_typeBoundVar_equiv C E bty xv xty E1 hboundOk E2
          (h12 (typeBoundVar_context_types_ne_nil C E bty xv xty E1 hboundOk)).2 hne⟩)

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- A successful `resolveAux` keeps the type-scope stack nonempty. -/
private theorem resolveAux_context_types_ne (C : LContext T) :
    ∀ (e : LExpr T.mono) (Env Env' : TEnv T.IDMeta) (et : LExprT T.mono),
      resolveAux C Env e = .ok (et, Env') →
      Env.context.types ≠ [] →
      Env'.context.types ≠ [] :=
  fun e Env Env' et h hne => (resolveAux_context_types_ne_equiv C e Env Env' et h hne).1

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- A successful `resolveAux` from a nonempty stack preserves the context up to `Equiv`. -/
theorem resolveAux_context_equiv (C : LContext T) :
    ∀ (e : LExpr T.mono) (Env Env' : TEnv T.IDMeta) (et : LExprT T.mono),
      resolveAux C Env e = .ok (et, Env') →
      Env.context.types ≠ [] →
      Env'.context.Equiv Env.context :=
  fun e Env Env' et h hne => (resolveAux_context_types_ne_equiv C e Env Env' et h hne).2

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- A successful `resolve` runs `resolveAux` from the input environment, with one empty type
    scope added if it has none, then applies the final substitution. That start has a type scope,
    keeps the substitution, and is well formed whenever the input is. -/
theorem resolve_resolveAux_init
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok (et, Env')) :
    ∃ Env0 etAux, resolveAux C Env0 e = .ok (etAux, Env') ∧
      applySubstT etAux Env'.stateSubstInfo.subst = et ∧
      (TEnvWF Env → TEnvWF Env0) ∧ Env0.context.types ≠ [] ∧
      Env0.stateSubstInfo = Env.stateSubstInfo ∧
      Env0 = (if Env.context.types.isEmpty = true then
        Env.updateContext { Env.context with types := [.empty] }
      else Env) := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  generalize h_init : (if Env.context.types.isEmpty = true then
      Env.updateContext { Env.context with types := [.empty] }
    else Env) = Env0 at h
  match h_res : resolveAux C Env0 e with
  | .error _ => simp [h_res] at h
  | .ok (etAux, Env_out) =>
    simp only [h_res, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_et, h_env'⟩ := h
    subst h_env'
    refine ⟨Env0, etAux, h_res, h_et, ?_, ?_, ?_, rfl⟩
    · intro h_envwf
      subst h_init
      split
      · exact TEnvWF.updateContext_emptyScope Env h_envwf
      · exact h_envwf
    · subst h_init
      split
      · exact List.cons_ne_nil _ _
      · intro h_nil
        simp_all only [Bool.not_eq_true, Bool.false_eq_true, ↓reduceIte]
        contradiction
    · subst h_init
      split <;> rfl

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `resolve` returns at least one type scope, even from an empty stack. -/
theorem resolve_context_types_ne
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok ⟨e_typed, Env'⟩) :
    Env'.context.types ≠ [] := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  elim_err h with result haux
  obtain ⟨et, EnvR⟩ := result
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  split at haux
  · apply resolveAux_context_types_ne C _ _ _ _ haux
    simp only [TEnv.updateContext, TEnv.context]
    exact List.cons_ne_nil _ _
  · rename_i hnonempty
    apply resolveAux_context_types_ne C _ _ _ _ haux
    intro hnil
    have hisEmpty : Env.context.types.isEmpty = true := by rw [hnil]; rfl
    exact hnonempty hisEmpty

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- `resolve` preserves the alias list and, up to `Equiv`, every scope below the newest. -/
theorem resolve_context_pop_equiv
    (e : LExpr T.mono) (e_typed : LExprT T.mono) (C : LContext T)
    (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok ⟨e_typed, Env'⟩) :
    HMaps.Equiv Env'.context.types.pop Env.context.types.pop ∧
      Env'.context.aliases = Env.context.aliases := by
  cases hEmpty : Env.context.types.isEmpty with
  | true =>
    unfold LExpr.resolve at h
    simp only [Bind.bind, Except.bind] at h
    simp only [hEmpty, ite_true] at h
    elim_err h
    rename_i result hAux
    obtain ⟨et, EnvR⟩ := result
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hne_ctx :
        (Env.updateContext { Env.context with types := [HMap.empty] }).context.types ≠ [] := by
      simp [TEnv.updateContext, TEnv.context]
    have hctx := resolveAux_context_equiv C e
      (Env.updateContext { Env.context with types := [HMap.empty] }) EnvR et hAux
      hne_ctx
    have hTypesNil : Env.context.types = [] := HMaps.isEmpty_iff_eq_nil.mp hEmpty
    constructor
    · have hpop := hctx.1.pop
      show HMaps.Equiv EnvR.context.types.pop Env.context.types.pop
      rw [hTypesNil]
      simpa [TEnv.updateContext, TEnv.context, HMaps.pop] using hpop
    · simpa [TEnv.updateContext, TEnv.context] using hctx.2
  | false =>
    have hne : Env.context.types ≠ [] :=
      fun h => Bool.eq_false_iff.mp hEmpty (HMaps.isEmpty_iff_eq_nil.mpr h)
    obtain ⟨Env0, et, hAux, -, -, -, -, h_Env0⟩ := resolve_resolveAux_init e e_typed C Env Env' h
    simp only [hEmpty, Bool.false_eq_true, ite_false] at h_Env0
    rw [h_Env0] at hAux
    have hctx := resolveAux_context_equiv C e Env Env' et hAux hne
    exact ⟨hctx.1.pop, hctx.2⟩

/-! ### Shapes of resolved atomic nodes and resolver invariants -/

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Resolving a constant needs its type registered, stores that type, and keeps the environment. -/
theorem resolveAux_const_shape (C : LContext T) (Env Env' : TEnv T.IDMeta) (m : T.Metadata)
    (c : LConst) (et : LExprT T.mono)
    (h : resolveAux C Env (.const m c) = .ok (et, Env')) :
    C.knownTypes.containsName c.tyName = true ∧ inferConst C Env c = .ok (c.ty, Env) ∧
      et = .const ⟨m, c.ty⟩ c ∧ Env' = Env := by
  by_cases hk : (C.knownTypes.containsName c.tyName && c.wt &&
      (c.isPrimitive || c.ty.knownInstance C.knownTypes)) = true
  · have hinf : inferConst C Env c = .ok (c.ty, Env) := by
      simp only [inferConst, hk, ite_true]
    simp only [resolveAux, hinf, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hk
    exact ⟨hk.1.1, hinf, rfl, rfl⟩
  · simp only [resolveAux, inferConst, hk, ite_false, bind, Except.bind, reduceCtorEq] at h

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Resolving an operator annotates it with an instance of its factory scheme; a written
    annotation is then instantiated and unified with that instance. -/
theorem resolveAux_op_shape (C : LContext T) (Env Env' : TEnv T.IDMeta) (m : T.Metadata)
    (o : T.Identifier) (oty : Option LMonoTy) (et : LExprT T.mono)
    (h : resolveAux C Env (.op m o oty) = .ok (et, Env')) :
    ∃ func scheme ty Env1, C.functions[o.name]? = some func ∧ func.type = .ok scheme ∧
      LTy.instantiateWithCheck scheme C Env = .ok (ty, Env1) ∧
      et = .op ⟨m, ty⟩ o (some ty) ∧
      (Env' = Env1 ∨
        ∃ (ann ann' : LMonoTy) (Env2 : TEnv T.IDMeta) (S : SubstInfo),
          LMonoTy.instantiateWithCheck ann C Env1 = .ok (ann', Env2) ∧
          (Constraints.unify [(ty, ann')] Env2.stateSubstInfo).mapError format = .ok S ∧
          Env' = TEnv.updateSubst Env2 S) := by
  simp only [resolveAux, Bind.bind, Except.bind] at h
  elim_err h with func hfunc
  elim_err h with scheme htype
  elim_err h with pr hinst
  obtain ⟨ty, Env1⟩ := pr
  refine ⟨func, scheme, ty, Env1, hfunc, htype, hinst, ?_⟩
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1.symm, .inl h2.symm⟩
  · rename_i ann
    elim_err h with v2 hinst2
    obtain ⟨ann', Env2⟩ := v2
    dsimp only at h
    elim_err h with S hmap
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1.symm, .inr ⟨ann, ann', Env2, S, hinst2, hmap, h2.symm⟩⟩

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Resolving a free variable is an `inferFVar` call storing its type. -/
theorem resolveAux_fvar_shape (C : LContext T) (Env Env' : TEnv T.IDMeta) (m : T.Metadata)
    (x : T.Identifier) (fty : Option LMonoTy) (et : LExprT T.mono)
    (h : resolveAux C Env (.fvar m x fty) = .ok (et, Env')) :
    ∃ ty, inferFVar C Env x fty = .ok (ty, Env') ∧ et = .fvar ⟨m, ty⟩ x (some ty) := by
  simp only [resolveAux, Bind.bind, Except.bind] at h
  elim_err h
  rename_i r hinfer
  obtain ⟨ty, Env1⟩ := r
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨ty, hinfer, rfl⟩

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata] in
/-- Resolving under a fresh substitution scope, then popping it, keeps the context closed and
    `FindEq` to the original. -/
theorem resolve_pushSubstScope_context_FindEq
    (C : LContext T) (Env : TEnv T.IDMeta) (e : LExpr T.mono) (i : Identifiers T.IDMeta)
    (v : LExprT T.mono × TEnv T.IDMeta)
    (h_res : LExpr.resolve { C with idents := i } Env.pushEmptySubstScope e = .ok v)
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions) :
    TContext.FindEq (T := T) (TEnv.context v.snd.popSubstScope) (TEnv.context Env)
      ∧ (checkContextTypesClosed (T := T) Env →
          checkContextTypesClosed (T := T) v.snd.popSubstScope) := by
  obtain ⟨e_typed, Env'⟩ := v
  have h_envwf_push : TEnvWF (T := T) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF Env h_envwf
  by_cases h_ne : Env.context.types ≠ []
  · have h_ne_push : Env.pushEmptySubstScope.context.types ≠ [] := by
      simpa only [TEnv.pushEmptySubstScope_context_eq] using h_ne
    have h_ctx : Env'.context.Equiv Env.pushEmptySubstScope.context :=
      resolve_preserves_context e e_typed { C with idents := i }
        Env.pushEmptySubstScope Env' h_res h_envwf_push h_ne_push h_fwf
    have h_ctx' : Env'.context.Equiv Env.context := by
      simpa only [TEnv.pushEmptySubstScope_context_eq] using h_ctx
    constructor
    · simpa only [TEnv.popSubstScope_context_eq] using h_ctx'.toFindEq
    · intro h_closed
      simpa only [checkContextTypesClosed, TEnv.popSubstScope_context_eq] using
        checkContextTypesClosed_of_ctx_eq h_closed h_ctx'
  · have h_nil : Env.context.types = [] := Classical.not_not.mp h_ne
    unfold LExpr.resolve at h_res
    simp only [Bind.bind, Except.bind] at h_res
    have h_empty : Env.pushEmptySubstScope.context.types.isEmpty = true := by
      rw [TEnv.pushEmptySubstScope_context_eq, h_nil]
      rfl
    simp only [h_empty, ite_true] at h_res
    elim_err h_res
    rename_i w h_aux
    obtain ⟨et, Env_r⟩ := w
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_res
    obtain ⟨h_typed, h_env'⟩ := h_res
    subst h_env'
    let Env_upd :=
      Env.pushEmptySubstScope.updateContext
        { Env.pushEmptySubstScope.context with types := [HMap.empty] }
    have h_upd_ctx_eq : Env_upd.context =
        { types := [HMap.empty], aliases := Env.context.aliases } := by
      simp [Env_upd, TEnv.updateContext, TEnv.context, TEnv.pushEmptySubstScope]
    have h_aux' :
        resolveAux { C with idents := i } Env_upd e = .ok (et, Env_r) := by
      simp only [Env_upd, TEnv.updateContext] at h_aux ⊢
      exact h_aux
    have h_upd_ne : Env_upd.context.types ≠ [] := by
      simp [Env_upd, TEnv.updateContext, TEnv.context]
    have h_ctx_upd : Env_r.context.Equiv Env_upd.context :=
      resolveAux_context_equiv { C with idents := i } e Env_upd Env_r et h_aux' h_upd_ne
    have h_base : Env_upd.context.FindEq Env.context := by
      rw [h_upd_ctx_eq]
      refine ⟨?_, rfl⟩
      intro k
      rw [h_nil]
      simp [HMaps.find?, HMap.find?_empty]
    have h_find : Env_r.context.FindEq Env.context :=
      h_ctx_upd.toFindEq.trans h_base
    have h_check_upd : checkContextTypesClosed (T := T) Env_upd := by
      simp only [checkContextTypesClosed, h_upd_ctx_eq, List.all_cons, List.all_nil,
        Bool.and_true, HMap.all, HMap.empty, ← Std.HashMap.all_toList,
        Std.HashMap.toList_emptyWithCapacity]
    have h_check_r : checkContextTypesClosed (T := T) Env_r :=
      checkContextTypesClosed_of_ctx_eq h_check_upd h_ctx_upd
    constructor
    · simpa only [TEnv.popSubstScope_context_eq] using h_find
    · intro _
      simpa only [checkContextTypesClosed, TEnv.popSubstScope_context_eq] using h_check_r

end Proofs

end LExpr

namespace LExpr

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta] [HasGen T.IDMeta] [Std.ToFormat (LFunc T)]

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- `resolveAux` keeps the range registered and reports a registered type, when arrows, Booleans
    and literal types are registered. -/
theorem resolveAux_RangeKnown
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (h_fwf : FactorySigWF C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_bool : C.knownTypes["bool"]? = some 0)
    (h_lit : LiteralTysKnown C)
    (hS : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes ∧
    LMonoTy.knownInstance et.toLMonoTy C.knownTypes = true := by
  refine resolveAux_ind
    (P := fun _ et C Env Env' =>
      C.knownTypes["arrow"]? = some 2 → C.knownTypes["bool"]? = some 0 → LiteralTysKnown C →
      Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes →
      Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes ∧
      LMonoTy.knownInstance et.toLMonoTy C.knownTypes = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    e et C Env Env' h_res h_envwf h_ne h_fwf h_arrow h_bool h_lit hS
  · intro m c et C Env Env' h_r _ _ _ _ _ h_lit hS
    obtain ⟨-, h_ic, rfl, rfl⟩ := resolveAux_const_shape C Env Env' m c et h_r
    exact ⟨hS, (inferConst_knownInstance C _ c c.ty _ h_ic h_lit).1⟩
  · intro m o oty et C Env Env' h_r _ _ _ _ _ _ hS
    obtain ⟨-, tyScheme, mty, Env1, -, -, h_inst, rfl, h_env⟩ :=
      resolveAux_op_shape C Env Env' m o oty et h_r
    obtain ⟨h_subst, h_mty⟩ :=
      LTy_instantiateWithCheck_subst_knownInstance tyScheme C Env mty Env1 h_inst
    have h_S1 : Subst.RangeKnown Env1.stateSubstInfo.subst C.knownTypes := by
      rw [h_subst]; exact hS
    rcases h_env with rfl | ⟨oty_val, oty_inst, Env2, S, h_inst2, h_mapError, rfl⟩
    · exact ⟨h_S1, h_mty⟩
    · exact ⟨instantiateAnnot_unify_RangeKnown C Env1 Env2 oty_val oty_inst mty _ S
        h_inst2 h_mapError (.inr rfl) h_mty h_S1, h_mty⟩
  · intro m x fty et C Env Env' h_r _ _ _ _ _ _ hS
    obtain ⟨ty, h_if, rfl⟩ := resolveAux_fvar_shape C Env Env' m x fty et h_r
    exact inferFVar_RangeKnown C Env x fty ty Env' h_if hS
  · intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      _ _ _ h_gen h_unify h_et h_env' _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2
      h_arrow h_bool h_lit hS
    obtain ⟨hS1, hk1⟩ := ih1 h_arrow h_bool h_lit hS
    obtain ⟨hS2, hk2⟩ := ih2 h_arrow h_bool h_lit hS1
    have hSgen : Subst.RangeKnown Env_gen.stateSubstInfo.subst C.knownTypes := by
      rw [TEnv.genTyVar_subst Env2 fresh_name Env_gen h_gen]; exact hS2
    have hftv : LMonoTy.knownInstance (.ftvar fresh_name) C.knownTypes = true := by
      simp only [LMonoTy.knownInstance]
    have harr : LMonoTy.knownInstance
        (.arrow e2t.toLMonoTy (.ftvar fresh_name)) C.knownTypes = true :=
      knownInstance_arrow C.knownTypes _ _ h_arrow hk2 hftv
    have hSu : Subst.RangeKnown substInfo.subst C.knownTypes := by
      refine Constraints.unify_RangeKnown C.knownTypes _ Env_gen.stateSubstInfo substInfo
        h_unify hSgen ?_
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨hk1, harr⟩
    refine ⟨?_, ?_⟩
    · rw [h_env']
      exact Subst.RangeKnown_remove C.knownTypes substInfo.subst fresh_name hSu
    · rw [h_et]
      exact knownInstance_subst C.knownTypes substInfo.subst _ hSu hftv
  · intro m name bty body et C Env Env' xv xty Env1 et_body Env2
      _ h_tbv _ h_et h_env' _ _ _ _ _ _ ih h_arrow h_bool h_lit hS
    obtain ⟨hsub1, hxty⟩ := typeBoundVar_subst_knownInstance C Env bty xv xty Env1 h_tbv
    have hS1 : Subst.RangeKnown Env1.stateSubstInfo.subst C.knownTypes := by
      rw [hsub1]; exact hS
    obtain ⟨hS2, hkb⟩ := ih h_arrow h_bool h_lit hS1
    refine ⟨?_, ?_⟩
    · rw [h_env']
      simpa only [TEnv.eraseFromContext, TEnv.updateContext] using hS2
    · rw [h_et]
      refine knownInstance_subst C.knownTypes _ _ hS2 ?_
      refine knownInstance_arrow C.knownTypes _ _ h_arrow hxty ?_
      rw [varCloseT_toLMonoTy]
      exact hkb
  · intro m qk name bty triggers body et C Env Env' xv xty Env1 et_body Env2 et_tr Env3 substInfo
      _ h_tbv _ _ h_unify h_et h_env' _ _ _ _ _ _ _ _ _ ihb iht h_arrow h_bool h_lit hS
    obtain ⟨hsub1, _⟩ := typeBoundVar_subst_knownInstance C Env bty xv xty Env1 h_tbv
    have hS1 : Subst.RangeKnown Env1.stateSubstInfo.subst C.knownTypes := by
      rw [hsub1]; exact hS
    obtain ⟨hS2, hkb⟩ := ihb h_arrow h_bool h_lit hS1
    obtain ⟨hS3, _⟩ := iht h_arrow h_bool h_lit hS2
    have hbool : LMonoTy.knownInstance LMonoTy.bool C.knownTypes = true :=
      knownInstance_nullary C.knownTypes "bool" h_bool
    have hSu : Subst.RangeKnown substInfo.subst C.knownTypes := by
      refine Constraints.unify_RangeKnown C.knownTypes _ Env3.stateSubstInfo substInfo
        h_unify hS3 ?_
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨hkb, hbool⟩
    refine ⟨?_, ?_⟩
    · rw [h_env']
      simpa only [TEnv.eraseFromContext, TEnv.updateContext, TEnv.updateSubst] using hSu
    · rw [h_et]
      exact hbool
  · intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      _ _ _ h_unify h_et h_env' _ _ _ _ _ _ _ _ _ ih1 ih2 h_arrow h_bool h_lit hS
    obtain ⟨hS1, hk1⟩ := ih1 h_arrow h_bool h_lit hS
    obtain ⟨hS2, hk2⟩ := ih2 h_arrow h_bool h_lit hS1
    refine ⟨?_, ?_⟩
    · rw [h_env']
      refine Constraints.unify_RangeKnown C.knownTypes _ Env2.stateSubstInfo substInfo
        h_unify hS2 ?_
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨hk1, hk2⟩
    · rw [h_et]
      exact knownInstance_nullary C.knownTypes "bool" h_bool
  · intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      _ _ _ _ h_unify h_et h_env' _ _ _ _ _ _ _ _ _ _ _ ihc iht ihe
      h_arrow h_bool h_lit hS
    obtain ⟨hS1, hkc⟩ := ihc h_arrow h_bool h_lit hS
    obtain ⟨hS2, hkt⟩ := iht h_arrow h_bool h_lit hS1
    obtain ⟨hS3, hke⟩ := ihe h_arrow h_bool h_lit hS2
    have hbool : LMonoTy.knownInstance LMonoTy.bool C.knownTypes = true :=
      knownInstance_nullary C.knownTypes "bool" h_bool
    refine ⟨?_, ?_⟩
    · rw [h_env']
      refine Constraints.unify_RangeKnown C.knownTypes _ Env3.stateSubstInfo substInfo
        h_unify hS3 ?_
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨hkc, hbool⟩
      · rw [List.mem_singleton] at hp'
        subst hp'
        exact ⟨hkt, hke⟩
    · rw [h_et]
      exact hkt

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- When `ps` holds no generated name, `resolveAux` keeps the substitution and type avoiding `ps`;
    its annotations avoid `ps` under any later `ps`-avoiding substitution that absorbs its own. -/
theorem resolveAux_varsAvoid {ps : List TyIdentifier}
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (h_fwf : FactorySigWF C.functions)
    (hgen : NoGenName ps) (hE : TEnv.VarsAvoid Env ps) :
    Subst.VarsAvoid Env'.stateSubstInfo.subst ps ∧
      (∀ v ∈ LMonoTy.freeVars et.toLMonoTy, v ∉ ps) ∧
      ∀ S : Subst, Subst.absorbs S Env'.stateSubstInfo.subst → Subst.VarsAvoid S ps →
        AnnotsAvoid (LExpr.unresolved (LExpr.applySubstT et S)) ps := by
  have hgenName : ∀ (E E' : TEnv T.IDMeta) (n : TyIdentifier), TEnv.genTyVar E = .ok (n, E') →
      n ∉ ps := by
    intro E E' n hg
    rw [genTyVar_name_eq E n E' hg]
    exact hgen _
  refine resolveAux_ind
    (P := fun _ et _ Env Env' => TEnv.VarsAvoid Env ps →
      Subst.VarsAvoid Env'.stateSubstInfo.subst ps ∧
      (∀ v ∈ LMonoTy.freeVars et.toLMonoTy, v ∉ ps) ∧
      ∀ S : Subst, Subst.absorbs S Env'.stateSubstInfo.subst → Subst.VarsAvoid S ps →
        AnnotsAvoid (LExpr.unresolved (LExpr.applySubstT et S)) ps)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e et C Env Env' h_res h_envwf h_ne h_fwf hE
  · intro m c et C Env Env' h_r _ _ _ hE
    obtain ⟨-, -, rfl, rfl⟩ := resolveAux_const_shape C Env Env' m c et h_r
    refine ⟨hE.1, ?_, ?_⟩
    · intro v hv
      simp only [toLMonoTy, LConst.ty_freeVars, List.not_mem_nil] at hv
    · intro S _ _ t ht
      simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved, LExpr.fvarAnnotations,
        LExpr.binderAnnotations] at ht
  · intro m o oty et C Env Env' h_r h_wf _ h_fwf hE
    obtain ⟨func, tyScheme, mty, Env1, h_func, h_type, h_inst, rfl, h_env⟩ :=
      resolveAux_op_shape C Env Env' m o oty et h_r
    have h_closed : LTy.freeVars tyScheme = [] :=
      LFunc.type_freeVars_eq_nil func tyScheme h_type
        (h_fwf.lfuncs_wf func (Factory.getElem?_is_some_implies_mem h_func))
    have h_mty : ∀ v ∈ LMonoTy.freeVars mty, v ∉ ps := by
      intro v hv
      rcases LTy_instantiateWithCheck_freeVars tyScheme C Env mty Env1 h_inst h_wf.aliasesWF v hv
        with hv | ⟨k, rfl⟩
      · rw [h_closed] at hv
        exact absurd hv List.not_mem_nil
      · exact hgen k
    have h_S1 : Subst.VarsAvoid Env1.stateSubstInfo.subst ps := by
      rw [(LTy_instantiateWithCheck_subst_knownInstance tyScheme C Env mty Env1 h_inst).1]
      exact hE.1
    have h_annots : ∀ S : Subst,
        AnnotsAvoid (LExpr.unresolved (LExpr.applySubstT (.op ⟨m, mty⟩ o (some mty)) S)) ps := by
      intro S t ht
      simp [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved, LExpr.fvarAnnotations,
        LExpr.binderAnnotations] at ht
    rcases h_env with rfl | ⟨oty_val, oty_inst, Env2, S, h_inst2, h_mapError, rfl⟩
    · exact ⟨h_S1, h_mty, fun S _ _ => h_annots S⟩
    · have h_aw1 : TContext.AliasesWF Env1.context :=
        (LTy_instantiateWithCheck_context' tyScheme C Env mty Env1 h_inst) ▸ h_wf.aliasesWF
      have h_oty : ∀ v ∈ LMonoTy.freeVars oty_inst, v ∉ ps := by
        intro v hv
        obtain ⟨k, rfl⟩ := LMonoTy_instantiateWithCheck_freeVars_genName oty_val C Env1 oty_inst
          Env2 h_inst2 h_aw1 v hv
        exact hgen k
      have h_S2 : Subst.VarsAvoid Env2.stateSubstInfo.subst ps := by
        rw [(LMonoTy_instantiateWithCheck_subst_knownInstance oty_val C Env1 oty_inst Env2
          h_inst2).1]
        exact h_S1
      refine ⟨?_, h_mty, fun S' _ _ => h_annots S'⟩
      simp only [TEnv.updateSubst]
      refine Constraints.unify_varsAvoid (unify_of_mapError h_mapError) h_S2
        (Constraints.freeVars_varsAvoid ?_)
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨h_mty, h_oty⟩
  · intro m x fty et C Env Env' h_r h_wf _ _ hE
    obtain ⟨ty, h_if, rfl⟩ := resolveAux_fvar_shape C Env Env' m x fty et h_r
    obtain ⟨hS', hty⟩ := inferFVar_varsAvoid C Env x fty ty Env' h_if h_wf.aliasesWF hgen hE
    refine ⟨hS', hty, ?_⟩
    intro S _ hSS t ht
    simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved, LExpr.fvarAnnotations,
      LExpr.binderAnnotations, Option.toList, List.append_nil, List.mem_singleton] at ht
    subst ht
    exact LMonoTy.subst_varsAvoid hSS hty
  · intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 fresh_name Env_gen substInfo
      _ _ _ h_gen h_unify h_et h_env' hAbs1 hAbs2 _ _ _ _ _ _ _ hCtx1 _ hCtx2 ih1 ih2 hE
    obtain ⟨hS1, hk1, ha1⟩ := ih1 hE
    obtain ⟨hS2, hk2, ha2⟩ := ih2 ⟨hS1, hE.2.of_equiv hCtx1⟩
    have hSgen : Subst.VarsAvoid Env_gen.stateSubstInfo.subst ps := by
      rw [TEnv.genTyVar_subst Env2 fresh_name Env_gen h_gen]
      exact hS2
    have hfresh : ∀ v ∈ LMonoTy.freeVars (.ftvar fresh_name), v ∉ ps := by
      intro v hv
      simp only [LMonoTy.freeVars, List.mem_singleton] at hv
      subst hv
      exact hgenName _ _ _ h_gen
    have hSu : Subst.VarsAvoid substInfo.subst ps := by
      refine Constraints.unify_varsAvoid h_unify hSgen (Constraints.freeVars_varsAvoid ?_)
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      refine ⟨hk1, ?_⟩
      intro v hv
      simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hk2 v hv
      · exact hfresh v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [h_env']
      exact hSu.remove fresh_name
    · rw [h_et]
      exact LMonoTy.subst_varsAvoid hSu hfresh
    · intro S hAbs hSS
      subst h_et
      rw [h_env'] at hAbs
      have h1 := ha1 S (Subst.absorbs_trans _ _ _ hAbs1 hAbs) hSS
      have h2 := ha2 S (Subst.absorbs_trans _ _ _ hAbs2 hAbs) hSS
      exact (LExpr.AnnotsAvoid.append_iff rfl rfl).mpr ⟨h1, h2⟩
  · intro m name bty body et C Env Env' xv xty Env1 et_body Env2
      _ h_tbv _ h_et h_env' h_wf _ _ _ _ _ ih hE
    obtain ⟨hE1, hxty⟩ := typeBoundVar_varsAvoid C Env bty xv xty Env1 h_tbv h_wf.aliasesWF hgen hE
    obtain ⟨hS2, hkb, hab⟩ := ih hE1
    have hEnv'S : Env'.stateSubstInfo.subst = Env2.stateSubstInfo.subst := by
      rw [h_env']
      rfl
    refine ⟨hEnv'S ▸ hS2, ?_, ?_⟩
    · rw [h_et]
      refine LMonoTy.subst_varsAvoid hS2 ?_
      intro v hv
      simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.append_nil, List.mem_append,
        varCloseT_toLMonoTy] at hv
      rcases hv with hv | hv
      · exact hxty v hv
      · exact hkb v hv
    · intro S hAbs hSS
      subst h_et
      rw [hEnv'S] at hAbs
      have hArrowSubst :
          LMonoTy.subst S
              (LMonoTy.subst Env2.stateSubstInfo.subst
                (.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy])) =
            .tcons "arrow" [LMonoTy.subst S xty, LMonoTy.subst S et_body.toLMonoTy] := by
        rw [varCloseT_toLMonoTy, LMonoTy.subst_absorbs S Env2.stateSubstInfo.subst _ hAbs,
          LMonoTy.subst_tcons_pair]
      have hStoredAbs :
          LExpr.unresolved (LExpr.applySubstT
            (.abs ⟨m, LMonoTy.subst Env2.stateSubstInfo.subst
              (.tcons "arrow" [xty, (LExpr.varCloseT 0 xv et_body).toLMonoTy])⟩
              name bty (LExpr.varCloseT 0 xv et_body)) S) =
            .abs m name (some (LMonoTy.subst S xty))
              (LExpr.unresolved (LExpr.applySubstT (LExpr.varCloseT 0 xv et_body) S)) := by
        simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved]
        rw [hArrowSubst]
        simp only [LMonoTy.isArrow]
      have hb := hab S hAbs hSS
      rw [hStoredAbs, applySubstT_varCloseT_comm]
      intro t ht
      simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, Option.toList, List.cons_append,
        List.nil_append, List.mem_append, List.mem_cons] at ht
      rw [LExpr.Proofs.binderAnnotations_unresolved_varCloseT] at ht
      rcases ht with ht | rfl | ht
      · exact hb t (List.mem_append_left _
          (LExpr.Proofs.fvarAnnotations_unresolved_varCloseT_subset _ _ _ t ht))
      · exact LMonoTy.subst_varsAvoid hSS hxty
      · exact hb t (List.mem_append_right _ ht)
  · intro m qk name bty triggers body et C Env Env' xv xty Env1 et_body Env2 et_tr Env3 substInfo
      _ h_tbv _ _ h_unify h_et h_env' hAbs32 h_wf _ _ _ _ _ _ hCtx2 ihb iht hE
    obtain ⟨hE1, hxty⟩ := typeBoundVar_varsAvoid C Env bty xv xty Env1 h_tbv h_wf.aliasesWF hgen hE
    obtain ⟨hS2, hkb, hab⟩ := ihb hE1
    obtain ⟨hS3, -, hat⟩ := iht ⟨hS2, hE1.2.of_equiv hCtx2⟩
    have hSu : Subst.VarsAvoid substInfo.subst ps := by
      refine Constraints.unify_varsAvoid h_unify hS3 (Constraints.freeVars_varsAvoid ?_)
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      refine ⟨hkb, ?_⟩
      intro v hv
      simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.not_mem_nil] at hv
    have hEnv'S : Env'.stateSubstInfo.subst = substInfo.subst := by
      rw [h_env']
      rfl
    refine ⟨hEnv'S ▸ hSu, ?_, ?_⟩
    · rw [h_et]
      intro v hv
      simp only [toLMonoTy, LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars,
        List.not_mem_nil] at hv
    · intro S hAbs hSS
      subst h_et
      rw [hEnv'S] at hAbs
      have hAbs3 : Subst.absorbs S Env3.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ h_unify) hAbs
      have hAbs2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ hAbs32 hAbs3
      have hXty : LMonoTy.subst S (LMonoTy.subst substInfo.subst xty) = LMonoTy.subst S xty :=
        LMonoTy.subst_absorbs S substInfo.subst xty hAbs
      have hb := hab S hAbs2 hSS
      have htr := hat S hAbs3 hSS
      simp only [LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved]
      rw [hXty]
      change AnnotsAvoid
        (.quant m qk name (some (LMonoTy.subst S xty))
          (LExpr.unresolved (LExpr.applySubstT (LExpr.varCloseT 0 xv et_tr) S))
          (LExpr.unresolved (LExpr.applySubstT (LExpr.varCloseT 0 xv et_body) S))) ps
      rw [applySubstT_varCloseT_comm, applySubstT_varCloseT_comm]
      intro t ht
      simp only [LExpr.fvarAnnotations, LExpr.binderAnnotations, Option.toList, List.cons_append,
        List.nil_append, List.mem_append, List.mem_cons] at ht
      rw [LExpr.Proofs.binderAnnotations_unresolved_varCloseT,
        LExpr.Proofs.binderAnnotations_unresolved_varCloseT] at ht
      rcases ht with (ht | ht) | rfl | ht | ht
      · exact htr t (List.mem_append_left _
          (LExpr.Proofs.fvarAnnotations_unresolved_varCloseT_subset _ _ _ t ht))
      · exact hb t (List.mem_append_left _
          (LExpr.Proofs.fvarAnnotations_unresolved_varCloseT_subset _ _ _ t ht))
      · exact LMonoTy.subst_varsAvoid hSS hxty
      · exact htr t (List.mem_append_right _ ht)
      · exact hb t (List.mem_append_right _ ht)
  · intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      _ _ _ h_unify h_et h_env' _ hAbs2 _ _ _ _ hCtx1 _ _ ih1 ih2 hE
    obtain ⟨hS1, hk1, ha1⟩ := ih1 hE
    obtain ⟨hS2, hk2, ha2⟩ := ih2 ⟨hS1, hE.2.of_equiv hCtx1⟩
    have hSu : Subst.VarsAvoid substInfo.subst ps := by
      refine Constraints.unify_varsAvoid h_unify hS2 (Constraints.freeVars_varsAvoid ?_)
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨hk1, hk2⟩
    refine ⟨h_env' ▸ hSu, ?_, ?_⟩
    · rw [h_et]
      intro v hv
      simp only [toLMonoTy, LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars,
        List.not_mem_nil] at hv
    · intro S hAbs hSS
      subst h_et
      rw [h_env'] at hAbs
      have hAbs2S : Subst.absorbs S Env2.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ h_unify) hAbs
      have h1 := ha1 S (Subst.absorbs_trans _ _ _ hAbs2 hAbs2S) hSS
      have h2 := ha2 S hAbs2S hSS
      exact (LExpr.AnnotsAvoid.append_iff rfl rfl).mpr ⟨h1, h2⟩
  · intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      _ _ _ _ h_unify h_et h_env' hAbs12 hAbs23 _ _ _ _ hCtx1 _ hCtx2 _ _ ihc iht ihe hE
    obtain ⟨hS1, hkc, hac⟩ := ihc hE
    obtain ⟨hS2, hkt, hat⟩ := iht ⟨hS1, hE.2.of_equiv hCtx1⟩
    obtain ⟨hS3, hke, hae⟩ := ihe ⟨hS2, hE.2.of_equiv hCtx2⟩
    have hSu : Subst.VarsAvoid substInfo.subst ps := by
      refine Constraints.unify_varsAvoid h_unify hS3 (Constraints.freeVars_varsAvoid ?_)
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · refine ⟨hkc, ?_⟩
        intro v hv
        simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.not_mem_nil] at hv
      · rw [List.mem_singleton] at hc'
        subst hc'
        exact ⟨hkt, hke⟩
    refine ⟨h_env' ▸ hSu, ?_, ?_⟩
    · rw [h_et]
      exact hkt
    · intro S hAbs hSS
      subst h_et
      rw [h_env'] at hAbs
      have hAbs3 : Subst.absorbs S Env3.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ h_unify) hAbs
      have hAbs2 : Subst.absorbs S Env2.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ hAbs23 hAbs3
      have hc := hac S (Subst.absorbs_trans _ _ _ hAbs12 hAbs2) hSS
      have ht := hat S hAbs2 hSS
      have he := hae S hAbs3 hSS
      simp only [AnnotsAvoid, LExpr.applySubstT, LExpr.replaceMetadata] at hc ht he ⊢
      simp only [LExpr.unresolved, LExpr.fvarAnnotations, LExpr.binderAnnotations,
        List.mem_append] at hc ht he ⊢
      intro t htm
      rcases htm with ((htm | htm) | htm) | ((htm | htm) | htm)
      · exact hc t (Or.inl htm)
      · exact ht t (Or.inl htm)
      · exact he t (Or.inl htm)
      · exact hc t (Or.inr htm)
      · exact ht t (Or.inr htm)
      · exact he t (Or.inr htm)

omit [ToString T.IDMeta] [Std.ToFormat (LFunc T)] in
/-- `resolveAux` keeps the scopes below the newest one binding nothing. -/
theorem resolveAux_tailClear (C : LContext T) :
    ∀ (e : LExpr T.mono) (Env Env' : TEnv T.IDMeta) (et : LExprT T.mono),
      resolveAux C Env e = .ok (et, Env') →
      TailClear Env.stateSubstInfo.subst → TailClear Env'.stateSubstInfo.subst :=
  resolveAux_preserves C
    (fun E E' => TailClear E.stateSubstInfo.subst → TailClear E'.stateSubstInfo.subst)
    (fun _ hS => hS)
    (fun _ _ _ h12 h23 hS => h23 (h12 hS))
    (fun scheme E mty E' hinst hS =>
      (LTy_instantiateWithCheck_subst_knownInstance scheme C E mty E' hinst).1 ▸ hS)
    (fun ann E mty E' hinst hS =>
      (LMonoTy_instantiateWithCheck_subst_knownInstance ann C E mty E' hinst).1 ▸ hS)
    (fun E x fty mty E' hinfer => inferFVar_tailClear C E x fty mty E' hinfer)
    (fun E n E' hgen hS => by rw [TEnv.genTyVar_subst E n E' hgen]; exact hS)
    (fun _ _ _ hu => Constraints.unify_tailClear hu)
    (fun _ _ _ n _ hu hS => (Constraints.unify_tailClear hu hS).remove n)
    (fun E bty xv xty E1 _ hboundOk h12 hS =>
      h12 ((typeBoundVar_subst_knownInstance C E bty xv xty E1 hboundOk).1 ▸ hS))

end LExpr

section

open LExpr

variable {T : LExprParams} [Std.ToFormat T.IDMeta]

/-! ### Facts about `resolve` that do not mention annotated typing -/

/-- Resolution preserves a registered substitution range and reports a registered type when
    function arrows, Booleans, and literal types are registered. -/
theorem resolve_RangeKnown [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_bool : C.knownTypes["bool"]? = some 0)
    (h_lit : LiteralTysKnown C)
    (hS : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes ∧
    LMonoTy.knownInstance et.toLMonoTy C.knownTypes = true := by
  obtain ⟨Env0, et_aux, h_res, h_et, h_wf_init, h_ne0, h_subst0, -⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  have hS0 : Subst.RangeKnown Env0.stateSubstInfo.subst C.knownTypes := by
    rw [h_subst0]; exact hS
  obtain ⟨hS_aux, hk_aux⟩ := resolveAux_RangeKnown e et_aux C Env0 Env' h_res
    h_envwf0 h_ne0 h_fwf h_arrow h_bool h_lit hS0
  refine ⟨hS_aux, ?_⟩
  rw [← h_et, applySubstT_toLMonoTy]
  exact knownInstance_subst C.knownTypes _ _ hS_aux hk_aux

/-- If `ps` holds no generated name, resolving from an environment avoiding `ps` yields a
    substitution, type, and annotations avoiding `ps`. -/
theorem resolve_varsAvoid [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    {ps : List TyIdentifier}
    (e : LExpr T.mono) (et : LExprT T.mono) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h : e.resolve C Env = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions)
    (hgen : NoGenName ps) (hE : TEnv.VarsAvoid Env ps) :
    Subst.VarsAvoid Env'.stateSubstInfo.subst ps ∧
      (∀ v ∈ LMonoTy.freeVars et.toLMonoTy, v ∉ ps) ∧ AnnotsAvoid (LExpr.unresolved et) ps := by
  obtain ⟨Env0, et_aux, h_res, h_et, h_wf_init, h_ne0, h_subst0, h_Env0⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  have hE0 : TEnv.VarsAvoid Env0 ps := by
    refine ⟨h_subst0 ▸ hE.1, ?_⟩
    subst h_Env0
    split
    · intro v hv
      simp [TContext.knownTypeVars, TEnv.updateContext, TEnv.context, HMaps.values,
        HMap.values_empty] at hv
    · exact hE.2
  obtain ⟨hS, hk, ha⟩ :=
    resolveAux_varsAvoid e et_aux C Env0 Env' h_res h_envwf0 h_ne0 h_fwf hgen hE0
  refine ⟨hS, ?_, ?_⟩
  · rw [← h_et, applySubstT_toLMonoTy]
    exact LMonoTy.subst_varsAvoid hS hk
  · rw [← h_et]
    exact ha _ (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF) hS

/-- Every free variable of `LExpr.resolve`'s output, under any type substitution, is declared in
    the input context. -/
theorem resolve_fvar_declared [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions) (S : Subst)
    {x : T.Identifier} {ann : Option LMonoTy}
    (h_mem : (x, ann) ∈ LExpr.freeVars (LExpr.unresolved (LExpr.applySubstT et S))) :
    ∃ sch, Env.context.types.find? x = some sch := by
  obtain ⟨Env0, et_aux, h_res, h_et, h_wf_init, h_ne0, -, h_Env0⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  have h_vars : x ∈ LExpr.getVars et_aux := by
    have h_x : x ∈ LExpr.getVars (LExpr.unresolved (LExpr.applySubstT et S)) := by
      rw [getVars_eq_freeVars_idents]
      exact List.mem_map.mpr ⟨(x, ann), h_mem, rfl⟩
    rw [Proofs.getVars_unresolved, ← h_et, Proofs.getVars_applySubstT,
      Proofs.getVars_applySubstT] at h_x
    exact h_x
  have h_known := Proofs.resolveAux_getVars_mem_knownVars e et_aux C Env0 Env' h_res h_envwf0
    h_ne0 h_fwf x h_vars
  obtain ⟨sch, h_sch⟩ := (HMaps.mem_keys_iff_find? Env0.context.types x).mp h_known
  subst h_Env0
  split at h_sch
  · simp [TEnv.updateContext, TEnv.context, HMaps.find?] at h_sch
  · exact ⟨sch, h_sch⟩

/-- Every operator in `resolveAux`'s output names a function of the factory. -/
private theorem resolveAux_getOps_mem [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h_res : resolveAux C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_ne : Env.context.types ≠ []) (h_fwf : FactorySigWF C.functions) :
    ∀ o ∈ LExpr.getOps et, (C.functions[o.name]?).isSome := by
  apply resolveAux_ind
    (P := fun _ et (C : LContext T) _ _ => ∀ o ∈ LExpr.getOps et, (C.functions[o.name]?).isSome)
    (e := e) (et := et) (C := C) (Env := Env) (Env' := Env')
    (h_res := h_res) (h_envwf := h_envwf) (h_ne := h_ne) (h_fwf := h_fwf)
  case h_const =>
    intro m c et C Env Env' h_res _ _ _ o ho
    obtain ⟨-, -, rfl, -⟩ := LExpr.resolveAux_const_shape C Env Env' m c et h_res
    simp [LExpr.getOps] at ho
  case h_op =>
    intro m o oty et C Env Env' h_res _ _ _ o' ho
    obtain ⟨func, ty_o, ty, Env_x, hfunc, htype, hiwc, h_et, -⟩ :=
      LExpr.resolveAux_op_shape C Env Env' m o oty et h_res
    subst h_et
    simp only [LExpr.getOps, List.mem_singleton] at ho
    subst ho
    simp [hfunc]
  case h_fvar =>
    intro m x fty et C Env Env' h_res _ _ _ o ho
    obtain ⟨ty, Env_x, h_et⟩ := LExpr.resolveAux_fvar_shape C Env Env' m x fty et h_res
    subst h_et
    simp [LExpr.getOps] at ho
  case h_app =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 freshName EnvGen substInfo
      hRes hRes1 hRes2 hGen hUnify hEt _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 o ho
    subst hEt
    simp only [LExpr.getOps, List.mem_append] at ho
    rcases ho with ho | ho
    · exact ih1 o ho
    · exact ih2 o ho
  case h_abs =>
    intro m name annotation body et C Env Env' xv xty Env1 bodyT Env2
      hRes hBound hBody hEt hEnv' _ _ _ _ _ _ ih o ho
    subst hEt
    simp only [LExpr.getOps, Proofs.getOps_varCloseT] at ho
    exact ih o ho
  case h_quant =>
    intro m qk name bty triggers body et C Env Env' xvb xtyb Env1 et_body Env2 et_tr Env3
      substInfo hRes hBound hBody hTr _ hEt _ _ _ _ _ _ _ _ _ _ ihBody ihTr o ho
    subst hEt
    simp only [LExpr.getOps, Proofs.getOps_varCloseT, List.mem_append] at ho
    rcases ho with ho | ho
    · exact ihTr o ho
    · exact ihBody o ho
  case h_eq =>
    intro m e1 e2 et C Env Env' e1t Env1 e2t Env2 substInfo
      hRes hRes1 hRes2 hUnify hEt _ _ _ _ _ _ _ _ _ _ ih1 ih2 o ho
    subst hEt
    simp only [LExpr.getOps, List.mem_append] at ho
    rcases ho with ho | ho
    · exact ih1 o ho
    · exact ih2 o ho
  case h_ite =>
    intro m c th el et C Env Env' ct Env1 tht Env2 elt Env3 substInfo
      hRes hc ht he hUnify hEt _ _ _ _ _ _ _ _ _ _ _ _ ihc iht ihe o ho
    subst hEt
    simp only [LExpr.getOps, List.mem_append] at ho
    rcases ho with (ho | ho) | ho
    · exact ihc o ho
    · exact iht o ho
    · exact ihe o ho

/-- Every operator of `LExpr.resolve`'s output, under any type substitution, names a function of
    the factory. -/
theorem resolve_getOps_mem [ToString T.IDMeta] [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    [HasGen T.IDMeta] [Std.ToFormat (LFunc T)] [Std.ToFormat T.Metadata]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : TEnvWF Env) (h_fwf : FactorySigWF C.functions) (S : Subst) :
    ∀ o ∈ LExpr.getOps (LExpr.unresolved (LExpr.applySubstT et S)),
      (C.functions[o.name]?).isSome := by
  obtain ⟨Env0, et_aux, h_res, h_et, h_wf_init, h_ne0, -, -⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_envwf0 := h_wf_init h_envwf
  intro o ho
  rw [Proofs.getOps_unresolved, ← h_et, Proofs.getOps_applySubstT,
    Proofs.getOps_applySubstT] at ho
  exact resolveAux_getOps_mem C Env0 Env' e et_aux h_res h_envwf0 h_ne0 h_fwf o ho

/-- The resolved type is fresh for the resolver's output generator state. -/
theorem resolve_result_type_fresh [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_env : TEnvWF Env) (h_fac : FactorySigWF C.functions) :
    ∀ v, v ∈ LMonoTy.freeVars et.toLMonoTy →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen →
        v ≠ TState.tyPrefix ++ toString n := by
  obtain ⟨Env0, et0, h_res, h_et, h_wf_init, h_ne0, -, -⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_env0 := h_wf_init h_env
  have h_props := LExpr.resolveAux_properties e et0 C Env0 Env' h_res h_ne0
    h_env0.aliasesWF h_fac h_env0.substFreshForGen h_env0.ctxFreshForGen h_env0.boundVarsFresh
  obtain ⟨h_sf, h_otf⟩ := h_props.preserves
  rw [← h_et, LExpr.applySubstT_toLMonoTy]
  intro v hv n hn
  rcases List.mem_append.mp
      (LMonoTy.freeVars_of_subst_subset Env'.stateSubstInfo.subst et0.toLMonoTy hv) with
    hv_et | hv_subst
  · exact h_otf v hv_et n hn
  · exact h_sf v (Or.inr hv_subst) n hn

/-- Expression resolution absorbs the incoming substitution. -/
theorem resolve_absorbs [DecidableEq T.IDMeta] [Hashable T.IDMeta] [HasGen T.IDMeta]
    (C : LContext T) (Env Env' : TEnv T.IDMeta) (e : LExpr T.mono) (et : LExprT T.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_env : TEnvWF Env) (h_fac : FactorySigWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  obtain ⟨Env0, et0, h_res, -, h_wf_init, h_ne0, h_subst, -⟩ :=
    resolve_resolveAux_init e et C Env Env' h
  have h_env0 := h_wf_init h_env
  have h_props := LExpr.resolveAux_properties e et0 C Env0 Env' h_res h_ne0
    h_env0.aliasesWF h_fac h_env0.substFreshForGen h_env0.ctxFreshForGen h_env0.boundVarsFresh
  have h_absorbs := h_props.absorbs
  rwa [h_subst] at h_absorbs

end

end -- public section

end Lambda
