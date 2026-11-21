/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
import all Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
import all Strata.Languages.Core.Typing.Spec.TypeSpecShared
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.FactoryProps
import Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
public import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
import Strata.Languages.Core.Typing.Props.FactoryRegistrationProps
import Strata.Languages.Core.Typing.Props.ProcedureTypeProps
import Strata.Languages.Core.Typing.Props.StatementTypeProps
import Strata.Languages.Core.Typing.Props.NamesWFProps
public import Strata.Languages.Core.Typing.Spec.NamesWF
import Strata.Languages.Core.Typing.Props.FunctionTypeProps
import Strata.Languages.Core.Typing.Props.DatatypeTypeProps
import all Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec

/-! ## Properties of factory extension and declaration typing

Key theorems: `factoryExtendedBy_addFactoryFunction` and `factoryExtendedBy_foldl` (registering
functions with new names extends the context by exactly those functions), and
`DeclsHasType_transport` (declaration-list typing by the typechecker spec moves to a type scope
with the same lookups and aliases) and `DeclsWellTyped.of_find?` (the same for output typing). -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative
open Strata.Util (HMaps)

public section

/-- Adding a function whose name is new to a type context extends it by exactly that function. -/
theorem factoryExtendedBy_addFactoryFunction (C : Expression.TyContext) (f : LFunc CoreLParams)
    (hfresh : f.name.name ∉ C.functions) :
    FactoryExtendedBy (fun f g => g = f) C (C.addFactoryFunction f) [f] := by
  unfold LContext.addFactoryFunction
  rw [dite_eq_right hfresh]
  refine { knownTypes_eq := rfl, datatypes_eq := rfl, idents_eq := rfl, rigidTypeVars_eq := rfl,
           preserves_old := ?_, contains_new := ?_, no_other := ?_ }
  · intro nm g h
    have hne : nm ≠ f.name.name := by
      intro heq
      exact hfresh (heq ▸ Factory.getElem?_some_implies_mem h)
    show (C.functions.push f hfresh)[nm]? = some g
    rw [Factory.push_mem_match, ite_eq_right hne]
    exact h
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    refine ⟨f, ?_, rfl⟩
    show (C.functions.push f hfresh)[f.name.name]? = some f
    rw [Factory.push_mem_match, ite_eq_left rfl]
  · intro nm h
    rcases (Factory.push_mem_iff C.functions f hfresh nm).mp h with heq | hmem
    · exact Or.inr (by simp [heq])
    · exact Or.inl hmem

/-- Folding the registration of functions with distinct names, all new to `C`, extends `C` by
    exactly those functions. -/
theorem factoryExtendedBy_foldl (C : Expression.TyContext) (l : List α)
    (g : α → LFunc CoreLParams) (hnodup : (l.map fun a => (g a).name.name).Nodup)
    (hfresh : ∀ a ∈ l, (g a).name.name ∉ C.functions) :
    FactoryExtendedBy (fun f e => e = f) C
      (l.foldl (fun C a => C.addFactoryFunction (g a)) C) (l.map g) := by
  induction l generalizing C with
  | nil =>
    refine { knownTypes_eq := rfl, datatypes_eq := rfl, idents_eq := rfl,
             rigidTypeVars_eq := rfl, preserves_old := fun _ _ h => h, contains_new := ?_,
             no_other := fun _ h => Or.inl h }
    intro x hx
    simp at hx
  | cons a t IH =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.foldl_cons, List.map_cons]
    have hstep := factoryExtendedBy_addFactoryFunction C (g a) (hfresh a List.mem_cons_self)
    have hfresh' : ∀ b ∈ t, (g b).name.name ∉ (C.addFactoryFunction (g a)).functions := by
      intro b hb hmem
      rcases hstep.no_other _ hmem with hC | hnew
      · exact hfresh b (List.mem_cons_of_mem a hb) hC
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hnew
        exact hnodup.1 (List.mem_map.mpr ⟨b, hb, hnew⟩)
    have hcomp := factoryExtendedBy_append hstep
      (IH (C.addFactoryFunction (g a)) hnodup.2 hfresh')
    simpa using hcomp

/-- Extension by exactly `entries` is extension by `newFuncs` under `agrees` when both have the
    same names and each new function agrees with its entry. -/
theorem FactoryExtendedBy.of_entries {agrees : LFunc CoreLParams → LFunc CoreLParams → Prop}
    {C C' : Expression.TyContext} {entries newFuncs : List (LFunc CoreLParams)}
    (h : FactoryExtendedBy (fun f e => e = f) C C' entries)
    (hnames : entries.map (·.name.name) = newFuncs.map (·.name.name))
    (hagree : ∀ f ∈ newFuncs, ∃ e ∈ entries, e.name.name = f.name.name ∧ agrees f e) :
    FactoryExtendedBy agrees C C' newFuncs := by
  refine { knownTypes_eq := h.knownTypes_eq, datatypes_eq := h.datatypes_eq,
           idents_eq := h.idents_eq, rigidTypeVars_eq := h.rigidTypeVars_eq,
           preserves_old := h.preserves_old, contains_new := ?_, no_other := ?_ }
  · intro f hf
    obtain ⟨e, he, hname, hagreeFE⟩ := hagree f hf
    obtain ⟨g, hg, hge⟩ := h.contains_new e he
    rw [hname, hge] at hg
    exact ⟨e, hg, hagreeFE⟩
  · intro nm hnm
    rcases h.no_other nm hnm with hC | hl
    · exact Or.inl hC
    · exact Or.inr (hnames ▸ hl)

/-- A renaming of a lemma's type parameters for one context is one for any context with the same
    rigid type variables and the same variable lookups. -/
theorem LemmaAlphaVariant.congr {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit}
    {l l' : Lemma} (hrigid : C'.rigidTypeVars = C.rigidTypeVars)
    (hscope : TContext.FindEq (T := CoreLParams) Γ' Γ) (h : LemmaAlphaVariant C Γ l l') :
    LemmaAlphaVariant C' Γ' l l' := by
  obtain ⟨ren, hren, rfl⟩ := h
  exact ⟨ren, TyArgRenaming.congr hrigid hscope hren, rfl⟩

/-- Declaration typing by the typechecker spec transfers to a type scope with the same lookups
    and aliases, with an output scope of the same lookups and aliases. -/
private theorem DeclHasType_transport {P : Program}
    {C C' : Expression.TyContext} {Γ Ξ Γ' : TContext Unit} {d : Decl}
    (hR : TContext.FindEq (T := CoreLParams) Ξ Γ)
    (h : DeclHasType P C Γ d C' Γ') :
    ∃ Ξ', DeclHasType P C Ξ d C' Ξ' ∧ TContext.FindEq (T := CoreLParams) Ξ' Γ' := by
  cases h
  case type_con =>
    rename_i tc md hadd
    exact ⟨Ξ, .type_con C C' Ξ tc md hadd, hR⟩
  case type_syn =>
    rename_i ts md hok
    obtain ⟨storedTy, hok⟩ := hok
    obtain ⟨hok', hR'⟩ := InputSynonymOk.of_findEq hR hok
    exact ⟨_, .type_syn C Ξ ts md _ ⟨storedTy, hok'⟩, hR'⟩
  case type_data =>
    rename_i block md block_r hcompat hadd
    exact ⟨Ξ, .type_data C C' Ξ block md block_r
      (MutualBlockTyCompat.of_aliasEquiv (fun _ _ hc => hR.aliases ▸ hc) hcompat) hadd, hR⟩
  case ax =>
    rename_i ax md hscoped hty hannots
    exact ⟨Ξ, .ax C Ξ ax md (HasType_FindEq C _ _ ax.e _ hR hty)
      (writtenAnnotsOk_of_aliases_eq hR.aliases hannots) hscoped, hR⟩
  case lemma =>
    rename_i l l' md hnodup hallowed hscoped hv hty hannots
    exact ⟨Ξ, .lemma C Ξ l l' md (hv.congr rfl hR) (HasType_FindEq C _ _ l'.e _ hR hty)
      (writtenAnnotsOk_of_aliases_eq hR.aliases hannots) hnodup hallowed hscoped, hR⟩
  case distinct =>
    rename_i l es md hlen hscoped hall hannots
    obtain ⟨mty, hall⟩ := hall
    exact ⟨Ξ, .distinct C Ξ l es md hlen
      ⟨mty, fun e he => HasType_FindEq C _ _ e _ hR (hall e he)⟩
      (fun e he => writtenAnnotsOk_of_aliases_eq hR.aliases (hannots e he)) hscoped, hR⟩
  case proc =>
    rename_i proc md hp
    obtain ⟨proc', hv, hproc⟩ := hp
    exact ⟨Ξ, .proc C Ξ proc md ⟨proc', hv.congr rfl hR, ProcHasTypeExact_transport hR hproc⟩, hR⟩
  case func =>
    rename_i func f' md hnr hnew hv hfunc hext
    exact ⟨Ξ, .func C C' Ξ func f' md hnr hnew (hv.congr rfl hR)
      (FuncHasTypeExact_transport hR hfunc)
      (hext.mono fun _ _ => FuncEntryOk.of_aliases_eq hR.aliases), hR⟩
  case recFuncBlock =>
    rename_i Cstub funcs funcs' md stubs fullFuncs hne hnew hnoinline hstubs hfull hrec hvars
      hextStub hall hextFull
    exact ⟨Ξ, .recFuncBlock C Cstub C' Ξ funcs funcs' md stubs fullFuncs hne hnew hnoinline
      (List.Rel₂.imp (fun _ _ hv => FuncAlphaVariant.congr rfl hR hv) hvars) hstubs hfull
      (hextStub.mono fun _ _ => FuncEntryOk.of_aliases_eq hR.aliases)
      (hextFull.mono fun _ _ => FuncEntryOk.of_aliases_eq hR.aliases)
      (fun f hf => FuncHasTypeExact_transport hR (hall f hf)) hrec, hR⟩

/-- `DeclsHasType` transfers to a type scope with the same lookups and aliases, with an output
    scope of the same lookups and aliases. -/
theorem DeclsHasType_transport {P : Program}
    {C C' : Expression.TyContext} {Γ Ξ Γ' : TContext Unit} {ds : List Decl}
    (hR : TContext.FindEq (T := CoreLParams) Ξ Γ)
    (h : DeclsHasType P C Γ ds C' Γ') :
    ∃ Ξ', DeclsHasType P C Ξ ds C' Ξ' ∧ TContext.FindEq (T := CoreLParams) Ξ' Γ' := by
  induction h generalizing Ξ with
  | nil C0 Γ0 => exact ⟨Ξ, .nil _ _, hR⟩
  | cons C0 C1 C2 Γ0 Γ1 Γ2 d ds hd _ IH =>
    obtain ⟨Ξ1, hd', hR1⟩ := DeclHasType_transport hR hd
    obtain ⟨Ξ2, hds', hR2⟩ := IH hR1
    exact ⟨Ξ2, .cons _ _ _ _ _ _ _ _ hd' hds', hR2⟩

/-- The functions in scope after a well-typed declaration are functions of its output table, when
    the scope before it consisted of functions of its input table. -/
theorem DeclWellTyped.extendScope_subset {P : Program} {C C' : LContext CoreLParams}
    {ts : TypeScopes} {d : Decl} {fns : String → Prop} (hfns : ∀ n, fns n → n ∈ C.functions)
    (h : DeclWellTyped P C ts d C') :
    ∀ n, d.extendScope fns n → n ∈ C'.functions := by
  refine And.elim (Decl.extendScope_subset hfns) ?_
  match h with
  | .type_con _ _ _ _ _ hadd =>
    exact ⟨fun _ hn => (addKnownTypeWithError_functions_eq _ _ _ _ hadd) ▸ hn, nofun⟩
  | .type_syn .. => exact ⟨fun _ hn => hn, nofun⟩
  | .type_data _ _ _ _ _ hadd =>
    refine ⟨fun n hn => addMutualBlock_mem_functions hadd n (.inl hn), fun n hn => ?_⟩
    simp only [Decl.funcNames, List.map_map] at hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    exact addMutualBlock_mem_functions hadd _ (.inr hm)
  | .ax .. => exact ⟨fun _ hn => hn, nofun⟩
  | .lemma .. => exact ⟨fun _ hn => hn, nofun⟩
  | .distinct .. => exact ⟨fun _ hn => hn, nofun⟩
  | .proc .. => exact ⟨fun _ hn => hn, nofun⟩
  | .func _ _ _ _ _ _ _ _ hext =>
    refine ⟨fun _ hn => hext.mem_old hn, fun n hn => ?_⟩
    simp only [Decl.funcNames, List.map_cons, List.map_nil, List.mem_singleton] at hn
    subst hn
    exact hext.mem_new (List.mem_singleton_self _)
  | .recFuncBlock _ _ _ _ _ _ _ _ _ _ _ _ hfull _ hext _ _ =>
    refine ⟨fun _ hn => hext.mem_old hn, fun n hn => ?_⟩
    simp only [Decl.funcNames, List.map_map] at hn
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
    subst hfull
    exact hext.mem_new (List.mem_map_of_mem hf)

/-- A well-typed function stays well typed from variable scopes with the same lookups. -/
theorem FuncWellTyped.of_find? {C : LContext CoreLParams} {ts ts' : TypeScopes}
    {func : Function} (hfind : ∀ y, ts'.find? y = ts.find? y) (h : FuncWellTyped C ts func) :
    FuncWellTyped C ts' func := by
  have hf : ∀ y, (funcScopes ts' func).find? y = (funcScopes ts func).find? y :=
    HMaps.find?_push_congr hfind _
  refine
    { inputsNodup := h.inputsNodup
      typeArgsNodup := h.typeArgsNodup
      noUndeclaredVars := h.noUndeclaredVars
      typeArgsInSignature := h.typeArgsInSignature
      signatureWellKinded := h.signatureWellKinded
      bodyTyped := fun body hb => (h.bodyTyped body hb).of_find? hf
      measureOnlyRecursive := h.measureOnlyRecursive
      measureTyped := ?_
      preconditionsTyped := fun p hp => (h.preconditionsTyped p hp).of_find? hf
      axiomsTyped := fun ax hax => (h.axiomsTyped ax hax).of_find? hf
      annotsScoped := h.annotsScoped
      constrNoBody := h.constrNoBody }
  intro m hm
  have hmt := h.measureTyped m hm
  cases m
  case fvar =>
    obtain ⟨ty, hty, hint | ⟨n, args, hc, hdt, ht⟩⟩ := hmt
    · exact ⟨ty, hty, .inl (hint.of_find? hf)⟩
    · exact ⟨ty, hty, .inr ⟨n, args, hc, hdt, ht.of_find? hf⟩⟩
  all_goals exact hmt.of_find? hf

/-- A well-typed procedure body stays well typed from variable scopes with the same lookups. -/
theorem ProcBodyWellTyped.of_find? {P : Program} {C : LContext CoreLParams}
    {ts ts' : TypeScopes} {body : Procedure.Body} (hfind : ∀ y, ts'.find? y = ts.find? y)
    (h : ProcBodyWellTyped P C ts body) : ProcBodyWellTyped P C ts' body := by
  cases h with
  | structured ss C' tsOut o hss =>
    obtain ⟨tsOut', hss', -⟩ := StatementsWellTyped.of_findEq hss hfind
    exact .structured ss C' tsOut' o hss'
  | cfg c o => exact .cfg c o
  | abstract => exact .abstract

/-- A well-typed procedure stays well typed from variable scopes with the same lookups. -/
theorem ProcWellTyped.of_find? {P : Program} {C : LContext CoreLParams}
    {ts ts' : TypeScopes} {proc : Procedure} (hfind : ∀ y, ts'.find? y = ts.find? y)
    (h : ProcWellTyped P C ts proc) : ProcWellTyped P C ts' proc := by
  have hin : ∀ y, (procInputScopes ts' proc).find? y = (procInputScopes ts proc).find? y :=
    HMaps.find?_push_congr hfind _
  have hbody : ∀ y, (procBodyScopes ts' proc).find? y = (procBodyScopes ts proc).find? y :=
    HMaps.find?_push_congr hfind _
  refine
    { inputsNodup := h.inputsNodup
      outputsNodup := h.outputsNodup
      oldNamesFresh := h.oldNamesFresh
      typeArgsNodup := h.typeArgsNodup
      noUndeclaredVars := h.noUndeclaredVars
      declTyVarsBound := h.declTyVarsBound
      signatureWellKinded := h.signatureWellKinded
      modRights := h.modRights
      preconditionsTyped := fun c hc => (h.preconditionsTyped c hc).of_find? hin
      postconditionsTyped := fun c hc => (h.postconditionsTyped c hc).of_find? hbody
      bodyTyped := ?_ }
  exact ProcBodyWellTyped.of_find? hbody h.bodyTyped

/-- A well-typed declaration stays well typed from variable scopes with the same lookups. -/
theorem DeclWellTyped.of_find? {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {d : Decl} (hfind : ∀ y, ts'.find? y = ts.find? y)
    (h : DeclWellTyped P C ts d C') : DeclWellTyped P C ts' d C' :=
  match h with
  | .type_con _ _ _ _ _ hadd => .type_con _ _ _ _ _ hadd
  | .type_syn _ _ _ _ hwf hnr hty => .type_syn _ _ _ _ hwf hnr hty
  | .type_data _ _ _ _ _ hadd => .type_data _ _ _ _ _ hadd
  | .ax _ _ _ _ hty hsc => .ax _ _ _ _ (hty.of_find? hfind) hsc
  | .lemma _ _ _ _ hty hnd hsc => .lemma _ _ _ _ (hty.of_find? hfind) hnd hsc
  | .distinct _ _ _ _ _ hlen ⟨mty, hty⟩ hsc =>
    .distinct _ _ _ _ _ hlen ⟨mty, fun e he => (hty e he).of_find? hfind⟩ hsc
  | .proc _ _ _ _ hp => .proc _ _ _ _ (hp.of_find? hfind)
  | .func _ _ _ _ _ hnr hfresh hf hext => .func _ _ _ _ _ hnr hfresh (hf.of_find? hfind) hext
  | .recFuncBlock _ _ _ _ _ _ _ _ hne hfresh hinl hstubs hfull hextS hext hfs hrec =>
    .recFuncBlock _ _ _ _ _ _ _ _ hne hfresh hinl hstubs hfull hextS hext
      (fun f hf => (hfs f hf).of_find? hfind) hrec

/-- A well-typed declaration list stays well typed from variable scopes with the same
    lookups. -/
theorem DeclsWellTyped.of_find? {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {ds : List Decl} (hfind : ∀ y, ts'.find? y = ts.find? y)
    (h : DeclsWellTyped P C ts ds C') : DeclsWellTyped P C ts' ds C' := by
  induction h with
  | nil => exact .nil _ _
  | cons _ _ _ _ _ _ hd _ ih => exact .cons _ _ _ _ _ _ (hd.of_find? hfind) (ih hfind)

end -- public section

end TypeSpec

end Core
