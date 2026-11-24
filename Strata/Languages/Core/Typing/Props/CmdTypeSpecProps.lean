/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
public import Strata.Languages.Core.Typing.Spec.CommandTypeSpec
public import Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
public import Strata.Languages.Core.Typing.Props.TypingSpecProps
public import Strata.DL.Lambda.LExprTypeSpecProps
import all Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.Denote.Assumptions
import Strata.DL.Lambda.Denote.LExprAnnotatedProps
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LExprTProps
import Strata.DL.Lambda.LExprTypeEnv
import all Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import all Strata.Languages.Core.Typing.Spec.ProgramTypeSpec

/-! # Properties of the command typechecker spec

Key theorems: `instAnnots_none` (reading through the environment binding no written type
variable changes nothing), `CmdExtHasType_transport`, `ScopesAnnotAgree.of_find?`, and
`CmdExtHasType_MonoScope`. -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- The written-annotation requirement depends on the scope only through its aliases. -/
theorem writtenAnnotsOk_of_aliases_eq {C : LContext CoreLParams} {Γ Ξ : TContext Unit}
    {e : Expression.Expr} (h_al : Ξ.aliases = Γ.aliases) (h : WrittenAnnotsOk C Γ e) :
    WrittenAnnotsOk C Ξ e := by
  obtain ⟨hfvar, hbinder⟩ := h
  refine ⟨?_, hbinder⟩
  change FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid Ξ.aliases e
  rw [h_al]
  exact hfvar

/-- Naming no alias of a type scope depends on the scope only through its aliases. -/
theorem nameNotAlias_of_aliases_eq {Γ Ξ : TContext Unit} {n : String}
    (h_al : Ξ.aliases = Γ.aliases) (h : ∀ al ∈ Γ.aliases, al.name ≠ n) :
    ∀ al ∈ Ξ.aliases, al.name ≠ n := by
  rw [h_al]
  exact h

/-- The conditions on a type synonym hold in a type scope with the same lookups and aliases,
    with an output scope of the same lookups and aliases. -/
theorem InputSynonymOk.of_findEq {C : LContext CoreLParams} {Γ Ξ Γ' : TContext Unit}
    {a : TypeAlias} {storedTy : LMonoTy} (hEq : TContext.FindEq (T := CoreLParams) Ξ Γ)
    (h : InputSynonymOk C Γ a storedTy Γ') :
    InputSynonymOk C Ξ a storedTy { Ξ with aliases := { a with type := storedTy } :: Ξ.aliases }
      ∧ TContext.FindEq (T := CoreLParams)
        { Ξ with aliases := { a with type := storedTy } :: Ξ.aliases } Γ' := by
  have hal : Ξ.aliases = Γ.aliases := hEq.2
  refine ⟨⟨h.wf, h.nameUnregistered, ?_, ?_, ?_, rfl⟩, ?_⟩
  · rw [hal]; exact h.nameFresh
  · rw [hal]; exact h.bodyTyped
  · rw [hal]; exact h.storedAliasFree
  · rw [h.scope]
    exact ⟨fun k => hEq.find? k, by rw [hal]⟩

/-- Agreement of a factory entry with its declared function depends on the type scope only
    through its aliases. -/
theorem FuncEntryOk.of_aliases_eq {Γ Ξ : TContext Unit} {f g : LFunc CoreLParams}
    (h_al : Ξ.aliases = Γ.aliases) (h : FuncEntryOk Γ f g) : FuncEntryOk Ξ f g := by
  unfold FuncEntryOk
  rw [h_al]
  exact h

/-- A valid source type stays valid when only the identifier registry changes. -/
theorem validSourceTy_idents_irrel {C : Expression.TyContext} {j : Identifiers Unit}
    {adm : TyVarAdmissibility} {aliases : List TypeAlias} {t : LMonoTy}
    (h : ∃ r, SourceTyWF { C with idents := j } adm aliases t r) :
    ∃ r, SourceTyWF C adm aliases t r :=
  h.imp fun _ hr => SourceTyWF.of_knownTypes_eq (C := { C with idents := j }) rfl hr

/-- The written-annotation requirement ignores the identifier registry. -/
theorem writtenAnnotsOk_idents_irrel (C : Expression.TyContext) (j : Identifiers Unit)
    (Γ : TContext Unit) (e : Expression.Expr) (h : WrittenAnnotsOk { C with idents := j } Γ e) :
    WrittenAnnotsOk C Γ e :=
  ⟨fun t ht => validSourceTy_idents_irrel (h.1 t ht), h.2⟩

/-- Reading an annotation through the environment binding no written type variable leaves it
    unchanged. -/
private theorem instAnnotTy_none (t : LMonoTy) : instAnnotTy (fun _ => none) t = t := by
  have hread : ∀ v, readTyVar (fun _ => none) v = .ftvar v := by
    intro v
    simp only [readTyVar, Option.getD_none, ite_self]
  have hpoint : ∀ v ∈ LMonoTy.freeVars t,
      LMonoTy.subst [] (LMonoTy.subst [restrictTo (readTyVar (fun _ => none)) t] (.ftvar v)) =
        LMonoTy.subst [] (.ftvar v) := by
    intro v hv
    have hfind : (Strata.Util.HMaps.find? [restrictTo (readTyVar (fun _ => none)) t] v) =
        some (readTyVar (fun _ => none) v) := by
      rw [Strata.Util.HMaps.find?_single_scope]
      exact LExpr.find?_buildSubstFromFunction _ _ v hv
    rw [LMonoTy.subst_ftvar_of_some hfind, hread v]
  have hagree := LMonoTy.subst_subst_of_pointwise _ [] [] t hpoint
  rw [LMonoTy.subst_nil, LMonoTy.subst_nil] at hagree
  exact hagree

/-- Reading an expression through the environment binding no written type variable leaves it
    unchanged. -/
theorem instAnnots_none : ∀ e : Expression.Expr, instAnnots (fun _ => none) e = e
  | .const _ _ => rfl
  | .op _ _ _ => rfl
  | .bvar _ _ => rfl
  | .fvar _ _ ty => by cases ty <;> simp only [instAnnots, Option.map, instAnnotTy_none]
  | .abs _ _ ty b => by
    cases ty <;> simp only [instAnnots, Option.map, instAnnotTy_none, instAnnots_none b]
  | .quant _ _ _ ty tr b => by
    cases ty <;>
      simp only [instAnnots, Option.map, instAnnotTy_none, instAnnots_none tr, instAnnots_none b]
  | .app _ f a => by simp only [instAnnots, instAnnots_none f, instAnnots_none a]
  | .ite _ c t f => by
    simp only [instAnnots, instAnnots_none c, instAnnots_none t, instAnnots_none f]
  | .eq _ a b => by simp only [instAnnots, instAnnots_none a, instAnnots_none b]

/-! ### Annotation agreement -/

/-- Annotation agreement depends on the context only through its function table. -/
theorem ScopesAnnotAgree.of_functions_eq {C C' : Expression.TyContext} {ts : TypeScopes}
    {e : Expression.Expr} (h : C'.functions = C.functions) (ha : ScopesAnnotAgree C ts e) :
    ScopesAnnotAgree C' ts e := by
  refine ⟨ha.fvarsDeclared, ?_, ?_⟩
  · rw [h]
    exact ha.opsInstantiate
  · rw [h]
    exact ha.opsKnown

/-- Annotation agreement transports to a type scope with the same variable lookups. -/
theorem ScopesAnnotAgree.of_find? {C : Expression.TyContext} {Γ Ξ : TContext Unit}
    {e : Expression.Expr} (hfind : ∀ x, Ξ.types.find? x = Γ.types.find? x)
    (ha : ScopesAnnotAgree C Γ.types e) : ScopesAnnotAgree C Ξ.types e := by
  refine ⟨fun x ann hx => ?_, ha.opsInstantiate, ha.opsKnown⟩
  rw [hfind x]
  exact ha.fvarsDeclared x ann hx

/-- Well-typedness of an expression depends on the variable scopes only through their lookups. -/
theorem ExprWellTyped.of_find? {C : LContext CoreLParams} {ts ts' : TypeScopes}
    {e : Expression.Expr} {mty : LMonoTy} (hfind : ∀ x, ts'.find? x = ts.find? x)
    (h : ExprWellTyped C ts e mty) : ExprWellTyped C ts' e mty :=
  ⟨h.1, h.2.1, ScopesAnnotAgree.of_find? (Γ := { types := ts }) (Ξ := { types := ts' }) hfind
    h.2.2⟩

/-- Annotation agreement depends on an expression only through its annotated free variables, its
    operator annotations and its operators. -/
private theorem ScopesAnnotAgree.of_annots_eq {C : Expression.TyContext} {ts : TypeScopes}
    {e e' : Expression.Expr} (hfv : LExpr.freeVars e' = LExpr.freeVars e)
    (hop : LExpr.opAnnots e' = LExpr.opAnnots e) (hops : LExpr.getOps e' = LExpr.getOps e)
    (ha : ScopesAnnotAgree C ts e) : ScopesAnnotAgree C ts e' := by
  refine ⟨fun x ann hx => ?_, fun o ty ho => ?_, fun o ho => ?_⟩
  · rw [hfv] at hx
    exact ha.fvarsDeclared x ann hx
  · rw [hop] at ho
    exact ha.opsInstantiate o ty ho
  · rw [hops] at ho
    exact ha.opsKnown o ho

/-- Substituting into the annotations of a typed expression's `LExpr` form agrees wherever the
    `LExpr` form of the substituted typed expression does. -/
theorem ScopesAnnotAgree.applyTypeSubst_unresolved {C : Expression.TyContext} {ts : TypeScopes}
    (et : LExprT CoreLParams.mono) (S : Subst)
    (ha : ScopesAnnotAgree C ts (LExpr.unresolved (LExpr.applySubstT et S))) :
    ScopesAnnotAgree C ts (LExpr.applyTypeSubst (LExpr.unresolved et) S) := by
  refine ScopesAnnotAgree.of_annots_eq ?_ ?_ ?_ ha
  · rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType, LExpr.freeVars_replaceUserProvidedType,
      LExpr.Proofs.freeVars_unresolved_applySubstT]
  · rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType, LExpr.opAnnots_replaceUserProvidedType,
      LExpr.Proofs.opAnnots_unresolved_applySubstT]
  · rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType, LExpr.getOps_replaceUserProvidedType,
      LExpr.Proofs.getOps_unresolved, LExpr.Proofs.getOps_unresolved,
      LExpr.Proofs.getOps_applySubstT]

/-! ### Transporting command typing -/

/-- Command typing by the typechecker spec with written type variables transfers to a type
    scope with the same lookups and aliases, with an output scope of the same lookups and
    aliases. -/
private theorem CmdHasType_transport {C : LContext CoreLParams}
    {Γ Ξ Γ' : TContext Unit} {Δ Δ' : WrittenEnv} {c : Cmd Expression}
    (hR : TContext.FindEq (T := CoreLParams) Ξ Γ) (h : CmdHasType C Δ Γ c Γ' Δ') :
    ∃ Ξ', CmdHasType C Δ Ξ c Ξ' Δ' ∧ TContext.FindEq (T := CoreLParams) Ξ' Γ' := by
  cases h with
  | init_det x xty e mty mty₀ σ md _ hfind hfun hfv hxty hdecl hwk hexpr hann hsc hEqv =>
    exact ⟨_, .init_det _ _ x xty e mty mty₀ σ md _ ((hR.find? x).trans hfind) hfun
      hfv hxty (hR.aliases ▸ hdecl) hwk (HasType_FindEq C _ _ _ _ hR hexpr)
      (writtenAnnotsOk_of_aliases_eq hR.aliases hann) hsc (TContext.Equiv.refl _),
      (hR.insert x _).trans hEqv.toFindEq.symm⟩
  | init_nondet x xty mty mty₀ σ md _ hfind hfun hxty hdecl hwk hEqv =>
    exact ⟨_, .init_nondet _ _ x xty mty mty₀ σ md _ ((hR.find? x).trans hfind)
      hfun hxty (hR.aliases ▸ hdecl) hwk (TContext.Equiv.refl _),
      (hR.insert x _).trans hEqv.toFindEq.symm⟩
  | set_det x mty e md Γo hfind hexpr hann hsc hEqv =>
    exact ⟨Ξ, .set_det _ Ξ x mty e md Ξ ((hR.find? x).trans hfind)
      (HasType_FindEq C _ _ _ _ hR hexpr) (writtenAnnotsOk_of_aliases_eq hR.aliases hann) hsc
      (TContext.Equiv.refl _), hR.trans hEqv.toFindEq.symm⟩
  | set_nondet x mty md Γo hfind hEqv =>
    exact ⟨Ξ, .set_nondet _ Ξ x mty md Ξ ((hR.find? x).trans hfind)
      (TContext.Equiv.refl _), hR.trans hEqv.toFindEq.symm⟩
  | assert l e md Γo hexpr hann hsc hEqv =>
    exact ⟨Ξ, .assert _ Ξ l e md Ξ (HasType_FindEq C _ _ _ _ hR hexpr)
      (writtenAnnotsOk_of_aliases_eq hR.aliases hann) hsc (TContext.Equiv.refl _),
      hR.trans hEqv.toFindEq.symm⟩
  | assume l e md Γo hexpr hann hsc hEqv =>
    exact ⟨Ξ, .assume _ Ξ l e md Ξ (HasType_FindEq C _ _ _ _ hR hexpr)
      (writtenAnnotsOk_of_aliases_eq hR.aliases hann) hsc (TContext.Equiv.refl _),
      hR.trans hEqv.toFindEq.symm⟩
  | cover l e md Γo hexpr hann hsc hEqv =>
    exact ⟨Ξ, .cover _ Ξ l e md Ξ (HasType_FindEq C _ _ _ _ hR hexpr)
      (writtenAnnotsOk_of_aliases_eq hR.aliases hann) hsc (TContext.Equiv.refl _),
      hR.trans hEqv.toFindEq.symm⟩

/-- Extended-command typing by the typechecker spec with written type variables transfers to a
    type scope with the same lookups and aliases, with an output scope of the same lookups and
    aliases. -/
theorem CmdExtHasType_transport {C : LContext CoreLParams}
    {P : Program} {Γ Ξ Γ' : TContext Unit} {Δ Δ' : WrittenEnv} {c : Command}
    (hR : TContext.FindEq (T := CoreLParams) Ξ Γ) (h : CmdExtHasType C P Δ Γ c Γ' Δ') :
    ∃ Ξ', CmdExtHasType C P Δ Ξ c Ξ' Δ' ∧ TContext.FindEq (T := CoreLParams) Ξ' Γ' := by
  cases h with
  | cmd _ _ _ hc =>
    obtain ⟨Ξ', hc', hR'⟩ := CmdHasType_transport hR hc
    exact ⟨Ξ', .cmd _ _ _ _ _ hc', hR'⟩
  | call pname tyArgs callArgs proc md σ Γo hpf hwf hlhs hinp hann hsc hout hEqv =>
    refine ⟨Ξ, .call _ Ξ pname tyArgs callArgs proc md σ Ξ hpf hwf ?_ ?_
      (fun e he => writtenAnnotsOk_of_aliases_eq hR.aliases (hann e he)) hsc ?_
      (TContext.Equiv.refl _), hR.trans hEqv.toFindEq.symm⟩
    · intro v hv
      rw [hR.find? v]
      exact hlhs v hv
    · intro i hi hj
      obtain ⟨mty, hc, hmatch⟩ := hinp i hi hj
      refine ⟨mty, hR.aliases ▸ hc, ?_⟩
      revert hmatch
      split
      · intro hmatch
        rw [hR.find? _]
        exact hmatch
      · exact HasType_FindEq C _ _ _ _ hR
    · intro i hi hj
      obtain ⟨mty, hc, hfind⟩ := hout i hi hj
      exact ⟨mty, hR.aliases ▸ hc, (hR.find? _).trans hfind⟩

/-- `CmdExtHasType` is invariant under changing the context's `idents` field. -/
theorem CmdExtHasType_idents_irrel (C : Expression.TyContext) (P : Program)
    (j : Identifiers Unit) (Γ : TContext Unit) (c : Command) (Γ' : TContext Unit)
    {Δ Δ' : WrittenEnv} (h : CmdExtHasType { C with idents := j } P Δ Γ c Γ' Δ') :
    CmdExtHasType C P Δ Γ c Γ' Δ' := by
  cases h with
  | call pname tyArgs callArgs proc md σ Γ' hpf hwf hlhs hinp hann hsc hout hEqv =>
    refine .call _ Γ pname tyArgs callArgs proc md σ Γ' hpf hwf hlhs ?_
      (fun e he => writtenAnnotsOk_idents_irrel C j Γ e (hann e he)) hsc hout hEqv
    intro i hi hj
    obtain ⟨mty, halias, hmatch⟩ := hinp i hi hj
    refine ⟨mty, halias, ?_⟩
    revert hmatch
    split
    · intro hmatch; exact hmatch
    · intro hmatch; exact HasType_idents_irrel C j Γ _ _ hmatch
  | cmd =>
    rename_i hcc
    cases hcc with
    | init_det x _ e mty _ _ _ _ hfind hfun hfv hxty hdecl hwk hexpr hann hsc hEqv =>
      exact .cmd _ _ _ _ _ (.init_det _ _ _ _ _ _ _ _ _ _ hfind hfun hfv hxty
        ⟨hdecl.1, validSourceTy_idents_irrel hdecl.2⟩
        (LContext.WellKindedTy_setIdents C j mty ▸ hwk)
        (HasType_idents_irrel C j Γ _ _ hexpr)
        (writtenAnnotsOk_idents_irrel C j Γ e hann) hsc hEqv)
    | init_nondet x _ mty _ _ _ _ hfind hfun hxty hdecl hwk hEqv =>
      exact .cmd _ _ _ _ _ (.init_nondet _ _ _ _ _ _ _ _ _ hfind hfun hxty
        ⟨hdecl.1, validSourceTy_idents_irrel hdecl.2⟩
        (LContext.WellKindedTy_setIdents C j mty ▸ hwk) hEqv)
    | set_det x mty e md Γ' hfind hexpr hann hsc hEqv =>
      exact .cmd _ _ _ _ _ (.set_det _ Γ x mty e md Γ' hfind
        (HasType_idents_irrel C j Γ _ _ hexpr)
        (writtenAnnotsOk_idents_irrel C j Γ e hann) hsc hEqv)
    | set_nondet x mty md Γ' hfind hEqv =>
      exact .cmd _ _ _ _ _ (.set_nondet _ Γ x mty md Γ' hfind hEqv)
    | assert l e md Γ' hexpr hann hsc hEqv =>
      exact .cmd _ _ _ _ _ (.assert _ Γ l e md Γ'
        (HasType_idents_irrel C j Γ _ _ hexpr)
        (writtenAnnotsOk_idents_irrel C j Γ e hann) hsc hEqv)
    | assume l e md Γ' hexpr hann hsc hEqv =>
      exact .cmd _ _ _ _ _ (.assume _ Γ l e md Γ'
        (HasType_idents_irrel C j Γ _ _ hexpr)
        (writtenAnnotsOk_idents_irrel C j Γ e hann) hsc hEqv)
    | cover l e md Γ' hexpr hann hsc hEqv =>
      exact .cmd _ _ _ _ _ (.cover _ Γ l e md Γ'
        (HasType_idents_irrel C j Γ _ _ hexpr)
        (writtenAnnotsOk_idents_irrel C j Γ e hann) hsc hEqv)

/-- Typing a command by the typechecker spec over a monotype-only scope yields a monotype-only
    scope. -/
private theorem CmdHasType_MonoScope {C : LContext CoreLParams} {Δ Δ' : WrittenEnv}
    {Γ Γ' : TContext Unit} {c : Cmd Expression}
    (h : CmdHasType C Δ Γ c Γ' Δ') (h_mono : MonoScope (IDMeta := Unit) Γ) :
    MonoScope (IDMeta := Unit) Γ' := by
  cases h with
  | init_det x _ _ mty _ _ _ _ _ _ _ _ _ _ _ _ _ hEqv =>
    exact MonoScope_of_findEq hEqv.toFindEq
      (MonoScope.insert h_mono (z := x) (tz := .forAll [] mty) rfl)
  | init_nondet x _ mty _ _ _ _ _ _ _ _ _ hEqv =>
    exact MonoScope_of_findEq hEqv.toFindEq
      (MonoScope.insert h_mono (z := x) (tz := .forAll [] mty) rfl)
  | set_det _ _ _ _ _ _ _ _ _ hEqv => exact MonoScope_of_findEq hEqv.toFindEq h_mono
  | set_nondet _ _ _ _ _ hEqv => exact MonoScope_of_findEq hEqv.toFindEq h_mono
  | assert _ _ _ _ _ _ _ hEqv => exact MonoScope_of_findEq hEqv.toFindEq h_mono
  | assume _ _ _ _ _ _ _ hEqv => exact MonoScope_of_findEq hEqv.toFindEq h_mono
  | cover _ _ _ _ _ _ _ hEqv => exact MonoScope_of_findEq hEqv.toFindEq h_mono

/-- Typing an extended command by the typechecker spec over a monotype-only scope yields a
    monotype-only scope. -/
theorem CmdExtHasType_MonoScope {C : LContext CoreLParams} {P : Program}
    {Δ Δ' : WrittenEnv} {Γ Γ' : TContext Unit} {c : Command}
    (h : CmdExtHasType C P Δ Γ c Γ' Δ') (h_mono : MonoScope (IDMeta := Unit) Γ) :
    MonoScope (IDMeta := Unit) Γ' := by
  cases h with
  | cmd _ _ _ hc => exact CmdHasType_MonoScope hc h_mono
  | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEqv =>
    exact MonoScope_of_findEq hEqv.toFindEq h_mono

end -- public section

end TypeSpec

public section

open Lambda

/-- The written-type-variable environment sending each variable to its image under `S`. -/
def substEnv (S : Subst) : TypeSpec.WrittenEnv :=
  fun v => some (LMonoTy.subst S (.ftvar v))

/-- Binding the type variables of a declared type in an environment that already binds every
    type variable changes nothing. -/
theorem TypeSpec.WrittenEnv.bindFirst_substEnv {S : Subst} (rigid : List TyIdentifier)
    (ann : LMonoTy) (σ : SubstOne) : (substEnv S).bindFirst rigid ann σ = substEnv S := by
  funext v
  simp only [TypeSpec.WrittenEnv.bindFirst, substEnv]

/-- In an environment binding every written type variable, every annotation is in scope. -/
theorem TypeSpec.annotsInScope_substEnv (rigid : List TyIdentifier) (S : Subst)
    (e : Expression.Expr) : AnnotsInScope rigid (substEnv S) e :=
  fun _ _ _ _ => Or.inr rfl

/-- `instAnnotTy Δ t` substitutes `t` by the restriction of `readTyVar Δ` to its free
    variables. -/
theorem instAnnotTy_eq (Δ : TypeSpec.WrittenEnv) (t : LMonoTy) :
    TypeSpec.instAnnotTy Δ t = LMonoTy.subst [restrictTo (readTyVar Δ) t] t := by
  rw [TypeSpec.instAnnotTy]

end -- public section

end Core
