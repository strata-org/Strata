/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProcedureType
public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
public import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
public import Strata.Languages.Core.StatementType
import Strata.DL.Lambda.LExprWFProps
import Strata.Util.Tactics
import all Strata.Languages.Core.StatementType
import Strata.Languages.Core.Typing.Props.StatementTypeProps
import Strata.Languages.Core.ProcedureProps
import all Strata.DL.Imperative.Procedure
import all Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import all Strata.Languages.Core.Program
import all Strata.Languages.Core.ProcedureType
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.Typing.Props.SkolemScopeProps
import all Strata.Languages.Core.Typing.Props.TypeSkolemProps
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Typing.Spec.CmdTypeSpec

/-! # Properties of procedure type checking

Key theorems:
* `Procedure.ambientRigidVarsFixed_iff`: the rigid-variable check holds exactly when the
  substitution fixes every listed variable.
* `Procedure.rigidNames_fresh`: a procedure's rigid renaming uses distinct, reserved,
  unregistered constants that avoid the given name sets.
* `Procedure.rigidNames_spec`: minted against a set covering the names in scope, the renaming
  avoids the names in scope.
* `Procedure.renameReservedTypeArgs_alphaVariant`: the checker's renaming of reserved type
  parameters is a `ProcAlphaVariant`.
* `ProcHasType_iff_of_allowed`: a procedure without reserved type parameters is its only
  renaming.
* `ProcHasTypeExact_transport`: procedure typing by the typechecker spec moves to a type scope
  with the same lookups and aliases. -/

public section

namespace Core

open Lambda
open TypeSpec

/-- `ambientRigidVarsFixed` holds iff the substitution leaves every listed variable unchanged. -/
theorem Procedure.ambientRigidVarsFixed_iff (rigidVars : List TyIdentifier) (S : Subst) :
    Procedure.ambientRigidVarsFixed rigidVars S = true ↔
      ∀ v ∈ rigidVars, LMonoTy.subst S (.ftvar v) = .ftvar v := by
  simp only [Procedure.ambientRigidVarsFixed, List.all_eq_true, beq_iff_eq]

/-! ### Properties of a procedure's rigid renaming -/

/-- A procedure's rigid renaming pairs its type parameters, in order, with distinct
    rigid-prefixed constants that are neither registered types nor names of `scope`, `progSigs`
    or `tyNames ()`. -/
theorem Procedure.rigidNames_fresh (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (proc : Procedure) (tyNames : Unit → List String) :
    RigidNamesPrefixed (Procedure.rigidNames scope progSigs C proc tyNames) ∧
      ((Procedure.rigidNames scope progSigs C proc tyNames).map Prod.snd).Nodup ∧
      RigidNamesFresh C.knownTypes (Procedure.rigidNames scope progSigs C proc tyNames) ∧
      (Procedure.rigidNames scope progSigs C proc tyNames).map Prod.fst =
        proc.header.typeArgs ∧
      ∀ p ∈ Procedure.rigidNames scope progSigs C proc tyNames,
        p.2 ∉ scope.get ∧ p.2 ∉ progSigs.get ∧ p.2 ∉ tyNames () :=
  rigidNamesAvoiding_spec C scope progSigs _ tyNames _

/-- A procedure's rigid renaming, minted against a set `scope` holding every type name in scope
    in `C` and `Env`, is chosen against the names in scope and the names `tyNames ()`. -/
theorem Procedure.rigidNames_spec (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (proc : Procedure)
    (tyNames : Unit → List String) (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ scope.get) :
    ScopeRigid C Env (tyNames ()) proc.header.typeArgs
      (Procedure.rigidNames scope progSigs C proc tyNames) :=
  ScopeRigid.of_cover C Env scope progSigs _ tyNames _ fun _ => hcov

/-- When `tyNames ()` includes every type name the procedure mentions (`procTyNames`), no
    constant of its rigid renaming is one of those names. -/
private theorem Procedure.rigidNames_not_procTyNames (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (proc : Procedure) (tyNames : Unit → List String)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tyNames ()) :
    ∀ p ∈ Procedure.rigidNames scope progSigs C proc tyNames,
      p.2 ∉ procTyNames proc (procAnnotTys proc) :=
  fun p hp hn => ((Procedure.rigidNames_fresh scope progSigs C proc tyNames).2.2.2.2 p hp).2.2
    (htn _ hn)

/-- When `tyNames ()` includes every type name the procedure mentions (`procTyNames`), no
    constant of its rigid renaming is a type name in a type the procedure writes
    (`procAnnotTys`). -/
private theorem Procedure.rigidNames_not_procAnnotTys
    (scope progSigs : Thunk (Std.HashSet String)) (C : Core.Expression.TyContext)
    (proc : Procedure) (tyNames : Unit → List String)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tyNames ()) :
    ∀ p ∈ Procedure.rigidNames scope progSigs C proc tyNames, ∀ t ∈ procAnnotTys proc,
      p.2 ∉ getTypeRefs t := by
  intro p hp t ht hn
  refine Procedure.rigidNames_not_procTyNames scope progSigs C proc tyNames htn p hp ?_
  unfold procTyNames
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨t, ht, hn⟩))

/-- When `tyNames ()` includes every type name the procedure mentions (`procTyNames`), no
    constant of its rigid renaming is a type name in the type of a literal of its conditions or
    body. -/
private theorem Procedure.rigidNames_not_procLitTyNames
    (scope progSigs : Thunk (Std.HashSet String)) (C : Core.Expression.TyContext)
    (proc : Procedure) (tyNames : Unit → List String)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tyNames ()) :
    ∀ p ∈ Procedure.rigidNames scope progSigs C proc tyNames, p.2 ∉ procLitTyNames proc := by
  intro p hp hn
  refine Procedure.rigidNames_not_procTyNames scope progSigs C proc tyNames htn p hp ?_
  unfold procTyNames
  exact List.mem_append_left _ (List.mem_append_right _ hn)

/-- The types of the literals in a procedure's preconditions name no constant of its rigid
    renaming, when the renaming is minted avoiding names `tyNames ()` that include the type
    names the procedure mentions. -/
theorem Procedure.rigidNames_preconditions_consts
    (scope progSigs : Thunk (Std.HashSet String)) (C : Core.Expression.TyContext)
    (proc : Procedure) (tyNames : Unit → List String)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tyNames ()) :
    ∀ c ∈ proc.spec.preconditions.values,
      ConstTysFixed (Procedure.rigidNames scope progSigs C proc tyNames) c.expr := by
  intro c hc
  refine ConstTysFixed_of_litTyNames c.expr fun p hp hn => ?_
  refine Procedure.rigidNames_not_procLitTyNames scope progSigs C proc tyNames htn p hp ?_
  unfold procLitTyNames procCollect
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  exact List.mem_flatMap.mpr ⟨c, hc, hn⟩

/-- The types of the literals in a procedure's postconditions name no constant of its rigid
    renaming, when the renaming is minted avoiding names `tyNames ()` that include the type
    names the procedure mentions. -/
theorem Procedure.rigidNames_postconditions_consts
    (scope progSigs : Thunk (Std.HashSet String)) (C : Core.Expression.TyContext)
    (proc : Procedure) (tyNames : Unit → List String)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tyNames ()) :
    ∀ c ∈ proc.spec.postconditions.values,
      ConstTysFixed (Procedure.rigidNames scope progSigs C proc tyNames) c.expr := by
  intro c hc
  refine ConstTysFixed_of_litTyNames c.expr fun p hp hn => ?_
  refine Procedure.rigidNames_not_procLitTyNames scope progSigs C proc tyNames htn p hp ?_
  unfold procLitTyNames procCollect
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_flatMap.mpr ⟨c, hc, hn⟩

/-- The types of the literals in a procedure's structured body name no constant of its rigid
    renaming, when the renaming is minted avoiding names `tyNames ()` that include the type
    names the procedure mentions. -/
theorem Procedure.rigidNames_body_lits
    (scope progSigs : Thunk (Std.HashSet String)) (C : Core.Expression.TyContext)
    (proc : Procedure) (tyNames : Unit → List String)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tyNames ()) :
    ∀ ss opq, proc.body = .structured ss opq →
      ∀ p ∈ Procedure.rigidNames scope progSigs C proc tyNames, p.2 ∉ stmtsLitTyNames ss := by
  intro ss _ hss p hp hn
  refine Procedure.rigidNames_not_procLitTyNames scope progSigs C proc tyNames htn p hp ?_
  unfold procLitTyNames procCollect
  rw [hss]
  exact List.mem_append_right _ hn

/-- `procSigTyNameThunk` holds every type name in the procedure signatures of `P`. -/
theorem procSigTyNameThunk_cover (P : Program) :
    ∀ n ∈ Program.procSigTyNames P, n ∈ (procSigTyNameThunk P).get :=
  Std.HashSet.mem_ofList_of_mem

/-- No constant of a procedure's rigid renaming, minted against a set `progSigs` holding every
    type name in the procedure signatures of `P`, is a type name in the signature of a
    procedure `P` declares. -/
theorem Procedure.rigidNames_not_programSigs (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (P : Program) (proc : Procedure)
    (tyNames : Unit → List String) (hP : ∀ n ∈ Program.procSigTyNames P, n ∈ progSigs.get) :
    ∀ p ∈ Procedure.rigidNames scope progSigs C proc tyNames, ∀ q md, Decl.proc q md ∈ P.decls →
      ∀ ty ∈ q.header.inputs.values ++ q.header.outputs.values, p.2 ∉ getTypeRefs ty := by
  intro p hp q md hq ty hty hn
  refine ((Procedure.rigidNames_fresh scope progSigs C proc tyNames).2.2.2.2 p hp).2.1 (hP _ ?_)
  unfold Program.procSigTyNames
  refine List.mem_flatMap.mpr ⟨.proc q md, hq, ?_⟩
  exact List.mem_flatMap.mpr ⟨ty, hty, hn⟩

/-- No annotation of a procedure's pre- or postconditions names a constant of its rigid
    renaming, when the renaming is minted avoiding names `tyNames ()` that include the type
    names the procedure mentions. -/
theorem Procedure.rigidNames_conditions (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (proc : Procedure) (tyNames : Unit → List String)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tyNames ()) :
    (∀ c ∈ proc.spec.preconditions.values, allExprTys (mtyAllTyConsNames
      (notRigidConst (Procedure.rigidNames scope progSigs C proc tyNames))) c.expr = true) ∧
    ∀ c ∈ proc.spec.postconditions.values, allExprTys (mtyAllTyConsNames
      (notRigidConst (Procedure.rigidNames scope progSigs C proc tyNames))) c.expr = true := by
  have hnot := Procedure.rigidNames_not_procAnnotTys scope progSigs C proc tyNames htn
  have hnotLit := Procedure.rigidNames_not_procLitTyNames scope progSigs C proc tyNames htn
  refine ⟨fun c hc => allExprTys_of_exprTyNames fun n hn => ?_,
    fun c hc => allExprTys_of_exprTyNames fun n hn => ?_⟩
  · rcases List.mem_append.mp hn with hann | hlit
    · obtain ⟨t, ht, hnt⟩ := List.mem_flatMap.mp hann
      refine notRigidConst_of_ne fun p hp heq => hnot p hp t ?_ (heq ▸ hnt)
      unfold procAnnotTys
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      exact List.mem_flatMap.mpr ⟨c, hc, ht⟩
    · refine notRigidConst_of_ne fun p hp heq => hnotLit p hp ?_
      unfold procLitTyNames procCollect
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      exact List.mem_flatMap.mpr ⟨c, hc, heq ▸ hlit⟩
  · rcases List.mem_append.mp hn with hann | hlit
    · obtain ⟨t, ht, hnt⟩ := List.mem_flatMap.mp hann
      refine notRigidConst_of_ne fun p hp heq => hnot p hp t ?_ (heq ▸ hnt)
      unfold procAnnotTys
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_flatMap.mpr ⟨c, hc, ht⟩
    · refine notRigidConst_of_ne fun p hp heq => hnotLit p hp ?_
      unfold procLitTyNames procCollect
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      exact List.mem_flatMap.mpr ⟨c, hc, heq ▸ hlit⟩

/-- No annotation of a procedure's structured body names a constant of its rigid renaming, when
    the renaming is minted avoiding names `tyNames ()` that include the type names the procedure
    mentions. -/
theorem Procedure.rigidNames_body (scope progSigs : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (proc : Procedure) (tyNames : Unit → List String)
    (htn : ∀ n ∈ procTyNames proc (procAnnotTys proc), n ∈ tyNames ()) :
    ∀ ss opq, proc.body = .structured ss opq →
      allStmtsTys (mtyAllTyConsNames
        (notRigidConst (Procedure.rigidNames scope progSigs C proc tyNames))) ss = true := by
  intro ss _ hss
  rw [Statement.allStmtsTys_eq_all_stmtsAnnotTys]
  refine List.all_eq_true.mpr fun t ht => List.all_eq_true.mpr fun n hn => ?_
  refine notRigidConst_of_ne fun p hp heq =>
    Procedure.rigidNames_not_procAnnotTys scope progSigs C proc tyNames htn p hp t ?_ (heq ▸ hn)
  unfold procAnnotTys
  rw [hss]
  exact List.mem_append_right _ ht

/-! ### Renaming a procedure's reserved type parameters -/

/-- The checker's renaming of the reserved type parameters of a procedure with distinct type
    parameters, away from names `avoid ()` that include the rigid type variables of `C` and the
    free type variables of the variables in `Γ`, renames them injectively to names that neither
    the procedure nor the context uses. -/
theorem Procedure.renameReservedTypeArgs_alphaVariant {C : LContext CoreLParams}
    {Γ : TContext Unit} (avoid : Unit → List String) (proc : Procedure)
    (hnd : proc.header.typeArgs.Nodup)
    (hsub : ∀ v ∈ C.rigidTypeVars ++ Γ.knownTypeVars, v ∈ avoid ()) :
    TypeSpec.ProcAlphaVariant C Γ proc
      (proc.renameReservedTypeArgs avoid fun _ => procAnnotTys proc) := by
  refine ⟨_, reservedTypeArgsRenaming_tyArgRenaming _ hnd ?_,
    Procedure.renameReservedTypeArgs_eq avoid proc _⟩
  intro v hv
  rw [List.append_assoc, List.mem_append] at hv
  rcases hv with hm | hs
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ (hsub v hs)

/-- A renaming of a procedure's type parameters for one context is one for any context with the
    same rigid type variables and the same variable lookups. -/
theorem TypeSpec.ProcAlphaVariant.congr {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit}
    {proc proc' : Procedure} (hrigid : C'.rigidTypeVars = C.rigidTypeVars)
    (hscope : TContext.FindEq (T := CoreLParams) Γ' Γ)
    (h : TypeSpec.ProcAlphaVariant C Γ proc proc') :
    TypeSpec.ProcAlphaVariant C' Γ' proc proc' := by
  obtain ⟨ren, hren, rfl⟩ := h
  exact ⟨ren, TypeSpec.TyArgRenaming.congr hrigid hscope hren, rfl⟩

/-- A procedure whose type parameters all have allowed names is its only renaming. -/
theorem TypeSpec.ProcAlphaVariant.eq_self_of_allowed {C : LContext CoreLParams}
    {Γ : TContext Unit} {proc proc' : Procedure}
    (hallowed : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true)
    (h : TypeSpec.ProcAlphaVariant C Γ proc proc') : proc' = proc := by
  obtain ⟨ren, hren, rfl⟩ := h
  rw [TypeSpec.TyArgRenaming.eq_nil_of_allowed hallowed hren]
  exact Procedure.renameTypeArgs_nil proc

/-- For a procedure whose type parameters all have allowed names, the typechecker spec
    `ProcHasType` means exactly `ProcHasTypeExact` for the procedure itself. -/
theorem TypeSpec.ProcHasType_iff_of_allowed {P : Program} {C : LContext CoreLParams}
    {Γ : TContext Unit} {proc : Procedure}
    (hallowed : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true) :
    TypeSpec.ProcHasType P C Γ proc ↔ TypeSpec.ProcHasTypeExact P C Γ proc := by
  constructor
  · rintro ⟨proc', hv, ht⟩
    rw [← TypeSpec.ProcAlphaVariant.eq_self_of_allowed hallowed hv]
    exact ht
  · intro ht
    have hren : TypeSpec.TyArgRenaming C Γ proc.header.typeArgs proc.mentionedTyVars [] :=
      ⟨⟨List.nodup_nil, List.nodup_nil, fun _ hp => absurd hp List.not_mem_nil⟩,
        fun _ hp => absurd hp List.not_mem_nil⟩
    exact ⟨proc, ⟨[], hren, (Procedure.renameTypeArgs_nil proc).symm⟩, ht⟩

/-- Renaming type parameters keeps the procedures a procedure calls and the shape of its body. -/
theorem Procedure.renameTypeArgs_body (proc : Procedure) (ren : List (String × String)) :
    (proc.renameTypeArgs ren).calledProcedureNames = proc.calledProcedureNames ∧
      (proc.renameTypeArgs ren).body.isStructured = proc.body.isStructured := by
  simp only [Procedure.calledProcedureNames_eq_body]
  cases hb : proc.body with
  | structured ss =>
    simp only [Procedure.renameTypeArgs, Procedure.mapTys, hb,
      Procedure.Body.calledProcedureNames_structured, mapStmtsTys_calledProcedureNames,
      Imperative.Body.isStructured, Imperative.Body.getStructured]
    exact ⟨trivial, rfl⟩
  | cfg c =>
    simp only [Procedure.renameTypeArgs, Procedure.mapTys, hb,
      Procedure.Body.calledProcedureNames_cfg, Imperative.Body.isStructured,
      Imperative.Body.getStructured]
    exact ⟨trivial, trivial⟩
  | abstract =>
    simp [Procedure.renameTypeArgs, Procedure.mapTys, hb, Procedure.Body.calledProcedureNames]

namespace TypeSpec

/-- Procedure-body typing by the typechecker spec transfers to a type scope with the same
    lookups and aliases. -/
private theorem ProcBodyHasType_transport {P : Program}
    {C : LContext CoreLParams} {Γ Ξ : TContext Unit} {body : Procedure.Body}
    (hR : TContext.FindEq (T := CoreLParams) Ξ Γ)
    (h : ProcBodyHasType P C Γ body) : ProcBodyHasType P C Ξ body := by
  cases h with
  | cfg c o => exact .cfg c o
  | abstract => exact .abstract
  | structured ss Cout Γout Δout o hss =>
    obtain ⟨Γout', hss', -⟩ := StatementsHasType_transport hR hss
    exact .structured ss Cout Γout' Δout o hss'

/-- Procedure typing by the typechecker spec transfers to a type scope with the same lookups and
    aliases. -/
theorem ProcHasTypeExact_transport {P : Program}
    {C : LContext CoreLParams} {Γ Ξ : TContext Unit} {proc : Procedure}
    (hR : TContext.FindEq (T := CoreLParams) Ξ Γ)
    (h : ProcHasTypeExact P C Γ proc) : ProcHasTypeExact P C Ξ proc where
  inputsNodup := h.inputsNodup
  outputsNodup := h.outputsNodup
  oldNamesFresh := h.oldNamesFresh
  typeArgsNodup := h.typeArgsNodup
  typeArgsNotReserved := h.typeArgsNotReserved
  noUndeclaredVars := h.noUndeclaredVars
  signatureWellKinded := fun ty hty =>
    hR.aliases ▸ h.signatureWellKinded ty hty
  modRights := h.modRights
  preconditionsTyped := fun c hc =>
    HasType_FindEq C _ _ _ _ (push_FindEq _ _ _ hR) (h.preconditionsTyped c hc)
  postconditionsTyped := fun c hc =>
    HasType_FindEq C _ _ _ _ (push_FindEq _ _ _ hR) (h.postconditionsTyped c hc)
  preconditionsAnnots := fun c hc =>
    writtenAnnotsOk_of_aliases_eq hR.aliases (h.preconditionsAnnots c hc)
  postconditionsAnnots := fun c hc =>
    writtenAnnotsOk_of_aliases_eq hR.aliases (h.postconditionsAnnots c hc)
  preconditionsInScope := h.preconditionsInScope
  postconditionsInScope := h.postconditionsInScope
  bodyTyped := ProcBodyHasType_transport (push_FindEq _ _ _ hR) h.bodyTyped

end TypeSpec

/-! ### Typing is invariant under identifier-table changes -/

/-- `ProcBodyHasType` is invariant under changing the context's `idents` field. -/
private theorem TypeSpec.ProcBodyHasType_idents_irrel
    (P : Program) (C : Expression.TyContext) (j : Identifiers Unit)
    (Γ_body : TContext Unit) (body : Procedure.Body)
    (h : ProcBodyHasType P { C with idents := j } Γ_body body) :
    ProcBodyHasType P C Γ_body body := by
  cases h with
  | structured ss C' Γ' Δ' o hss =>
    obtain ⟨Cbase, _, hss'⟩ := StatementsHasType_idents_irrel hss C j rfl
    exact ProcBodyHasType.structured ss Cbase Γ' Δ' o hss'
  | cfg c o => exact ProcBodyHasType.cfg c o
  | abstract => exact ProcBodyHasType.abstract

/-- Changing only the ambient identifier table preserves procedure typing by the typechecker
    spec. -/
theorem TypeSpec.ProcHasTypeExact_idents_irrel
    (P : Program) (C : Expression.TyContext) (j : Identifiers Unit)
    (Γ : TContext Unit) (proc : Procedure)
    (h : ProcHasTypeExact P { C with idents := j } Γ proc) :
    ProcHasTypeExact P C Γ proc where
  inputsNodup := h.inputsNodup
  outputsNodup := h.outputsNodup
  oldNamesFresh := h.oldNamesFresh
  typeArgsNodup := h.typeArgsNodup
  typeArgsNotReserved := h.typeArgsNotReserved
  noUndeclaredVars := h.noUndeclaredVars
  signatureWellKinded := fun ty hty =>
    validSourceTy_idents_irrel (h.signatureWellKinded ty hty)
  modRights := h.modRights
  preconditionsTyped := fun c hc =>
    HasType_idents_irrel C j _ _ _ (h.preconditionsTyped c hc)
  postconditionsTyped := fun c hc =>
    HasType_idents_irrel C j _ _ _ (h.postconditionsTyped c hc)
  preconditionsAnnots := fun c hc =>
    writtenAnnotsOk_idents_irrel C j _ _ (h.preconditionsAnnots c hc)
  postconditionsAnnots := fun c hc =>
    writtenAnnotsOk_idents_irrel C j _ _ (h.postconditionsAnnots c hc)
  preconditionsInScope := h.preconditionsInScope
  postconditionsInScope := h.postconditionsInScope
  bodyTyped :=
    ProcBodyHasType_idents_irrel P
      { C with rigidTypeVars := C.rigidTypeVars ++ proc.header.typeArgs } j
      (procBodyContext Γ proc) proc.body h.bodyTyped

end Core

end -- public section
