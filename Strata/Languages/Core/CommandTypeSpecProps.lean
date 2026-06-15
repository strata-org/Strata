/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.CommandTypeSpec
import all Strata.Languages.Core.CmdTypeSpecProps
import all Strata.Languages.Core.StatementType

/-! ## Soundness of Command (CmdExt) Typechecker

This file relates the executable command typechecker `Statement.typeCheckCmd`
to the declarative typing relations `CmdExtHasType` and `CmdExtHasTypeA`.

* **`Command.typeCheckCmd_sound`** — if `typeCheckCmd` succeeds, then
  `CmdExtHasType` holds between the substituted input and output contexts.

* **`Command.typeCheckCmd_annotated_sound`** — if `typeCheckCmd` succeeds,
  the output command satisfies `CmdExtHasTypeA`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

/-! ### Well-formedness conditions on procedures -/

/-- A procedure's formal types only mention declared type parameters. -/
def ProcHeaderClosed (proc : Procedure) : Prop :=
  (∀ mty, mty ∈ proc.header.inputs.values →
    ∀ a, a ∈ LMonoTy.freeVars mty → a ∈ proc.header.typeArgs) ∧
  (∀ mty, mty ∈ proc.header.outputs.values →
    ∀ a, a ∈ LMonoTy.freeVars mty → a ∈ proc.header.typeArgs)

/-! ### Bridge lemma -/

/-- Substituting via `σ = zip typeArgs (map (subst S ∘ ftvar) freshVars)` is
    equivalent to the two-step substitution through fresh variables, provided
    the type's free variables are among `typeArgs`.

    Concretely: if `tyArgSubst = [zip typeArgs (map ftvar freshVars)]` and
    `σ = zip typeArgs (map (fun fv => subst S (ftvar fv)) freshVars)`, then
    `subst [σ] t = subst S (subst tyArgSubst t)` when `freeVars(t) ⊆ typeArgs`.
-/
theorem bridge_subst_eq (typeArgs : List TyIdentifier) (freshVars : List TyIdentifier)
    (S : Subst) (t : LMonoTy)
    (h_len : freshVars.length = typeArgs.length)
    (h_closed : ∀ a, a ∈ LMonoTy.freeVars t → a ∈ typeArgs) :
    let tyArgSubst : Subst := [List.zip typeArgs (freshVars.map LMonoTy.ftvar)]
    let σ : List (TyIdentifier × LMonoTy) :=
      List.zip typeArgs (freshVars.map (fun fv => LMonoTy.subst S (.ftvar fv)))
    LMonoTy.subst [σ] t = LMonoTy.subst S (LMonoTy.subst tyArgSubst t) := by
  sorry

/-! ### Context preservation for call typechecking -/

/-- The call branch of `typeCheckCmd` preserves the context. -/
theorem typeCheckCmd_call_preserves_context (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (pname : String) (callArgs : List (CallArg Expression))
    (md : MetaData Expression) (cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P (.call pname callArgs md) = .ok (cmd', Env')) :
    Env'.context = Env.context := by
  sorry

/-! ### Call case auxiliary -/

/-- Core lemma for the `.call` case: if `typeCheckCmd` succeeds on a call,
    then there exists a procedure and a typing derivation. -/
theorem typeCheckCmd_call_sound_aux (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (pname : String) (callArgs : List (CallArg Expression))
    (md : MetaData Expression) (cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P (.call pname callArgs md) = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_closed : ∀ proc,
      Program.Procedure.find? P ⟨pname, ()⟩ = some proc →
      ProcHeaderClosed proc) :
    ∃ proc, Program.Procedure.find? P ⟨pname, ()⟩ = some proc ∧
      CmdExtHasType C P (TContext.subst Env.context Env'.stateSubstInfo.subst)
        (.call pname callArgs md)
        (TContext.subst Env.context Env'.stateSubstInfo.subst) := by
  sorry

/-! ### Part I — Unannotated soundness -/

/--
Soundness of the command typechecker for `Command` (CmdExt):
if `typeCheckCmd` succeeds, then `CmdExtHasType` holds between the
substituted input and output contexts.
-/
theorem Command.typeCheckCmd_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (cmd cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : ∀ proc pname callArgs md,
      cmd = .call pname callArgs md →
      Program.Procedure.find? P pname = some proc →
      ProcHeaderClosed proc) :
    CmdExtHasType C P (TContext.subst Env.context Env'.stateSubstInfo.subst) cmd
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  cases cmd with
  | cmd c =>
    unfold Statement.typeCheckCmd at h
    simp only [Bind.bind, Except.bind] at h
    elim_err h
    rename_i v h_tc
    obtain ⟨c', Env'_inner⟩ := v
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_cmd_eq, h_env_eq⟩ := h
    subst h_cmd_eq; subst h_env_eq
    have h_sound := Cmd.typeCheck_sound C Env c c' Env'_inner h_tc
      h_wf h_fwf h_ne h_mono h_rigid_inv
    exact CmdExtHasType'.cmd _ _ c h_sound
  | call pname callArgs md =>
    have h_ctx := typeCheckCmd_call_preserves_context C Env P pname callArgs md cmd' Env' h
    rw [h_ctx]
    have h_closed' := h_closed
    simp only [CmdExt.call.injEq] at h_closed'
    -- Extract proc from the successful typechecking
    have ⟨proc, h_find, h_call_sound⟩ :=
      typeCheckCmd_call_sound_aux C Env P pname callArgs md cmd' Env' h h_wf h_fwf h_ne h_mono
        (fun proc h_find => h_closed' proc pname callArgs md ⟨rfl, rfl, rfl⟩ h_find)
    exact h_call_sound

/-! ### Annotated case helpers -/

/-- Bridge: `Command.subst S (.cmd c')` satisfies `CmdExtHasTypeA` when
    `Cmd.applySubst c' S` satisfies `CmdHasTypeA`. -/
theorem Command_subst_cmd_HasTypeA (C : LContext CoreLParams) (P : Program)
    (Env : TEnv Unit) (Env' : TEnv Unit) (c c' : Cmd Expression)
    (h_tc : Imperative.Cmd.typeCheck C Env c = .ok (c', Env'))
    (h_sound : CmdHasTypeA C (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (TypeSpec.Cmd.applySubst c' Env'.stateSubstInfo.subst)
      (TContext.subst Env'.context Env'.stateSubstInfo.subst)) :
    CmdExtHasTypeA C P (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (Statement.Command.subst Env'.stateSubstInfo.subst (.cmd c'))
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  sorry

/-- Core lemma for the annotated `.call` case. -/
theorem typeCheckCmd_call_annotated_sound_aux (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (pname : String) (callArgs : List (CallArg Expression))
    (md : MetaData Expression) (cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P (.call pname callArgs md) = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_closed : ∀ proc,
      Program.Procedure.find? P ⟨pname, ()⟩ = some proc →
      ProcHeaderClosed proc) :
    CmdExtHasTypeA C P (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (Statement.Command.subst Env'.stateSubstInfo.subst cmd')
      (TContext.subst Env.context Env'.stateSubstInfo.subst) := by
  sorry

/-! ### Part II — Annotated soundness -/

/--
Annotated soundness of the command typechecker for `Command` (CmdExt):
if `typeCheckCmd` succeeds, the output command satisfies `CmdExtHasTypeA`.
-/
theorem Command.typeCheckCmd_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (cmd cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_closed : ∀ proc pname callArgs md,
      cmd = .call pname callArgs md →
      Program.Procedure.find? P pname = some proc →
      ProcHeaderClosed proc) :
    CmdExtHasTypeA C P (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (Statement.Command.subst Env'.stateSubstInfo.subst cmd')
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  cases cmd with
  | cmd c =>
    unfold Statement.typeCheckCmd at h
    simp only [Bind.bind, Except.bind] at h
    elim_err h
    rename_i v h_tc
    obtain ⟨c', Env'_inner⟩ := v
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_cmd_eq, h_env_eq⟩ := h
    subst h_cmd_eq; subst h_env_eq
    have h_sound := Cmd.typeCheck_annotated_sound C Env c c' Env'_inner h_tc
      h_wf h_fwf h_ne h_mono h_resolved
    exact Command_subst_cmd_HasTypeA C P Env Env'_inner c c' h_tc h_sound
  | call pname callArgs md =>
    have h_ctx := typeCheckCmd_call_preserves_context C Env P pname callArgs md cmd' Env' h
    rw [h_ctx]
    have h_closed' := h_closed
    simp only [CmdExt.call.injEq] at h_closed'
    exact typeCheckCmd_call_annotated_sound_aux C Env P pname callArgs md cmd' Env' h
      h_wf h_fwf h_ne h_mono h_resolved
      (fun proc h_find => h_closed' proc pname callArgs md ⟨rfl, rfl, rfl⟩ h_find)

end TypeSpec
end Core
