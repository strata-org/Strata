/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreSpecification
public import Strata.DL.Imperative.Logic.TerminationProps
import Strata.Languages.Core.StatementSemanticsProps
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.RelationsProps
import all Strata.Languages.Core.Procedure
import all Strata.Util.ListMap

/-! # Core specification properties

Supporting results for `CoreSpecification`: projections of the typed
procedure-entry environment.

## Key results

- `mem_procVerifyInitIdents_of_input`, `mem_procVerifyInitIdents_of_output`, and
  `mem_procVerifyInitIdents_of_oldInout` identify required procedure-entry slots.
- `ProcEnvWF.storeDefined`, `ProcEnvWF.inputTyped`, `ProcEnvWF.outputTyped`, and
  `ProcEnvWF.oldInoutTyped` project definedness and typed values from `ProcEnvWF`.
- `ProcEnvWF.of_sameSignature` — an entry environment carries over to a
  procedure with the same header and specification.
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-! ### Convenient projections of `ProcEnvWF.storeDefinedAndWellTyped` -/

/-- An input parameter (with its declared type) is one of the variables that
    must be initialized before the body runs. -/
theorem mem_procVerifyInitIdents_of_input {proc : Procedure}
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (h : (id, ty) ∈ proc.header.inputs.toList) :
    (id, ty) ∈ procVerifyInitIdents proc := by
  unfold procVerifyInitIdents
  exact List.mem_append_left _ (List.mem_append_left _ h)

/-- An output parameter (with its declared type) is one of the variables that
    must be initialized before the body runs. -/
theorem mem_procVerifyInitIdents_of_output {proc : Procedure}
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (h : (id, ty) ∈ proc.header.outputs.toList) :
    (id, ty) ∈ procVerifyInitIdents proc := by
  unfold procVerifyInitIdents
  exact List.mem_append_left _ (List.mem_append_right _ h)

/-- The old snapshot of an in-out parameter (with the parameter's original
    type) is one of the variables that must be initialized before the body
    runs. -/
theorem mem_procVerifyInitIdents_of_oldInout {proc : Procedure}
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (h : (id, ty) ∈ proc.header.getInoutParams.toList) :
    (CoreIdent.mkOld id.name, ty) ∈ procVerifyInitIdents proc := by
  unfold procVerifyInitIdents
  exact List.mem_append_right _ (List.mem_map_of_mem h)

/-- Definedness projection: every variable that must be initialized holds
    *some* value. -/
theorem ProcEnvWF.storeDefined {params : InitEnvWFParams} {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (hm : (id, ty) ∈ procVerifyInitIdents proc) :
    (ρ.store id).isSome := by
  obtain ⟨v, hv, _⟩ := h.storeDefinedAndWellTyped id ty hm
  rw [hv]; rfl

/-- Typed-value projection for input parameters. -/
theorem ProcEnvWF.inputTyped {params : InitEnvWFParams} {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (hm : (id, ty) ∈ proc.header.inputs.toList) :
    ∃ v, ρ.store id = some v ∧
      HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty) :=
  h.storeDefinedAndWellTyped id ty (mem_procVerifyInitIdents_of_input hm)

/-- Typed-value projection for output parameters. -/
theorem ProcEnvWF.outputTyped {params : InitEnvWFParams} {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (hm : (id, ty) ∈ proc.header.outputs.toList) :
    ∃ v, ρ.store id = some v ∧
      HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty) :=
  h.storeDefinedAndWellTyped id ty (mem_procVerifyInitIdents_of_output hm)

/-- Typed-value projection for the old snapshots of in-out parameters. -/
theorem ProcEnvWF.oldInoutTyped {params : InitEnvWFParams} {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    {id : Expression.Ident} {ty : Lambda.LMonoTy}
    (hm : (id, ty) ∈ proc.header.getInoutParams.toList) :
    ∃ v, ρ.store (CoreIdent.mkOld id.name) = some v ∧
      HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty) :=
  h.storeDefinedAndWellTyped (CoreIdent.mkOld id.name) ty
    (mem_procVerifyInitIdents_of_oldInout hm)


/-- `ProcEnvWF` reads only a procedure's header, its specification and the
    well-formedness of its body. So an entry environment of `proc` is one of any
    `proc'` with the same header and specification whose body is well formed
    from it. -/
theorem ProcEnvWF.of_sameSignature {params : InitEnvWFParams} {proc proc' : Procedure}
    {ρ : Imperative.Env Expression} (h : ProcEnvWF params proc ρ)
    (h_header : proc'.header = proc.header) (h_spec : proc'.spec = proc.spec)
    (h_structured : ∀ ss, proc'.body = .structured ss →
      Core.Logic.BlockInitEnvWF params [Stmt.block "" ss #[]] ρ)
    (h_cfg : ∀ cfg, proc'.body = .cfg cfg → Core.Logic.CFGInitEnvWF params cfg ρ) :
    ProcEnvWF params proc' ρ where
  toWellFormedSemanticEval := h.toWellFormedSemanticEval
  storeValues := h.storeValues
  storeDefinedAndWellTyped id ty hm := by
    rw [procVerifyInitIdents, h_header] at hm
    exact h.storeDefinedAndWellTyped id ty hm
  oldInoutMatchesInout := by rw [h_header]; exact h.oldInoutMatchesInout
  preconditionsHold := by rw [h_spec]; exact h.preconditionsHold
  structuredBodyWF := h_structured
  cfgBodyWF := h_cfg

end Core.Specification

end -- public section
