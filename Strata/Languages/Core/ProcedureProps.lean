/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Procedure
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.StatementSemanticsProps

/-! # Properties of Core procedures

Key results:

- `Procedure.mapExprs_id` — `Procedure.mapExprs` with the identity is the
  identity (the procedure-level analog of `Statements.mapExprs_id`).
- `Procedure.Header.keys_getInoutParams`, `Procedure.Header.keys_getOutputOnlyParams` —
  the keys of Core's inout and output-only formals are the generic
  `Calls.inoutParams` / `Calls.outputOnlyParams`.
-/

public section

namespace Core

/-- The keys of Core's inout formals are the generic `Calls.inoutParams`. -/
theorem Procedure.Header.keys_getInoutParams (h : Procedure.Header) :
    ListMap.keys h.getInoutParams = Imperative.Calls.inoutParams (P := Expression) h :=
  listMap_keys_filter _ _

/-- A name is an in-out parameter exactly when it is both an input and an output. -/
theorem Procedure.Header.mem_keys_getInoutParams (h : Procedure.Header) (g : CoreIdent) :
    g ∈ h.getInoutParams.keys ↔ g ∈ h.inputs.keys ∧ g ∈ h.outputs.keys := by
  unfold Procedure.Header.getInoutParams Core.getInoutParams
  rw [listMap_keys_filter _ h.inputs]
  simp only [List.mem_filter, List.contains_iff_mem]

/-- The keys of Core's output-only formals are the generic `Calls.outputOnlyParams`. -/
theorem Procedure.Header.keys_getOutputOnlyParams (h : Procedure.Header) :
    ListMap.keys h.getOutputOnlyParams = Imperative.Calls.outputOnlyParams (P := Expression) h :=
  listMap_keys_filter (fun _ => !_) _

/-- `Procedure.mapExprs` with the identity is the identity. -/
theorem Procedure.mapExprs_id (p : Procedure) : Procedure.mapExprs id p = p := by
  have hmap : ∀ (lm : ListMap CoreLabel Procedure.Check),
      lm.map (fun (l, c) => (l, { c with expr := id c.expr })) = lm := by
    intro lm
    have : ∀ x : CoreLabel × Procedure.Check,
        (fun (l, c) => (l, { c with expr := id c.expr })) x = x := by
      rintro ⟨l, c⟩; rfl
    exact (List.map_congr_left (fun x _ => this x)).trans (List.map_id lm)
  cases p with
  | mk header spec body =>
    cases spec with
    | mk pre post =>
      simp only [Procedure.mapExprs, hmap]
      cases body with
      | structured ss =>
        simp only [Imperative.Procedure.mk.injEq, Imperative.Body.structured.injEq, true_and]
        exact Statements.mapExprs_id ss
      | cfg c => rfl

/-- A structured body calls exactly the procedures called by its statements. -/
@[simp] theorem Procedure.Body.calledProcedureNames_structured (ss : Statements) :
    Procedure.Body.calledProcedureNames (.structured ss)
      = Statements.calledProcedureNames ss := by
  rw [Procedure.Body.calledProcedureNames]

/-- A control-flow-graph body has no called procedure names. -/
@[simp] theorem Procedure.Body.calledProcedureNames_cfg (g : DetCFG) :
    Procedure.Body.calledProcedureNames (.cfg g) = [] := by
  rw [Procedure.Body.calledProcedureNames]

/-- A procedure's callees are exactly the callees of its body. -/
@[simp] theorem Procedure.calledProcedureNames_eq_body (p : Procedure) :
    Procedure.calledProcedureNames p = Procedure.Body.calledProcedureNames p.body := by
  rw [Procedure.calledProcedureNames]

end Core

end -- public section
