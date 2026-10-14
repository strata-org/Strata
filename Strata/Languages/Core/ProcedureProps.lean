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
    calc lm.map _ = lm.map _root_.id := List.map_congr_left (fun x _ => this x)
    _ = lm := List.map_id lm
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

end Core

end -- public section
