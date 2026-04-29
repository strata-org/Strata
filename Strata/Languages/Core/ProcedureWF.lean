/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Procedure

public section

namespace Core

/-! ## Helper lemmas about getInoutParams and getOutputOnlyParams -/

/-- Keys of `getInoutParams` are a subset of keys of inputs. -/
theorem getInoutParams_keys_subset_inputs (h : Procedure.Header) :
    ∀ id ∈ ListMap.keys h.getInoutParams, id ∈ ListMap.keys h.inputs := by
  intro id hid
  unfold Procedure.Header.getInoutParams at hid
  rw [ListMap.keys_eq_map_fst] at hid ⊢
  obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := List.mem_map.mp hid
  exact List.mem_map_of_mem (f := Prod.fst) (List.mem_filter.mp hmem).1

/-- Keys of `getOutputOnlyParams` are disjoint from keys of inputs. -/
theorem getOutputOnlyParams_keys_disjoint_inputs (h : Procedure.Header) :
    ∀ id ∈ ListMap.keys h.getOutputOnlyParams, id ∉ ListMap.keys h.inputs := by
  intro id hid
  unfold Procedure.Header.getOutputOnlyParams at hid
  rw [ListMap.keys_eq_map_fst] at hid
  obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := List.mem_map.mp hid
  have hfilt := (List.mem_filter.mp hmem).2
  simp only [Bool.not_eq_true'] at hfilt
  exact fun hmem' => by
    have := List.elem_eq_true_of_mem hmem'
    simp only [List.contains] at hfilt
    exact absurd this (Bool.eq_false_iff.mp hfilt)

/-- Keys of `getOutputOnlyParams` are a subset of keys of outputs. -/
theorem getOutputOnlyParams_keys_subset_outputs (h : Procedure.Header) :
    ∀ id ∈ ListMap.keys h.getOutputOnlyParams, id ∈ ListMap.keys h.outputs := by
  intro id hid
  unfold Procedure.Header.getOutputOnlyParams at hid
  rw [ListMap.keys_eq_map_fst] at hid ⊢
  obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := List.mem_map.mp hid
  exact List.mem_map_of_mem (f := Prod.fst) (List.mem_filter.mp hmem).1

/-- Nodup of `getInoutParams` keys follows from nodup of inputs keys. -/
theorem getInoutParams_nodup (h : Procedure.Header)
    (hnd : (ListMap.keys h.inputs).Nodup) :
    (ListMap.keys h.getInoutParams).Nodup := by
  unfold Procedure.Header.getInoutParams
  rw [ListMap.keys_eq_map_fst] at hnd ⊢
  exact (List.filter_sublist.map Prod.fst).nodup hnd

/-- Nodup of `getOutputOnlyParams` keys follows from nodup of outputs keys. -/
theorem getOutputOnlyParams_nodup (h : Procedure.Header)
    (hnd : (ListMap.keys h.outputs).Nodup) :
    (ListMap.keys h.getOutputOnlyParams).Nodup := by
  unfold Procedure.Header.getOutputOnlyParams
  rw [ListMap.keys_eq_map_fst] at hnd ⊢
  exact (List.filter_sublist.map Prod.fst).nodup hnd

/-- Keys of `getInoutParams` are in both inputs and outputs,
    so they are in `inputs ++ outputs`. -/
theorem getInoutParams_keys_in_io (h : Procedure.Header) :
    ∀ id ∈ ListMap.keys h.getInoutParams,
      id ∈ ListMap.keys h.inputs ++ ListMap.keys h.outputs := by
  intro id hid
  exact List.mem_append_left _ (getInoutParams_keys_subset_inputs h id hid)

namespace WF

open Lambda

theorem snd_values_mem {ps : ListMap CoreLabel Procedure.Check} :
  x ∈ ps.toList →
  x.snd ∈ ListMap.values ps := by
  intros Hin
  induction ps
  case cons h t ih =>
    simp_all [ListMap.toList, ListMap.values]
    cases Hin
    case inl eq => left ; rw [eq]
    case inr mem => right ; exact (ih mem)
  case nil => cases Hin

-- theorem Procedure.typeCheckWF : Procedure.typeCheck C T p pp md = Except.ok (pp', T') → WFProcedureProp p pp := by sorry


/-
set_option warn.sorry false in
/--
A Procedure 'pp' that passes type checking is well formed with respect to the whole program 'p'.
-/
theorem Procedure.typeCheckWF : Procedure.typeCheck T p pp = Except.ok (pp', T') → WFProcedureProp p pp := by
  intros tcok
  simp only [Procedure.typeCheck] at tcok
  generalize Hc1 : (!decide (ListMap.keys pp.header.inputs).Nodup) = if1 at tcok
  generalize Hc2 : (!decide (ListMap.keys pp.header.outputs).Nodup) = if2 at tcok
  generalize Hc3 : (!decide pp.spec.modifies.Nodup) = if3 at tcok
  generalize Hc4 : (pp.spec.modifies.any fun v => decide (v ∈ ListMap.keys pp.header.inputs)) = if4 at tcok
  generalize Hc6 : (pp.spec.modifies.any fun v => decide (v ∈ ListMap.keys pp.header.outputs)) = if6 at tcok
  generalize Hc7 : ((ListMap.keys pp.header.inputs).any fun v => decide (v ∈ ListMap.keys pp.header.outputs)) = if7 at tcok
  generalize Hc8 : (pp.spec.modifies.any fun v => (Maps.find? T.context.types v).isNone) = if8 at tcok
  generalize Hc9 : ((Imperative.Stmts.modifiedVars pp.body).eraseDups.any fun v =>
                    decide ¬v ∈ ListMap.keys pp.header.outputs ++ pp.spec.modifies ++
                    (Imperative.Stmts.definedVars pp.body).eraseDups) = if9 at tcok
  generalize Hc10: ((Procedure.Spec.getCheckExprs pp.spec.preconditions).any fun p =>
                          OldExpressions.containsOldExpr p) = if10 at tcok
  cases if1 with | true => simp_all | false => cases if2 with | true => simp_all | false =>
  cases if3 with | true => simp_all | false => cases if4 with | true => simp_all | false =>
  cases if7 with | true => simp_all; split at tcok <;> simp_all | false =>
    cases if8 with | true => simp_all; split at tcok <;> simp_all | false =>
  cases if9 with
  | true => simp_all; split at tcok <;> simp_all
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at tcok
  constructor
  . simp only [bind, Except.bind] at tcok
    split at tcok <;> simp_all
    split at tcok <;> simp_all
    split at tcok <;> try simp_all
    split at tcok <;> try simp_all
    split at tcok <;> try simp_all
    split at tcok <;> try simp_all
    split at tcok <;> try simp_all
    next heq =>
    exact Statement.typeCheckWF heq
  . -- 4. All local variable declarations in a procedure have no duplicates.
    sorry
  . -- 12. The `inputs` list of a procedure does not overlap with the `outputs` list of the procedure
    sorry
  . simp at Hc1
    exact Hc1
  . simp at Hc2
    exact Hc2
  . -- 11. All `modifies` variables have no duplicates.
    sorry
  . -- 14. The `inputs` list of a procedure are all `CoreIdent.locl`
    sorry
  . -- 15.  The `outputs` list of a procedure are all `CoreIdent.locl`
    sorry
  . constructor <;> simp
    . -- precondition
      apply List.Forall_mem_iff.mpr
      intros x Hin
      constructor
      . constructor
        -- 5. All variables in post-conditions and pre-conditions are either `CoreIdent.locl` or `CoreIdent.glob`.
        . sorry
        -- 16. All variables in pre/post conditions that are `.locl` must be in `outputs` or `inputs` of the procedure
        . sorry
      . split at tcok <;> simp_all
        split at tcok <;> simp_all
        apply Hc10 x.snd.expr ?_
        . -- precondition does not contain old expressions
          simp [Procedure.Spec.getCheckExprs]
          exists x.2
          refine ⟨?_, rfl⟩
          exact snd_values_mem Hin
    . -- postcondition
      apply List.Forall_mem_iff.mpr
      intros x Hin
      constructor
      . -- 5. All variables in post-conditions and pre-conditions are either `CoreIdent.locl` or `CoreIdent.glob`.
        sorry
      . -- 6. Postconditions in a procedure are all `ValidExpression`s
        sorry
    . -- `modifies` variables
      apply List.Forall_mem_iff.mpr
      intros x Hin
      constructor
      -- 1. All modified variables in a procedure are declared in the program.
      sorry
  done
-/

end WF
end Core

end -- public section
