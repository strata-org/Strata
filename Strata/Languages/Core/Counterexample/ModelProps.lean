/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.Model
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps

/-! # Properties of level-(c) counterexamples (solver models)

Key theorems:
- `gateModelTypes_flagged`: a binding `gateModelTypes` leaves flagged has every type
  the obligation reads its variable at.
- `interpretableConsts_spec`: every constant `interpretableConsts` offers is an
  uninterpreted constant of `F` that no factory axiom and no removed entry mentions.
-/

namespace Core

open _root_.Lambda Imperative

public section

/-- A binding that `gateModelTypes` leaves flagged was flagged before, and its value has
    each type at which the obligation reads its variable (`obligationReadVars`). -/
theorem gateModelTypes_flagged {F : @Lambda.Factory CoreLParams}
    {obligation : ProofObligation Expression}
    {model : FlaggedLExprModel} {name : CoreIdent} {value : Expression.Expr}
    (h : (name, value, true) ∈ gateModelTypes F obligation model) :
    (name, value, true) ∈ model ∧
      ∀ ty, (name, ty) ∈ obligationReadVars obligation → valueHasMonoType F value ty := by
  simp only [gateModelTypes, List.mem_map] at h
  obtain ⟨⟨name', value', flag⟩, hmem, heq⟩ := h
  simp only [Prod.mk.injEq, Bool.and_eq_true, List.all_eq_true] at heq
  obtain ⟨rfl, rfl, hflag, hall⟩ := heq
  exact ⟨hflag ▸ hmem, fun ty hty => by simpa using hall _ hty⟩

/-- Every constant `interpretableConsts F obligation removed` offers is an uninterpreted
    constant `f` of `F` (`isUninterpretedConst`), with its type, that no axiom of a
    function of `F` and no entry of `removed` mentions. -/
theorem interpretableConsts_spec {F : @Lambda.Factory CoreLParams}
    {obligation : ProofObligation Expression} {removed : List (PathConditionEntry Expression)}
    {c : CoreIdent} {ty : LMonoTy} (h : (c, ty) ∈ interpretableConsts F obligation removed) :
    ∃ f, F[c.name]? = some f ∧ f.name = c ∧ f.output = ty ∧ isUninterpretedConst f ∧
      (∀ g ∈ F.toArray, ∀ a ∈ g.axioms, c.name ∉ a.getOps.map (·.name)) ∧
      c.name ∉ removed.flatMap PathConditionEntry.opNames := by
  simp only [interpretableConsts] at h
  split at h
  · simp at h
  · simp only [List.mem_filterMap, Option.filter_eq_some_iff, Option.ite_none_left_eq_some,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨f, ⟨n, -, hF, hc⟩, hex, rfl, rfl⟩ := h
    simp only [List.contains_iff_mem, List.mem_append, List.mem_flatMap, List.mem_map] at hex
    exact ⟨f, by rw [Factory.getElem?_name hF]; exact hF, rfl, rfl, hc,
      fun g hg a ha hm => hex (.inl ⟨g, by simpa using hg, a, ha, List.mem_map.mp hm⟩),
      fun hm => hex (.inr (by simpa using hm))⟩

end -- public section

end Core
