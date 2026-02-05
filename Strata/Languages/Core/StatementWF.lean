/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Util.ListUtils
import Strata.Languages.Core.Program
import Strata.Languages.Core.WF
import Strata.Languages.Core.StatementType

---------------------------------------------------------------------
namespace Core
namespace WF

open Std Lambda

/-- Helper lemma: mapping only the values of a ListMap preserves the keys. -/
private theorem listMap_keys_map_snd {α β γ : Type} (l : List (α × β)) (f : β → γ) :
    ListMap.keys (l.map (fun (id, ty) => (id, f ty))) = ListMap.keys l := by
  induction l with
  | nil => simp [ListMap.keys]
  | cons h t ih => simp [ListMap.keys, ih]

theorem typeCheckCmdWF: Statement.typeCheckCmd C T p c = Except.ok v
  → WFCmdExtProp p c := by
  intro H
  simp [Statement.typeCheckCmd, bind, Except.bind] at H
  split at H <;> try contradiction
  split at H <;> try contradiction
  rename_i H' ; simp [Imperative.Cmd.typeCheck, bind, Except.bind] at H'
  repeat (first | (split at H' <;> try contradiction) | constructor)
  any_goals repeat (split at H <;> try contradiction)
  any_goals simp_all
  sorry
  sorry
  sorry

theorem Statement.typeCheckAux_elim_acc: Statement.typeCheckAux.go P op C T ss (acc1 ++ acc2) = Except.ok (pp, T', C') ↔
  (List.IsPrefix acc2.reverse pp ∧ Statement.typeCheckAux.go P op C T ss acc1 = Except.ok (pp.drop acc2.length, T', C'))
  := by
  induction ss generalizing pp acc1 acc2 T C
  simp [Statement.typeCheckAux.go]
  constructor <;> intro H
  simp [← H]
  simp [H]
  rw [← List.length_reverse, ← List.prefix_iff_eq_append]; simp [H]
  rename_i h t ind
  unfold Statement.typeCheckAux.go
  simp [bind, Except.bind]
  split <;> try contradiction
  repeat (any_goals (split <;> try contradiction))
  any_goals simp
  any_goals rw [← List.cons_append, ind]

theorem Statement.typeCheckAux_elim_singleton: Statement.typeCheckAux.go P op C T ss [s] = Except.ok (pp, T', C') →
  Statement.typeCheckAux.go P op C T ss [] = Except.ok (pp.drop 1, T', C') := by
  intro H
  have : [s] = [] ++ [s] := by simp
  rw [this, Statement.typeCheckAux_elim_acc] at H; simp at H
  simp [H]

theorem Statement.typeCheckAux_go_WF :
  Statement.typeCheckAux.go P op C T ss [] = Except.ok (pp', T', C') →
  WF.WFStatementsProp P acc →
  WF.WFStatementsProp P (acc ++ ss) := by
  intros tcok h_acc_ok
  induction ss generalizing acc C T pp' T' C' with
  | nil => simp_all [WFStatementsProp]
  | cons h t ih =>
    unfold Statement.typeCheckAux.go at tcok
    simp [bind] at tcok
    cases h with
    | cmd c =>
      cases c with
      | call lhs procName args md =>
        -- Show that the called procedure is declared.
        simp [Except.bind] at tcok
        split at tcok <;> try contradiction
        rw[List.append_cons];
        have tcok := Statement.typeCheckAux_elim_singleton tcok
        apply ih tcok <;> try assumption
        simp [WFStatementsProp] at *
        simp [List.Forall_append, Forall, *]
        apply typeCheckCmdWF (by assumption)
      | cmd cmd =>
        simp [Except.bind] at tcok
        split at tcok <;> try contradiction
        rw[List.append_cons];
        have tcok := Statement.typeCheckAux_elim_singleton tcok
        apply ih tcok <;> try assumption
        simp [WFStatementsProp] at *
        simp [List.Forall_append, Forall, *]
        apply typeCheckCmdWF (by assumption)
    | block label bss md =>
      simp [Except.bind] at tcok
      repeat split at tcok <;> try contradiction
      have tcok := Statement.typeCheckAux_elim_singleton tcok
      rw[List.append_cons];
      apply ih tcok <;> try assumption
      simp [WFStatementsProp] at *
      simp [List.Forall_append, Forall, *]
      constructor
    | ite c t e md =>
      simp [Except.bind] at tcok
      repeat (split at tcok <;> try contradiction)
      have tcok := Statement.typeCheckAux_elim_singleton tcok
      rw[List.append_cons];
      apply ih tcok <;> try assumption
      simp [WFStatementsProp] at *
      simp [List.Forall_append, Forall, *]
      constructor
    | goto l =>
      simp [Except.bind] at tcok
      split at tcok <;> try contradiction
      have tcok := Statement.typeCheckAux_elim_singleton tcok
      rw[List.append_cons];
      apply ih tcok <;> try assumption
      simp [WFStatementsProp] at *
      simp [List.Forall_append, Forall, *]
      constructor
    | loop g m i b md =>
      simp [Except.bind] at tcok
      repeat (split at tcok <;> try contradiction)
      any_goals (repeat (split at tcok <;> try contradiction))
      any_goals (repeat (split at tcok <;> try contradiction))
      any_goals (repeat (split at tcok <;> try contradiction))
      any_goals (have tcok := Statement.typeCheckAux_elim_singleton tcok; rw[List.append_cons])
      any_goals (apply ih tcok <;> try assumption)
      any_goals (try simp [WFStatementsProp] at *; try simp [List.Forall_append, *]; try constructor)
      any_goals (simp [Forall])
      any_goals constructor
    | funcDecl decl md =>
      simp [Except.bind] at tcok
      -- Split through the tryCatch and PureFunc.typeCheck structure
      simp only [tryCatch] at tcok
      repeat (split at tcok <;> try contradiction)
      -- After splits, we need to extract the Function.typeCheck success
      simp only [Except.mapError, tryCatchThe] at *
      -- Now split on the PureFunc.typeCheck result
      split at * <;> try contradiction
      rename_i v_go heq_go v_func heq_func_match heq_tryCatch
      -- v_func has type (PureFunc Expression × Function × TEnv Visibility)
      -- heq_func_match is: (match PureFunc.typeCheck ... with | .error => ... | .ok v => .ok v) = .ok v_func
      -- The match on .ok case is identity, so we can extract the equality
      have heq_func_tc : Function.typeCheck C T
        { name := decl.name, typeArgs := decl.typeArgs, isConstr := decl.isConstr,
          inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty)),
          output := Lambda.LTy.toMonoTypeUnsafe decl.output,
          body := decl.body, attr := decl.attr, concreteEval := none, axioms := decl.axioms }
        = .ok (v_func.2.1, v_func.2.2) := by
          simp only [PureFunc.typeCheck, bind, Except.bind] at heq_func_match
          cases h : Function.typeCheck C T
            { name := decl.name, typeArgs := decl.typeArgs, isConstr := decl.isConstr,
              inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty)),
              output := Lambda.LTy.toMonoTypeUnsafe decl.output,
              body := decl.body, attr := decl.attr, concreteEval := none, axioms := decl.axioms } with
          | error e => simp [h] at heq_func_match
          | ok v =>
            simp [h] at heq_func_match
            -- heq_func_match shows v_func = (decl', v.fst, v.snd)
            -- So v_func.2.1 = v.fst and v_func.2.2 = v.snd
            simp [← heq_func_match]
      have tcok := Statement.typeCheckAux_elim_singleton tcok
      rw[List.append_cons];
      apply ih tcok <;> try assumption
      simp [WFStatementsProp] at *
      simp [List.Forall_append, Forall, *]
      constructor
      -- Prove arg_nodup using Function.typeCheck_inputs_nodup
      have h_nodup := Function.typeCheck_inputs_nodup C T
        { name := decl.name, typeArgs := decl.typeArgs, isConstr := decl.isConstr,
          inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty)),
          output := Lambda.LTy.toMonoTypeUnsafe decl.output,
          body := decl.body, attr := decl.attr, concreteEval := none, axioms := decl.axioms }
        v_func.2.1 v_func.2.2 heq_func_tc
      -- h_nodup : (decl.inputs.map ...).keys.Nodup, we need: decl.inputs.keys.Nodup
      rw [listMap_keys_map_snd] at h_nodup
      exact h_nodup

/--
A list of Statement `ss` that passes type checking is well formed with respect
to the whole program `p`.
-/
theorem Statement.typeCheckWF :
  Statement.typeCheck C T P proc ss = Except.ok (pp', T') →
  WF.WFStatementsProp P ss := by
  intros tcok
  simp [Statement.typeCheck, Statement.typeCheckAux, bind, Except.bind] at tcok
  split at tcok <;> simp_all
  rename_i x v heq
  have h_tc_go := Statement.typeCheckAux_go_WF (P := P) (op := proc) (C := C) (T := T) (ss := ss) (pp' := v.fst) (T' := v.snd.fst) (C' := v.snd.snd) (acc := []) heq
  simp [WFStatementsProp] at h_tc_go
  exact h_tc_go (by constructor)
  done

/-
theorem Statement.typeCheckWF :
  Statement.typeCheck T p proc ss = Except.ok (pp', T') →
  WF.WFStatementsProp p ss := by
  intros tcok
  simp only [Statement.typeCheck, bind, Except.bind] at *
  induction ss generalizing T pp' T' with
  | nil => constructor
  | cons h t ih =>
  unfold Statement.typeCheckAux at ih
  apply (List.Forall_cons (WF.WFStatementProp p) h t).mpr
  apply And.intro
  . unfold Statement.typeCheckAux Statement.typeCheckAux.go at tcok
    simp only [bind] at tcok
    cases h with
    | cmd c =>
      cases c with
      | call lhs procName args md =>
        -- Show that the called procedure is declared
        simp [Except.bind, Statement.typeCheckCmd] at tcok
        split at tcok <;> simp_all
        next _ _ heq =>
        split at heq <;> try simp_all
        next Hcall =>
        split at Hcall <;> try simp_all
        split at Hcall <;> simp_all
        split at Hcall <;> try simp_all
        split at Hcall <;> try simp_all
        constructor <;> simp_all
        . -- 13. The `lhs` of a call statement is disjoint from `modifies`, `outputs`, and `inputs` of the procedure
          sorry
        . -- 7. The `lhs` of a call statement contain no duplicates and are `CoreIdent.locl`.
          sorry
        . refine List.Forall_mem_iff.mpr ?_
          intros arg Hin
          constructor
          refine List.Forall_mem_iff.mpr ?_
          intros var Hin'
          -- 9. All variables mentioned in `args` of a call statement are either `CoreIdent.locl` or `CoreIdent.glob`.
          sorry
      | cmd =>
        constructor
    | _ => constructor
    done
  . split at tcok <;> simp_all
    next Htc =>
    unfold Statement.typeCheckAux Statement.typeCheckAux.go at Htc
    simp only [bind, Except.bind] at Htc
    cases h with
    | cmd c =>
      simp only at Htc
      rename_i _ ss_Tss
      split at Htc <;> try simp_all
      -- split at Htc <;> try simp_all
      next Htc3 =>
      rename_i _ c_Tc
      apply ih
      rw [Htc3]
    | block l b md =>
      simp at Htc
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      next Htc3 =>
      apply ih
      rw [Htc3]
    | ite c tb e md =>
      simp at Htc
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      next heq =>
      apply ih
      rw [heq]
    | loop g m i b md =>
      sorry
    | goto l =>
      simp at Htc
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      split at Htc <;> try simp_all
      next heq =>
      apply ih
      rw [heq]
-/

end WF
end Core
