/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Util.ListUtils
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.WF
import Strata.Languages.Boogie.StatementType

---------------------------------------------------------------------
namespace Boogie
namespace WF

open Std Lambda

theorem Statement.typeCheckAux_go_WF :
  Statement.typeCheckAux.go p proc T ss acc = Except.ok (pp', T') →
  WF.WFStatementsProp p acc →
  WF.WFStatementsProp p (acc ++ ss) := by
  intros tcok h_acc_ok
  induction ss generalizing acc T pp' T' with
  | nil => simp_all
  | cons h t ih =>
    unfold Statement.typeCheckAux.go at tcok
    simp [bind] at tcok
    cases h with
    | cmd c =>
      cases c with
      | call lhs procName args md =>
        -- Show that the called procedure is declared.
        sorry
      | cmd cmd =>
        simp [Except.bind] at tcok
        split at tcok <;> try simp_all
        sorry
    | block label bss md => sorry
    | ite c t e md => sorry
    | goto l => sorry
    | loop g m i b md => sorry

/--
A list of Statement `ss` that passes type checking is well formed with respect
to the whole program `p`.
-/
theorem Statement.typeCheckAuxWF :
  Statement.typeCheck T p proc ss = Except.ok (pp', T') →
  WF.WFStatementsProp p ss := by
  intros tcok
  simp [Statement.typeCheck, Statement.typeCheckAux, bind, Except.bind] at tcok
  split at tcok <;> simp_all
  rename_i x v heq
  have h_tc_go := @Statement.typeCheckAux_go_WF p proc T ss [] v.fst v.snd
  simp_all [WFStatementsProp, Forall]
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
        . -- 7. The `lhs` of a call statement contain no duplicates and are `BoogieIdent.locl`.
          sorry
        . refine List.Forall_mem_iff.mpr ?_
          intros arg Hin
          constructor
          refine List.Forall_mem_iff.mpr ?_
          intros var Hin'
          -- 9. All variables mentioned in `args` of a call statement are either `BoogieIdent.locl` or `BoogieIdent.glob`.
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
end Boogie
