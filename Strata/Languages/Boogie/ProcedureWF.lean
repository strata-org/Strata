/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Util.ListUtils
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.ProcedureType
import Strata.Languages.Boogie.WF
import Strata.Languages.Boogie.StatementWF

namespace Boogie
namespace WF

open Lambda

theorem snd_values_mem {ps : ListMap BoogieLabel Procedure.Check} :
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
  . -- 14. The `inputs` list of a procedure are all `BoogieIdent.locl`
    sorry
  . -- 15.  The `outputs` list of a procedure are all `BoogieIdent.locl`
    sorry
  . constructor <;> simp
    . -- precondition
      apply List.Forall_mem_iff.mpr
      intros x Hin
      constructor
      . constructor
        -- 5. All variables in post-conditions and pre-conditions are either `BoogieIdent.locl` or `BoogieIdent.glob`.
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
      . -- 5. All variables in post-conditions and pre-conditions are either `BoogieIdent.locl` or `BoogieIdent.glob`.
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
end WF
end Boogie
