/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPCoreProgram
public import Strata.Transform.Passive.ProgramProps
public import Strata.Transform.Passive.SimulationProps
import Strata.Util.ExceptProps

/-! # Properties of the WP phase on Core procedures and programs

Key theorems: `contractWrapped_emptySpec` (the contract-wrapped body of a procedure with an
empty contract is the body), `checkLoopFree_ok` (what the check of the WP phase guarantees of a
loop-free list), `wpLoopFree_body` (the WP phase of a loop-free list runs `wpEntry`); and
`wpProcsProgram_unit` (the WP phase of a program keeps its obligation units, which lifts the
per-procedure results of the phase to whole programs). -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP

public section

/-- The contract-wrapped body of a procedure with no preconditions and no postconditions is
    the body. -/
theorem contractWrapped_emptySpec (p : Procedure) (body : Statements)
    (hpre : p.spec.preconditions = []) (hpost : p.spec.postconditions = []) :
    p.contractWrapped body = body := by
  simp [Imperative.Procedure.contractWrapped, hpre, hpost]

/-- **What `checkLoopFree` checks.**  A loop-free list `ss` that passes `checkLoopFree p` reads
    only variables of `entryScope p`, is well scoped from `entryScope p` with its assigned
    variables as locals (`WFL`), and every `exit` of `ss` targets an enclosing block. -/
theorem checkLoopFree_ok {p : Procedure} {ss : Statements}
    (h : checkLoopFree p ss = .ok ()) :
    (∀ x ∈ Block.freeVars ss, x ∈ entryScope p) ∧ WFL (Block.assignedVars ss) (entryScope p) ss ∧
      Block.exitsCoveredByBlocks [] ss := by
  simp only [checkLoopFree, wflBH_eq, Block.assignedVarsH_eq, Block.freeVarsH_eq] at h
  split at h <;> (try split at h) <;> (try split at h) <;> try cases h
  rename_i hw hc
  exact ⟨by grind [List.find?_eq_none], wflB_wfl (by simpa using hw),
    Block.exitsCoveredByBlocks_of_check (by simpa using hc)⟩

/-- The WP phase of a loop-free list runs `wpEntry` with the parameter types. -/
theorem wpLoopFree_body {G : IdSet Expression} {p : Procedure} {ss : Statements}
    {w : WOut Expression} (h : wpLoopFree G p ss = .ok w) :
    wpEntry G (paramTys p) ss = .ok w := (Except.bind_is_ok _ _ _).1 h |>.elim fun _ h => h.2

/-- A successful run of `wpProcsProgram` keeps every obligation unit of its input. -/
private theorem wpProcsProgram_unit {reserved : List Expression.Ident} {mid out : Program}
    (h : wpProcsProgram reserved mid = .ok out) :
    ∀ q md, Decl.proc q md ∈ mid.decls → isObligationUnit q = true → Decl.proc q md ∈ out.decls :=
  fun _ _ hq hu => ((Except.bind_is_ok _ _ _).1 h).elim fun _ ⟨hm, he⟩ => by
    obtain ⟨d, hdo, hd⟩ := mapM_except_mem_left _ _ _ hm _ hq
    simp only [hu, ite_true] at hd
    exact Except.ok.inj he ▸ Except.ok.inj hd ▸ hdo

end -- public section
end WP
end Core
