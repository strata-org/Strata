/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkLoopElim
import all Strata.Languages.Core.Counterexample.BackLinkLoopElim

/-! # Properties of the `loopElim` configuration map

`unloopElimConfig origins` maps a configuration of the loop-elimination output to the
source, replacing every *expansion* (an `if` whose `then` branch is headed by a block
whose label `origins` records) by its source loop (`unloopStmt`, `unloopStmts`).

Key theorems:
- `unloopElimConfig_stmts_of_free`: a `.stmts` start whose statement list contains no
  expansion (`loopExpansionFreeStmts`) and does not start with a statement the pass
  introduced maps to itself.
- `unloopElimConfig_top`: the top-level downstream start of a *loop-elimination image*
  of a source unit (`LoopElimImageStmts`: the source with each eliminated loop replaced
  by its expansion) maps to the top of the source unit.
-/

namespace Core

open _root_.Lambda Imperative

public section

/-! ## Identity outside expansions -/

mutual

/-- `unloopStmt` is the identity on an expansion-free statement (one containing no `if`
    headed by a block whose label the origins record, at any depth). -/
private theorem unloopStmt_of_free (origins : LoopOrigins) :
    ∀ (s : Statement), loopExpansionFreeStmt origins s → unloopStmt origins s = s
  | .ite _ t e _, ⟨hhead, ht, he⟩ => by
    have hT := unloopStmts_of_free _ _ ht
    have hE := unloopStmts_of_free _ _ he
    rcases t with _ | ⟨_ | _, _⟩ <;> cases e <;> simp [*, unloopStmt]
  | .block _ b _, hfree | .loop _ _ _ b _, hfree => by
    simp [unloopStmt, unloopStmts_of_free _ _ hfree]
  | .cmd _, _ | .exit .., _ | .typeDecl .., _ => rfl

/-- `unloopStmts` is the identity on an expansion-free statement list (one containing no
    `if` headed by a block whose label the origins record, at any depth). -/
private theorem unloopStmts_of_free (origins : LoopOrigins) :
    ∀ (ss : List Statement), loopExpansionFreeStmts origins ss → unloopStmts origins ss = ss
  | [], _ => rfl
  | _ :: _, ⟨hs, hr⟩ => by rw [unloopStmts, unloopStmt_of_free _ _ hs, unloopStmts_of_free _ _ hr]

end

/-- **Identity outside expansions.**  `unloopElimConfig` maps a `.stmts` start to itself
    when its statement list is expansion-free (no `if` headed by a block whose label the
    origins record, at any depth) and does not start with a block or assumption the pass
    introduced. -/
theorem unloopElimConfig_stmts_of_free (origins : LoopOrigins) (ss : List Statement)
    (env : IEnv Expression) (hfree : loopExpansionFreeStmts origins ss)
    (hhead : headIsLoopElimInternal ss = false) :
    unloopElimConfig origins (.stmts ss env) = some (.stmts ss env) := by
  grind [unloopElimConfig, unloopStmts_of_free]

/-! ## The top-level downstream start -/

/-- `unloopStmt` keeps an `if` whose `then` branch is not headed by a block whose label the
    origins record, and maps both of its branches. -/
private theorem unloopStmt_ite_of_unrecorded (origins : LoopOrigins)
    (guard : ExprOrNondet Expression)
    (thenB elseB : List Statement) (md : Imperative.MetaData Expression)
    (hhead : match thenB with
      | .block label _ _ :: _ => origins.lookup label = none
      | _ => True) :
    unloopStmt origins (.ite guard thenB elseB md)
      = .ite guard (unloopStmts origins thenB) (unloopStmts origins elseB) md := by
  rcases thenB with _ | ⟨_ | _ | _ | _ | _ | _ | _, _⟩ <;> cases elseB
  all_goals rw [unloopStmt] <;> simp! [*]

mutual

/-- `unloopStmt` recovers a source statement from its loop-elimination image (the source
    with each eliminated loop replaced by its expansion). -/
private theorem unloopStmt_of_image (origins : LoopOrigins) :
    ∀ {s s' : Statement}, LoopElimImageStmt origins s s' → unloopStmt origins s' = s
  | _, _, .expansion _ _ _ _ _ _ _ h => by simp! [h]
  | _, _, .ite _ _ _ _ _ _ hhead hthen helse => by
    rw [unloopStmt_ite_of_unrecorded _ _ _ _ _ hhead, unloopStmts_of_image _ hthen,
      unloopStmts_of_image _ helse]
  | _, _, .block _ _ _ _ himg | _, _, .loop _ _ _ _ _ _ himg => by
    simp [unloopStmt, unloopStmts_of_image _ himg]
  | _, _, .cmd _ | _, _, .exit .. | _, _, .typeDecl .. => rfl

/-- `unloopStmts` recovers a source statement list from its loop-elimination image (the
    source with each eliminated loop replaced by its expansion, position by position). -/
private theorem unloopStmts_of_image (origins : LoopOrigins) :
    ∀ {ss ss' : List Statement}, LoopElimImageStmts origins ss ss' →
      unloopStmts origins ss' = ss
  | _, _, .nil => rfl
  | _, _, .cons _ _ _ _ hs hr => by
    rw [unloopStmts, unloopStmt_of_image _ hs, unloopStmts_of_image _ hr]

end

/-- **Downstream top => source top.**  The top-level downstream start `.stmts st' env`,
    for `st'` the loop-elimination image of the source unit `st` (the source with each
    eliminated loop replaced by its expansion) not starting with a statement the pass
    introduced, maps to the top of the source unit `.stmts st env` (the pass introduces no
    variables, so the environment is unchanged). -/
theorem unloopElimConfig_top (origins : LoopOrigins) (st st' : List Statement)
    (env : IEnv Expression) (himg : LoopElimImageStmts origins st st')
    (hhead : headIsLoopElimInternal st' = false) :
    unloopElimConfig origins (.stmts st' env) = some (.stmts st env) := by
  grind [unloopElimConfig, unloopStmts_of_image]

end -- public section

end Core
