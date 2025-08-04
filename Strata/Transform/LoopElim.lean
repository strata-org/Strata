/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.Languages.Boogie.Statement

namespace Boogie
open Imperative Lambda

/-! ## Loop elimination

This transformation recursively removes loops from a Boogie statement, resulting
in a new, acyclic statement. If a loop invariant is present, it adds checks that
the invariant is established on entry and re-established at the end of each
iteration.

-/

partial
def Statement.removeLoopsM (s : Boogie.Statement) : StateM Nat Boogie.Statement :=
  let incState : StateM Nat Unit := StateT.modifyGet (fun x => ((), x + 1))
  match s with
  | .loop guard _ invariant? body _ => do
    let invariant := invariant?.getD LExpr.true
    let loop_num ← StateT.get
    let neg_guard : Expression.Expr := .app boolNotOp guard
    let assigned_vars := (Stmts.modifiedVars body.ss).map (λ s => s.2)
    let havocd : Statement :=
      .block s!"loop_havoc_{loop_num}" {
        ss := assigned_vars.map (λ n => Statement.havoc (Coe.coe n) {})
      } {}
    let entry_invariant : Statement :=
      .assert s!"entry_invariant_{loop_num}" invariant {}
    let first_iter_facts : Statement :=
      .block s!"first_iter_asserts_{loop_num}" {ss := [entry_invariant]} {}
    let arbitrary_iter_assumes := .block s!"arbitrary_iter_assumes_{loop_num}" {
      ss := [(Statement.assume s!"assume_guard_{loop_num}" guard {}),
             (Statement.assume s!"assume_invariant_{loop_num}" invariant {})]}
    let maintain_invariant : Statement :=
      .assert s!"arbitrary_iter_maintain_invariant_{loop_num}" invariant {}
    incState
    let body_statements ← body.ss.mapM removeLoopsM
    let arbitrary_iter_facts : Statement := .block s!"arbitrary_iter_facts_{loop_num}" {
      ss := [havocd, arbitrary_iter_assumes] ++
            body_statements ++
            [maintain_invariant]
    } {}
    let not_guard : Statement := .assume s!"not_guard_{loop_num}" neg_guard {}
    let invariant : Statement := .assume s!"invariant_{loop_num}" invariant {}
    pure (.ite guard {ss := [first_iter_facts, arbitrary_iter_facts, havocd, not_guard, invariant]} { ss := [] } {})
  | .ite c t e md => do
    incState
    let tss ← t.ss.mapM removeLoopsM
    incState
    let ess ← e.ss.mapM removeLoopsM
    pure (.ite c { ss := tss } { ss := ess } md)
  | .block label b md => do
    incState
    let bss ← b.ss.mapM removeLoopsM
    pure (.block label { ss := bss } md)
  | .cmd _ => pure s
  | .goto _ _ => pure s

def Statement.removeLoops (s : Boogie.Statement) : Boogie.Statement :=
  (StateT.run (removeLoopsM s) 0).fst
