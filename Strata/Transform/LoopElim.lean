/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.Stmt

namespace Boogie
open Imperative Lambda

/-! ## Loop elimination

This transformation recursively removes loops from a statement, resulting in a
new, acyclic statement. If a loop invariant is present, it adds checks that the
invariant is established on entry and re-established at the end of each
iteration. If a loop invariant is not present, this transformation isn't very
useful.

-/

mutual

def Stmt.removeLoopsM
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C]
  (s : Stmt P C) : StateM Nat (Stmt P C) :=
  match s with
  | .loop guard _ invariant? ⟨ bss ⟩ md => do
    let invariant := invariant?.getD HasBool.tt
    let loop_num ← StateT.modifyGet (fun x => (x, x + 1))
    let neg_guard : P.Expr := HasNot.not guard
    let assigned_vars := Stmts.modifiedVars bss
    let havocd : Stmt P C :=
      .block s!"loop_havoc_{loop_num}" {
        ss := assigned_vars.map (λ n => Stmt.cmd (HasHavoc.havoc n))
      } {}
    let entry_invariant :=
      Stmt.cmd (HasPassiveCmds.assert s!"entry_invariant_{loop_num}" invariant md)
    let first_iter_facts :=
      .block s!"first_iter_asserts_{loop_num}" {ss := [entry_invariant]} {}
    let arbitrary_iter_assumes := .block s!"arbitrary_iter_assumes_{loop_num}" {
      ss := [(Stmt.cmd (HasPassiveCmds.assume s!"assume_guard_{loop_num}" guard md)),
             (Stmt.cmd (HasPassiveCmds.assume s!"assume_invariant_{loop_num}" invariant md))]}
    let maintain_invariant :=
      Stmt.cmd (HasPassiveCmds.assert s!"arbitrary_iter_maintain_invariant_{loop_num}" invariant md)
    let body_statements ← Stmts.removeLoopsM bss
    let arbitrary_iter_facts := .block s!"arbitrary_iter_facts_{loop_num}" {
      ss := [havocd, arbitrary_iter_assumes] ++
            body_statements ++
            [maintain_invariant]
    } {}
    let not_guard := Stmt.cmd (HasPassiveCmds.assume s!"not_guard_{loop_num}" neg_guard md)
    let invariant := Stmt.cmd (HasPassiveCmds.assume s!"invariant_{loop_num}" invariant md)
    pure (.ite guard {ss := [first_iter_facts, arbitrary_iter_facts, havocd, not_guard, invariant]} { ss := [] } {})
  | .ite c ⟨ tss ⟩ ⟨ ess ⟩ md => do
    let tss ← Stmts.removeLoopsM tss
    let ess ← Stmts.removeLoopsM ess
    pure (.ite c { ss := tss } { ss := ess } md)
  | .block label ⟨ bss ⟩ md => do
    let bss ← Stmts.removeLoopsM bss
    pure (.block label { ss := bss } md)
  | .cmd _ => pure s
  | .goto _ _ => pure s

def Stmts.removeLoopsM
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C]
  (ss : List (Stmt P C)) : StateM Nat (List (Stmt P C)) :=
  match ss with
  | [] => pure []
  | s :: ss => do
    let s ← Stmt.removeLoopsM s
    let ss ← Stmts.removeLoopsM ss
    pure (s :: ss)

end

def Stmt.removeLoops
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C]
  (s : Stmt P C) : Stmt P C :=
  (StateT.run (removeLoopsM s) 0).fst
