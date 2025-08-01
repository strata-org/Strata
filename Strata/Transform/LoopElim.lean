/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Statement

namespace Boogie
open Imperative

/-! ## Loop elimination

This transformation recursively removes loops from a Boogie statement, resulting
in a new, acyclic statement. It requires that the loop is annotated with a
decreasing measure and one or more loop invariants. It translates those two
annotations to a collection of assertions and assumptions that check:

  * The invariant is established on entry.

  * The measure is non-negative on entry.

  * The invariant is re-established by the end each iteration, assuming it holds
    at the beginning of the iteration.

  * The measure decreases on each iteration of the loop.

  * If the measure is non-positive, it implies the guard is false (i.e., the
    loop has terminated.)

-/

partial
def Statement.removeLoopsM (s : Boogie.Statement) : StateM Nat Boogie.Statement :=
  let incState : StateM Nat Unit := StateT.modifyGet (fun x => ((), x + 1))
  let trueExpr : Expression.Expr := .const "true" (some .bool)
  let intZero : Expression.Expr := .const "0" (some .int)
  match s with
  | .loop guard measure invariant body _ =>
    match measure, invariant with
    | .some measure, some invariant => do
      let loop_num ← StateT.get
      let neg_guard : Expression.Expr := .app boolNotOp guard
      let assigned_vars := (Stmts.modifiedVars body.ss).map (λ s => (Visibility.unres, s))
      let havocd : Statement :=
        .block s!"loop_havoc_{loop_num}" {ss:= assigned_vars.map (λ (_, n) => Statement.havoc n {})} {}
      let measure_pos :=
        .app (.app intGeOp measure) intZero
      let entry_invariant : Statement :=
        .assert s!"entry_invariant_{loop_num}" invariant {}
      let assert_measure_positive : Statement :=
        .assert s!"assert measure_pos_{loop_num}" measure_pos {}
      let first_iter_facts : Statement :=
        .block s!"first_iter_asserts_{loop_num}" {ss := [entry_invariant, assert_measure_positive]} {}
      let arbitrary_iter_assumes := .block s!"arbitrary_iter_assumes_{loop_num}" {
        ss := [(Statement.assume s!"assume_guard_{loop_num}" guard {}),
               (Statement.assume s!"assume_invariant_{loop_num}" invariant {}),
               (Statement.assume s!"assume_measure_pos_{loop_num}" measure_pos {})]} {}
      let measure_old_value_assign : Statement :=
        .init s!"special_name_for_old_measure_value_{loop_num}" (.forAll [] .int) measure {}
      let measure_decreases : Statement :=
        .assert s!"measure_decreases_{loop_num}" (.app (.app intLtOp measure) (.fvar s!"special_name_for_old_measure_value_{loop_num}" none)) {}
      let measure_imp_not_guard : Statement :=
        .assert s!"measure_imp_not_guard_{loop_num}" (.ite (.app (.app intLeOp measure) intZero) neg_guard trueExpr) {}
      let maintain_invariant : Statement :=
        .assert s!"arbitrary_iter_maintain_invariant_{loop_num}" invariant {}
      incState
      let body_statements ← body.ss.mapM removeLoopsM
      let arbitrary_iter_facts : Statement := .block s!"arbitrary_iter_facts_{loop_num}" {
        ss := [havocd, arbitrary_iter_assumes, measure_old_value_assign] ++
              body_statements ++
              [measure_decreases, measure_imp_not_guard, maintain_invariant]
      } {}
      let not_guard : Statement := .assume s!"not_guard_{loop_num}" neg_guard {}
      let invariant : Statement := .assume s!"invariant_{loop_num}" invariant {}

      pure (.ite guard {ss := [first_iter_facts, arbitrary_iter_facts, havocd, not_guard, invariant]} {ss := []} {})
    | _, _ => panic! s!"Loop elimination requires measure and invariant, got: {measure} {invariant}"
  | .ite c t e md => do
    incState
    let tss ← t.ss.mapM removeLoopsM
    incState
    let ess ← e.ss.mapM removeLoopsM
    pure (.ite c {ss := tss } {ss := ess } md)
  | .block label b md => do
    incState
    let bss ← b.ss.mapM removeLoopsM
    pure (.block label {ss := bss } md)
  | .cmd _ => pure s
  | .goto _ _ => pure s

def Statement.removeLoops (s : Boogie.Statement) : Boogie.Statement :=
  (StateT.run (removeLoopsM s) 0).fst
