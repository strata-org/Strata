/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.LaurelPass

/-!
# Push `Old` Inward

Distribute `StmtExpr.Old` over its sub-expressions until each `Old` immediately
wraps an inout `Var`.

No-op `old(...)` usage (an `old` that captures no heap state, or a nested
`old(old(...))`) is diagnosed by `Resolution.validateOldUsage`, the single
source of user-program diagnostics — this pass only performs the rewrite.
-/

namespace Strata
namespace Laurel

public section

structure PushOldState where
  inoutNames : List String := []

abbrev PushOldM := StateM PushOldState

@[expose]
def insideOld (expr : StmtExprMd) : StateT Bool PushOldM StmtExprMd := do
  match expr.val with
  | .Var (.Local name) =>
    if (← getThe PushOldState).inoutNames.contains name.text then
      set true
      return ⟨.Old expr, expr.source⟩
    else
      return expr
  | .Old inner =>
    -- Nested `old` is redundant; `Resolution` warns. Here we just drop it.
    return inner
  | _ => return expr

@[expose]
def visitOld (expr : StmtExprMd) : PushOldM (Option StmtExprMd) := do
  match expr.val with
  | .Old inner =>
    let (inner', _changed) ← (mapStmtExprM insideOld inner).run false
    return some inner'
  | _ => return none

@[expose]
def pushOldInwardExpr (expr : StmtExprMd) : PushOldM StmtExprMd :=
  mapStmtExprPrePostM visitOld pure expr

@[expose]
def procInoutNames (proc : Procedure) : List String :=
  proc.inputs.filterMap fun inp =>
    if proc.outputs.any (·.name == inp.name) then some inp.name.text else none

@[expose]
def transformProcedurePushOld (proc : Procedure) : PushOldM Procedure := do
  modify fun s => { s with inoutNames := procInoutNames proc }
  mapProcedureM pushOldInwardExpr proc

/-- Push every `StmtExpr.Old` inward until it immediately wraps an inout
    variable. (No-op `old` usage is diagnosed by `Resolution`.) -/
def pushOldInward (program : Program) : Program :=
  let (program', _finalState) :=
    (program.staticProcedures.mapM transformProcedurePushOld).run {}
  { program with staticProcedures := program' }

/-- Pipeline pass: translate modifies clauses into ensures clauses. -/
public def pushOldInwardPass : LoweringPass where
  name := "pushOldInward"
  documentation := "Distributes `old(...)` over its subexpressions until each `old` immediately wraps an inout variable. No-op `old(...)` usage is diagnosed by Resolution."
  run := fun _ p _ =>
    (pushOldInward p, [], {})

end -- public section
end Laurel
end Strata
