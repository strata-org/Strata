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
wraps an inout `Var`. Warns on `old(e)` where `e` mentions no inout, and on
nested `old(old(...))`.
-/

namespace Strata
namespace Laurel

public section

structure PushOldState where
  inoutNames : List String := []
  diagnostics : List DiagnosticModel := []

abbrev PushOldM := StateM PushOldState

@[expose]
def warn (source : Option FileRange) (msg : String) : PushOldM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [diagnosticFromSource source msg .Warning] }

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
    warn expr.source "nested `old(...)` has no effect"
    return inner
  | _ => return expr

@[expose]
def visitOld (expr : StmtExprMd) : PushOldM (Option StmtExprMd) := do
  match expr.val with
  | .Old inner =>
    let (inner', changed) ← (mapStmtExprM insideOld inner).run false
    if !changed then
      warn expr.source "`old(...)` has no effect: expression contains no inout parameter"
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
    variable. Returns the rewritten program and any warnings emitted. -/
def pushOldInward (program : Program) : Program × List DiagnosticModel :=
  let (program', finalState) :=
    (program.staticProcedures.mapM transformProcedurePushOld).run {}
  ({ program with staticProcedures := program' }, finalState.diagnostics)

/-- Pipeline pass: translate modifies clauses into ensures clauses. -/
public def pushOldInwardPass : LoweringPass where
  name := "pushOldInward"
  documentation := "Distributes `old(...)` over its subexpressions until each `old` immediately wraps an inout variable. Warns on `old(e)` where `e` mentions no inout parameter and on nested `old(old(...))`."
  run := fun _ p _ =>
    let (p', diags) := pushOldInward p
    (p', diags, {})

end -- public section
end Laurel
end Strata
