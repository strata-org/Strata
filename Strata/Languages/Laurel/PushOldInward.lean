/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
# Push `Old` Inward

Distribute `StmtExpr.Old` over its sub-expressions until each `Old` immediately
wraps an inout `Var`. After this pass, the Laurel-to-Core translator only
needs to handle `Old (Var (Local n))`: every other `Old` shape has been pushed
deeper or eliminated.

Two warnings are emitted:
- An outer `old(...)` whose subexpression mentions no inout parameter has no
  effect; the wrapper is dropped.
- A nested `old(...)` inside another `old(...)` has no effect; the inner
  wrapper is dropped.
-/

namespace Strata
namespace Laurel

public section

structure PushOldState where
  inoutNames : List String := []
  diagnostics : List DiagnosticModel := []
  /-- Set whenever the inner traversal wraps an inout `Var` in `.Old`. -/
  changed : Bool := false

abbrev PushOldM := StateM PushOldState

private def warn (source : Option FileRange) (msg : String) : PushOldM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics ++ [diagnosticFromSource source msg .Warning] }

/-- Inside an `old(...)` subtree: wrap inout `Var` in `.Old`, drop nested
    `old(...)` (with a warning), leave everything else alone. -/
private def insideOld (expr : StmtExprMd) : PushOldM StmtExprMd := do
  match expr.val with
  | .Var (.Local name) =>
    if (← get).inoutNames.contains name.text then
      modify fun s => { s with changed := true }
      return ⟨.Old expr, expr.source⟩
    else
      return expr
  | .Old inner =>
    warn expr.source "nested `old(...)` has no effect"
    return inner
  | _ => return expr

/-- Top-down: when we hit an `Old`, distribute via `mapStmtExprM` and signal
    that recursion should stop here (children handled internally). For all
    other nodes we return `none` so the generic traversal recurses normally. -/
private def visitOld (expr : StmtExprMd) : PushOldM (Option StmtExprMd) := do
  match expr.val with
  | .Old inner =>
    modify fun s => { s with changed := false }
    let inner' ← mapStmtExprM insideOld inner
    if !(← get).changed then
      warn expr.source "`old(...)` has no effect: expression contains no inout parameter"
    return some inner'
  | _ => return none

def pushOldInwardExpr (expr : StmtExprMd) : PushOldM StmtExprMd :=
  mapStmtExprPrePostM visitOld pure expr

/-- Inout names of a procedure: parameters that appear in both inputs and outputs. -/
private def procInoutNames (proc : Procedure) : List String :=
  proc.inputs.filterMap fun inp =>
    if proc.outputs.any (·.name == inp.name) then some inp.name.text else none

private def transformProcedure (proc : Procedure) : PushOldM Procedure := do
  modify fun s => { s with inoutNames := procInoutNames proc }
  mapProcedureM pushOldInwardExpr proc

/--
Push every `StmtExpr.Old` inward until it immediately wraps an inout variable.
Returns the rewritten program along with any warnings emitted.
-/
def pushOldInward (program : Program) : Program × List DiagnosticModel :=
  let (program', finalState) :=
    (program.staticProcedures.mapM transformProcedure).run {}
  ({ program with staticProcedures := program' }, finalState.diagnostics)

end -- public section
end Laurel
end Strata
