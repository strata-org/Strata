/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
# Push `Old` Inward

Distribute `StmtExpr.Old` over its sub-expressions until each `Old` immediately
wraps a variable reference. After this pass, the Laurel-to-Core translator only
needs to handle `Old (Var (Local n))`: every other `Old` shape has been pushed
deeper or eliminated.

If an `Old e` does not contain any inout parameter of the enclosing procedure,
`old(...)` has no effect and we emit a warning. The wrapper is then dropped.
-/

namespace Strata
namespace Laurel

public section

structure PushOldState where
  inoutNames : List String := []
  diagnostics : List DiagnosticModel := []

abbrev PushOldM := StateM PushOldState

private def warn (source : Option FileRange) (msg : String) : PushOldM Unit := do
  modify fun s => { s with diagnostics := s.diagnostics ++ [diagnosticFromSource source msg .Warning] }

/-- Does `expr` reference any variable named in `inoutNames`? -/
partial def mentionsAnyInout (inoutNames : List String) (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .Var (.Local name) => inoutNames.contains name.text
  | .Var (.Field target _) => mentionsAnyInout inoutNames target
  | .PrimitiveOp _ args | .StaticCall _ args =>
      args.any (mentionsAnyInout inoutNames)
  | .InstanceCall target _ args =>
      mentionsAnyInout inoutNames target || args.any (mentionsAnyInout inoutNames)
  | .ReferenceEquals l r => mentionsAnyInout inoutNames l || mentionsAnyInout inoutNames r
  | .IfThenElse c t e =>
      mentionsAnyInout inoutNames c || mentionsAnyInout inoutNames t
        || (e.elim false (mentionsAnyInout inoutNames))
  | .AsType target _ | .IsType target _ => mentionsAnyInout inoutNames target
  | .Quantifier _ _ _ body => mentionsAnyInout inoutNames body
  | .Old inner | .Fresh inner | .Assigned inner => mentionsAnyInout inoutNames inner
  | _ => false

/-- Distribute `Old` over the structure of `expr`, stopping once each `Old`
    immediately wraps an inout `Var`. Variables that are not inout lose the
    surrounding `Old` (no two-state difference applies to them). -/
partial def pushOld (expr : StmtExprMd) : PushOldM StmtExprMd := do
  let source := expr.source
  let wrap (v : StmtExpr) : StmtExprMd := ⟨v, source⟩
  match expr.val with
  | .Var (.Local name) =>
      if (← get).inoutNames.contains name.text then
        return wrap (.Old expr)
      else
        return expr
  | .Var (.Field target fieldName) =>
      return wrap (.Var (.Field (← pushOld target) fieldName))
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .This | .Abstract | .All | .New _ =>
      return expr
  | .PrimitiveOp op args =>
      return wrap (.PrimitiveOp op (← args.mapM pushOld))
  | .StaticCall callee args =>
      return wrap (.StaticCall callee (← args.mapM pushOld))
  | .InstanceCall target callee args =>
      return wrap (.InstanceCall (← pushOld target) callee (← args.mapM pushOld))
  | .ReferenceEquals lhs rhs =>
      return wrap (.ReferenceEquals (← pushOld lhs) (← pushOld rhs))
  | .IfThenElse cond th el =>
      let el' ← el.mapM pushOld
      return wrap (.IfThenElse (← pushOld cond) (← pushOld th) el')
  | .AsType target ty => return wrap (.AsType (← pushOld target) ty)
  | .IsType target ty => return wrap (.IsType (← pushOld target) ty)
  | .Quantifier mode param trigger body =>
      let trigger' ← trigger.mapM pushOld
      return wrap (.Quantifier mode param trigger' (← pushOld body))
  | .Old inner => pushOld inner -- old(old(e)) ≡ old(e)
  | _ => return expr

/-- Top-down rewrite: every `Old e` is replaced by the result of distributing
    `Old` through `e`. Warns once per user-written `Old` that does not mention
    any inout parameter. -/
partial def pushOldInwardExpr (expr : StmtExprMd) : PushOldM StmtExprMd := do
  match expr.val with
  | .Old inner =>
      let inner' ← pushOldInwardExpr inner
      if mentionsAnyInout (← get).inoutNames inner' then
        pushOld inner'
      else
        warn expr.source "`old(...)` has no effect: expression contains no inout parameter"
        return inner'
  | _ =>
      let rewriteOld (e : StmtExprMd) : PushOldM StmtExprMd := do
        match e.val with
        | .Old inner =>
            if mentionsAnyInout (← get).inoutNames inner then
              pushOld inner
            else
              warn e.source "`old(...)` has no effect: expression contains no inout parameter"
              return inner
        | _ => return e
      mapStmtExprM (m := PushOldM) rewriteOld expr

/-- Inout names of a procedure: parameters that appear in both inputs and outputs. -/
private def procInoutNames (proc : Procedure) : List String :=
  proc.inputs.filterMap fun inp =>
    if proc.outputs.any (·.name == inp.name) then some inp.name.text else none

/-- Apply `pushOldInward` to every expression in a procedure. -/
private def transformProcedure (proc : Procedure) : PushOldM Procedure := do
  modify fun s => { s with inoutNames := procInoutNames proc }
  mapProcedureM pushOldInwardExpr proc

/--
Push every `StmtExpr.Old` inward until it immediately wraps a variable.
Returns the rewritten program along with any warnings emitted (e.g. for
`old(...)` over an expression with no inout variable).
-/
def pushOldInward (program : Program) : Program × List DiagnosticModel :=
  let initState : PushOldState := {}
  let (program', finalState) :=
    (program.staticProcedures.mapM transformProcedure).run initState
  ({ program with staticProcedures := program' }, finalState.diagnostics)

end -- public section
end Laurel
end Strata
