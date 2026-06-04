/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Util.Tactics

/-!
# Eliminate Increment / Decrement

Lowers `.IncrDecr` nodes (Java-style `++x`, `x++`, `--x`, `x--`) into
existing Laurel constructs. Runs before `LiftImperativeExpressions` so that
later passes never see `.IncrDecr`.

The lowering, parameterised on `op` (`Incr | Decr`) and `mode` (`Pre | Post`):

* **Prefix** (`++x`, `--x`) — yields the **new** value:
  ```
  ++x  ⇝  (x := x + 1)
  --x  ⇝  (x := x - 1)
  ```
  An assignment used as an expression already evaluates to the new value, so
  no extra arithmetic is needed.

* **Postfix** (`x++`, `x--`) — yields the **old** value, recovered by
  applying the inverse delta to the new value:
  ```
  x++  ⇝  ((x := x + 1) - 1)
  x--  ⇝  ((x := x - 1) + 1)
  ```

The traversal is statement-context aware: a top-level `.IncrDecr` directly in
a statement position (a list element of a block, the body of a while, an
if-branch reached as a statement) is lowered to a clean `.Assign` whose
yielded value is unused. In every other position the expression form is
emitted, and `LiftImperativeExpressions` later snapshots the variable so
nested `(x++)+(x++)` etc. observe Java semantics.

The target of `.IncrDecr` must be a `Variable.Local` or `Variable.Field` —
the concrete-to-abstract translator already enforces this. A stray
`.Declare` falls back to the expression form (which Lift will then handle
gracefully).
-/

namespace Strata.Laurel

public section

private def bare (v : StmtExpr) (source : Option FileRange) : StmtExprMd :=
  ⟨v, source⟩

/-- Reconstruct the read-side `StmtExprMd` corresponding to the given target
    `Variable`. For `.Local` we read the variable; for `.Field` we read the
    field. For `.Declare` (which should not occur after the translator's
    lvalue check) we fall back to a local read with the same name. -/
private def targetAsRead (target : VariableMd) : StmtExprMd :=
  let source := target.source
  match target.val with
  | .Local name => bare (.Var (.Local name)) source
  | .Field tgt fieldName => bare (.Var (.Field tgt fieldName)) source
  | .Declare param => bare (.Var (.Local param.name)) source

/-- Build `.Assign [target] (target ⊕ 1)` where `⊕` is `Add` if `op = Incr`
    and `Sub` if `op = Decr`. The result is an assignment expression that
    yields the new value of `target`. -/
private def lowerToAssign (op : IncrDecrOp) (target : VariableMd)
    (source : Option FileRange) : StmtExprMd :=
  let primOp : Operation := match op with
    | .Incr => .Add
    | .Decr => .Sub
  let one := bare (.LiteralInt 1) source
  let read := targetAsRead target
  let updated := bare (.PrimitiveOp primOp [read, one]) source
  bare (.Assign [target] updated) source

/-- Build the expression form yielding the right value depending on `mode`.
    See module docstring for the rewrite tables. -/
private def lowerToExpr (mode : IncrDecrMode) (op : IncrDecrOp)
    (target : VariableMd) (source : Option FileRange) : StmtExprMd :=
  let assign := lowerToAssign op target source
  match mode with
  | .Pre => assign
  | .Post =>
    -- Recover the old value: apply the inverse delta to the new value.
    let inverseOp : Operation := match op with
      | .Incr => .Sub
      | .Decr => .Add
    let one := bare (.LiteralInt 1) source
    bare (.PrimitiveOp inverseOp [assign, one]) source

mutual

/-- Lower `.IncrDecr` nodes appearing in expression-yielding positions.
    Recurses into all StmtExpr children with `lowerExpr` except the bodies of
    blocks/while-loops, whose top-level statements use `lowerStmt`. -/
partial def lowerExpr (expr : StmtExprMd) : StmtExprMd :=
  let source := expr.source
  match expr.val with
  | .IncrDecr mode op target =>
    -- Recurse into a Field target first (covers nested IncrDecr in obj.f).
    let target' := lowerVariable target
    lowerToExpr mode op target' source
  | .Block stmts label =>
    ⟨.Block (stmts.map lowerStmt) label, source⟩
  | .While cond invs dec body =>
    ⟨.While (lowerExpr cond) (invs.map lowerExpr) (dec.map lowerExpr) (lowerStmt body), source⟩
  | .IfThenElse cond th el =>
    ⟨.IfThenElse (lowerExpr cond) (lowerExpr th) (el.map lowerExpr), source⟩
  | .Assign targets value =>
    ⟨.Assign (targets.map lowerVariable) (lowerExpr value), source⟩
  | .PrimitiveOp op args =>
    ⟨.PrimitiveOp op (args.map lowerExpr), source⟩
  | .StaticCall callee args =>
    ⟨.StaticCall callee (args.map lowerExpr), source⟩
  | .InstanceCall target callee args =>
    ⟨.InstanceCall (lowerExpr target) callee (args.map lowerExpr), source⟩
  | .Var (.Field target fieldName) =>
    ⟨.Var (.Field (lowerExpr target) fieldName), source⟩
  | .Var _ => expr
  | .PureFieldUpdate target fieldName newVal =>
    ⟨.PureFieldUpdate (lowerExpr target) fieldName (lowerExpr newVal), source⟩
  | .ReferenceEquals lhs rhs =>
    ⟨.ReferenceEquals (lowerExpr lhs) (lowerExpr rhs), source⟩
  | .AsType target ty =>
    ⟨.AsType (lowerExpr target) ty, source⟩
  | .IsType target ty =>
    ⟨.IsType (lowerExpr target) ty, source⟩
  | .Quantifier mode param trigger body =>
    ⟨.Quantifier mode param (trigger.map lowerExpr) (lowerExpr body), source⟩
  | .Assigned name => ⟨.Assigned (lowerExpr name), source⟩
  | .Old value => ⟨.Old (lowerExpr value), source⟩
  | .Fresh value => ⟨.Fresh (lowerExpr value), source⟩
  | .Assert cond =>
    ⟨.Assert { cond with condition := lowerExpr cond.condition }, source⟩
  | .Assume cond => ⟨.Assume (lowerExpr cond), source⟩
  | .Return v => ⟨.Return (v.map lowerExpr), source⟩
  | .ProveBy v p => ⟨.ProveBy (lowerExpr v) (lowerExpr p), source⟩
  | .ContractOf ty f => ⟨.ContractOf ty (lowerExpr f), source⟩
  -- Leaves with no StmtExpr children
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _
  | .LiteralDecimal _ | .New _ | .This | .Abstract | .All | .Hole .. => expr

/-- Lower a statement-position `StmtExprMd`. A top-level `.IncrDecr` becomes
    a clean `.Assign` (no value yielded). Everything else delegates to
    `lowerExpr`, except control-flow constructors whose children remain
    statements. -/
partial def lowerStmt (stmt : StmtExprMd) : StmtExprMd :=
  let source := stmt.source
  match stmt.val with
  | .IncrDecr _ op target =>
    -- In statement position, the yielded value is discarded — emit a clean assignment.
    lowerToAssign op (lowerVariable target) source
  | .Block stmts label =>
    ⟨.Block (stmts.map lowerStmt) label, source⟩
  | .While cond invs dec body =>
    ⟨.While (lowerExpr cond) (invs.map lowerExpr) (dec.map lowerExpr) (lowerStmt body), source⟩
  | .IfThenElse cond th el =>
    ⟨.IfThenElse (lowerExpr cond) (lowerStmt th) (el.map lowerStmt), source⟩
  | _ => lowerExpr stmt

/-- Recurse into a Field target's nested expression, lowering any `.IncrDecr`
    that may appear inside it. -/
partial def lowerVariable (v : VariableMd) : VariableMd :=
  match v.val with
  | .Field target fieldName => ⟨.Field (lowerExpr target) fieldName, v.source⟩
  | _ => v

end

/-- Apply IncrDecr elimination to a procedure body. -/
private def lowerBody (body : Body) : Body :=
  match body with
  | .Transparent b => .Transparent (lowerStmt b)
  | .Opaque postconds impl modif =>
    .Opaque
      (postconds.map (·.mapCondition lowerExpr))
      (impl.map lowerStmt)
      (modif.map lowerExpr)
  | .Abstract postconds =>
    .Abstract (postconds.map (·.mapCondition lowerExpr))
  | .External => .External

private def lowerProcedure (proc : Procedure) : Procedure :=
  { proc with
    body := lowerBody proc.body
    preconditions := proc.preconditions.map (·.mapCondition lowerExpr)
    decreases := proc.decreases.map lowerExpr
    invokeOn := proc.invokeOn.map lowerExpr }

/--
Eliminate every `.IncrDecr` node in a Laurel program by lowering it to
existing constructs. After this pass, no remaining pass should see an
`.IncrDecr` node.
-/
def eliminateIncrDecr (program : Program) : Program :=
  let staticProcs := program.staticProcedures.map lowerProcedure
  let types := program.types.map fun td =>
    match td with
    | .Composite ct =>
      .Composite { ct with instanceProcedures := ct.instanceProcedures.map lowerProcedure }
    | other => other
  { program with staticProcedures := staticProcs, types := types }

end -- public section
end Strata.Laurel
