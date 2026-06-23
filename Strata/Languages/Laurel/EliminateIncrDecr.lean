/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelPass
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

The pass uses the generic `mapStmtExpr` bottom-up traversal from
`MapStmtExpr.lean`. The only constructor that changes is `.IncrDecr`; all
other nodes are left as-is by the traversal's default recursion.

The target of `.IncrDecr` must be a `Variable.Local` or `Variable.Field` —
the concrete-to-abstract translator already enforces this.
-/

namespace Strata.Laurel

public section

/-- Reconstruct the read-side `StmtExprMd` for a `Variable`. -/
private def targetAsRead (target : VariableMd) : StmtExprMd :=
  let source := target.source
  match target.val with
  | .Local name => ⟨.Var (.Local name), source⟩
  | .Field tgt fieldName => ⟨.Var (.Field tgt fieldName), source⟩
  | .Declare param => ⟨.Var (.Local param.name), source⟩

/-- Build `.Assign [target] (target ⊕ 1)` where `⊕` is `Add` for `Incr` and
    `Sub` for `Decr`. The resulting assignment expression yields the new value. -/
private def lowerToAssign (op : IncrDecrOp) (target : VariableMd)
    (source : Option FileRange) : StmtExprMd :=
  let primOp : Operation := match op with
    | .Incr => .Add
    | .Decr => .Sub
  let one : StmtExprMd := ⟨.LiteralInt 1, source⟩
  let read := targetAsRead target
  let updated : StmtExprMd := ⟨.PrimitiveOp primOp [read, one], source⟩
  ⟨.Assign [target] updated, source⟩

/-- Lower a single `.IncrDecr` node to the expression form that yields the
    correct value for the given `mode` (Pre or Post). -/
private def lowerIncrDecr (mode : IncrDecrMode) (op : IncrDecrOp)
    (target : VariableMd) (source : Option FileRange) : StmtExprMd :=
  let assign := lowerToAssign op target source
  match mode with
  | .Pre => assign
  | .Post =>
    -- Recover the old value: apply the inverse delta to the new value.
    let inverseOp : Operation := match op with
      | .Incr => .Sub
      | .Decr => .Add
    let one : StmtExprMd := ⟨.LiteralInt 1, source⟩
    ⟨.PrimitiveOp inverseOp [assign, one], source⟩

/-- The rewrite step applied bottom-up by `mapStmtExpr`. Replaces `.IncrDecr`
    with its lowered form; all other nodes pass through unchanged. -/
private def rewriteNode (node : StmtExprMd) : StmtExprMd :=
  match node.val with
  | .IncrDecr mode op target => lowerIncrDecr mode op target node.source
  | _ => node

/-- Apply the rewrite to a procedure (body, preconditions, decreases, invokeOn). -/
private def lowerProcedure (proc : Procedure) : Procedure :=
  mapProcedureM (m := Id) (mapStmtExpr rewriteNode) proc

/--
Eliminate every `.IncrDecr` node in a Laurel program by lowering it to
existing constructs. After this pass, no `.IncrDecr` node remains.
-/
def eliminateIncrDecr (program : Program) : Program :=
  mapProgramProcedures lowerProcedure program

/-- Pipeline pass: eliminate increment/decrement operators. -/
public def eliminateIncrDecrPass : LaurelPass where
  name := "EliminateIncrDecr"
  documentation := "Lowers Java-style increment/decrement operators (`++x`, `x++`, `--x`, `x--`) into existing Laurel assignment and arithmetic constructs. Prefix forms yield the new value; postfix forms yield the old value. Runs early so that no later pass observes an `.IncrDecr` node."
  run := fun p _m => (eliminateIncrDecr p, [], {})

end -- public section
end Strata.Laurel
