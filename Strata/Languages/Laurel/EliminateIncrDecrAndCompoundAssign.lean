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
# Eliminate Increment / Decrement and Compound Assignment

Lowers `.IncrDecr` nodes (Java-style `++x`, `x++`, `--x`, `x--`) and
`.CompoundAssign` nodes (C-style `x += e`, `-=`, `*=`, `/=`, `%=`, `^=`) into
existing Laurel constructs. Runs before `LiftImperativeExpressions` so that
later passes never see either node.

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

Compound assignment `x op= e` lowers to `x := x op e` — always new-valued, so
unlike postfix `IncrDecr` it needs no old-value recovery. Both share the same
core (`lowerOpAssign`), with `IncrDecr` supplying `rhs = 1`.

The pass uses the generic `mapStmtExpr` bottom-up traversal from
`MapStmtExpr.lean`. The only constructors that change are `.IncrDecr` and
`.CompoundAssign`; all other nodes are left as-is by the traversal's default
recursion.

The target of `.IncrDecr` / `.CompoundAssign` must be a `Variable.Local` or
`Variable.Field` — the concrete-to-abstract translator already enforces this.
-/

namespace Strata.Laurel

public section

/-- Reconstruct the read-side `StmtExprMd` for a `Variable`.

    A `.Field` target duplicates the object subtree into the read operand (the lowering
    emits `target op rhs`). This is sound — and term-size cost only, not a correctness
    risk — because a field read lowers to the pure, obligation-free `readField` lookup,
    so both copies read the same `$heap` at the same point. (Revisit if field reads ever
    gain a precondition.) -/
private def targetAsRead (target : VariableMd) : StmtExprMd :=
  let source := target.source
  match target.val with
  | .Local name => ⟨.Var (.Local name), source⟩
  | .Field tgt fieldName => ⟨.Var (.Field tgt fieldName), source⟩
  | .Declare param => ⟨.Var (.Local param.name), source⟩

/-- Build `.Assign [target] (target ⊕ rhs)` where `⊕` is `primOp`, yielding the new
    value. Shared by the `IncrDecr` lowering (`rhs = 1`) and `CompoundAssign` (user's
    RHS). The `.PrimitiveOp` keeps the default `skipProof := false`, so `/=`/`%=` carry
    the same division-by-zero obligation as a hand-written `x := x / e`. -/
private def lowerOpAssign (primOp : Operation) (target : VariableMd)
    (rhs : StmtExprMd) (source : Option FileRange) : StmtExprMd :=
  let read := targetAsRead target
  let updated : StmtExprMd := ⟨.PrimitiveOp primOp [read, rhs], source⟩
  ⟨.Assign [target] updated, source⟩

/-- Build `.Assign [target] (target ⊕ 1)` where `⊕` is `Add` for `Incr` and
    `Sub` for `Decr`. The resulting assignment expression yields the new value. -/
private def lowerToAssign (op : IncrDecrOp) (target : VariableMd)
    (source : Option FileRange) : StmtExprMd :=
  let primOp : Operation := match op with
    | .Incr => .Add
    | .Decr => .Sub
  lowerOpAssign primOp target ⟨.LiteralInt 1, source⟩ source

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
    and `.CompoundAssign` with their lowered forms; all other nodes pass through.

    `IncrDecr` and `CompoundAssign` share one lowering, `x := x ⊕ rhs` via
    `lowerOpAssign` (`IncrDecr` supplies `rhs = 1`). We fuse both here rather
    than lowering `IncrDecr → CompoundAssign → :=` in separate passes: same
    shared lowering, one fewer traversal. Prefix `++x` is exactly that
    assignment; only postfix `x++` adds an inverse-op wrapper to recover the
    old value. -/
private def rewriteNode (node : StmtExprMd) : StmtExprMd :=
  match node.val with
  | .IncrDecr mode op target => lowerIncrDecr mode op target node.source
  | .CompoundAssign op target rhs => lowerOpAssign op target rhs node.source
  | _ => node

/-- Apply the rewrite to a procedure (body, preconditions, decreases, invokeOn). -/
private def lowerProcedure (proc : Procedure) : Procedure :=
  mapProcedureM (m := Id) (mapStmtExpr rewriteNode) proc

/--
Eliminate every `.IncrDecr` and `.CompoundAssign` node in a Laurel program by
lowering it to existing constructs. After this pass, neither node remains.
-/
def eliminateIncrDecrAndCompoundAssign (program : Program) : Program :=
  let staticProcs := program.staticProcedures.map lowerProcedure
  let types := program.types.map fun td =>
    match td with
    | .Composite ct =>
      .Composite { ct with instanceProcedures := ct.instanceProcedures.map lowerProcedure }
    | other => other
  { program with staticProcedures := staticProcs, types := types }

/-- Pipeline pass: eliminate increment/decrement and compound-assignment operators. -/
public def eliminateIncrDecrAndCompoundAssignPass : LaurelPass where
  name := "EliminateIncrDecrAndCompoundAssign"
  documentation := "Lowers Java-style increment/decrement operators (`++x`, `x++`, `--x`, `x--`) and C-style compound assignments (`x += e`, `-=`, `*=`, `/=`, `%=`, `^=`) into existing Laurel assignment and arithmetic constructs. Prefix `++`/`--` and compound assignment yield the new value; postfix `++`/`--` yield the old value. Runs early so that no later pass observes an `.IncrDecr` or `.CompoundAssign` node."
  run := fun p _m => (eliminateIncrDecrAndCompoundAssign p, [], {})

end -- public section
end Strata.Laurel
