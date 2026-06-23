/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.MapStmtExpr

/-!
# Desugar Short-Circuit Operators

Rewrites `AndThen`, `OrElse`, and `Implies` to `IfThenElse` when the second
operand contains imperative calls (assignments or non-functional procedure calls).
This must run before `LiftImperativeExpressions` to prevent the lifter from
hoisting imperative calls out of the short-circuited branch.

Pure operands pass through unchanged and are handled by the Core translator.
-/

namespace Strata.Laurel

public section


/-- Local rewrite of a single short-circuit node. Recursion is handled by `mapStmtExpr`. -/
private def desugarShortCircuitNode (imperativeCallees : List String) (expr : StmtExprMd) : StmtExprMd :=
  let source := expr.source
  let wrap (v : StmtExpr) : StmtExprMd := ⟨v, source⟩
  match expr.val with
  | .PrimitiveOp op args _ =>
    match op, args with
    -- With bottom-up traversal, `a` and `b` are already desugared (nested
    -- short-circuits converted to IfThenElse). The check still works because
    -- `containsAssignmentOrImperativeCall` recurses into IfThenElse.
    | .AndThen, [a, b] | .Implies, [a, b] =>
      if containsAssignmentOrImperativeCall imperativeCallees b then
        let elseVal := match op with | .AndThen => false | _ => true
        ⟨.IfThenElse a b (some (wrap (.LiteralBool elseVal))), source⟩
      else expr
    | .OrElse, [a, b] =>
      if containsAssignmentOrImperativeCall imperativeCallees b then
        ⟨.IfThenElse a (wrap (.LiteralBool true)) (some b), source⟩
      else expr
    | _, _ => expr
  | _ => expr

/-- Desugar short-circuit operators in a program. -/
def desugarShortCircuit (program : Program) : Program :=
  let imperativeCallees := (program.staticProcedures.filter (!·.isFunctional)).map (·.name.text)
  mapProgram (mapStmtExpr (desugarShortCircuitNode imperativeCallees)) program

end -- public section

/-- Pipeline pass: desugar short-circuit operators. -/
public def desugarShortCircuitPass : LoweringPass where
  name := "DesugarShortCircuit"
  documentation := "Rewrites short-circuit boolean operators (`&&` and `||`) into equivalent conditional expressions. This simplifies subsequent passes and the final translation to Core, which does not have short-circuit semantics built in."
  run := fun p _ _ =>
    (desugarShortCircuit p, [], {})
  comesBefore := [
      ⟨ liftImperativeExpressionsPass.meta, "The desugar short circuit pass introduces if-then-else expressions whose control-flow must be taken into account by the lifting pass."⟩]

end Strata.Laurel
