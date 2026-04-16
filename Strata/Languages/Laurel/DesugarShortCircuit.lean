/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.LiftImperativeExpressions
public import Strata.Util.Statistics

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

private def bare (v : StmtExpr) : StmtExprMd := ⟨v, none, default⟩

/-- Local rewrite of a single short-circuit node. Recursion is handled by `mapStmtExprM`. -/
private def desugarShortCircuitNode (model : SemanticModel) (expr : StmtExprMd) : Id StmtExprMd :=
  let source := expr.source
  let md := expr.md
  match expr.val with
  | .PrimitiveOp op args =>
    match op, args with
    | .AndThen, [a, b] | .Implies, [a, b] =>
      if containsAssignmentOrImperativeCall model b then
        let elseVal := match op with | .AndThen => false | _ => true
        ⟨.IfThenElse a b (some (bare (.LiteralBool elseVal))), source, md⟩
      else expr
    | .OrElse, [a, b] =>
      if containsAssignmentOrImperativeCall model b then
        ⟨.IfThenElse a (bare (.LiteralBool true)) (some b), source, md⟩
      else expr
    | _, _ => expr
  | _ => expr

/-- Desugar short-circuit operators in a program. -/
def desugarShortCircuit (model : SemanticModel) (program : Program) : Program :=
  mapProgramM (mapStmtExprM (desugarShortCircuitNode model)) program

end -- public section
end Strata.Laurel
