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

private def bare (v : StmtExpr) : StmtExprMd := ⟨v, default⟩

inductive DesugarStats where
  /-- Number of short-circuit operators (AndThen/OrElse/Implies) rewritten to IfThenElse. -/
  | operatorsDesugared

#derive_prefixed_toString DesugarStats "DesugarShortCircuit"

private abbrev DesugarM := StateM Statistics

/-- Local rewrite of a single short-circuit node. Recursion is handled by `mapStmtExprM`. -/
private def desugarShortCircuitNode (model : SemanticModel) (expr : StmtExprMd) : DesugarM StmtExprMd := do
  let md := expr.md
  match expr.val with
  | .PrimitiveOp op args =>
    match op, args with
    | .AndThen, [a, b] | .Implies, [a, b] =>
      if containsAssignmentOrImperativeCall model b then
        modify (·.increment s!"{DesugarStats.operatorsDesugared}")
        let elseVal := match op with | .AndThen => false | _ => true
        return ⟨.IfThenElse a b (some (bare (.LiteralBool elseVal))), md⟩
      else return expr
    | .OrElse, [a, b] =>
      if containsAssignmentOrImperativeCall model b then
        modify (·.increment s!"{DesugarStats.operatorsDesugared}")
        return ⟨.IfThenElse a (bare (.LiteralBool true)) (some b), md⟩
      else return expr
    | _, _ => return expr
  | _ => return expr

/-- Desugar short-circuit operators in a program. -/
def desugarShortCircuit (model : SemanticModel) (program : Program) : Program × Statistics :=
  let (program', stats) :=
    (mapProgramM (mapStmtExprM (desugarShortCircuitNode model)) program).run {}
  (program', stats)

end -- public section
end Strata.Laurel
