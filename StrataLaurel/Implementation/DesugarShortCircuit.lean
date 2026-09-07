/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.Resolution
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.LiftImperativeExpressions
import StrataLaurel.Implementation.MapStmtExpr

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
  -- The short-circuit operators are calls to their built-in wrappers
  -- (`Operation.procName`); none of them is overloaded, so `UniqueOverloadNames`
  -- leaves the names alone and matching on the callee text is safe.
  | .StaticCall callee args =>
    match Operation.ofProcName? callee.text, args with
    -- With bottom-up traversal, `a` and `b` are already desugared (nested
    -- short-circuits converted to IfThenElse). The check still works because
    -- `containsAssignmentOrImperativeCall` recurses into IfThenElse.
    | some op@.AndThen, [a, b] | some op@.Implies, [a, b] =>
      if containsAssignmentOrImperativeCall imperativeCallees b then
        let elseVal := match op with | .AndThen => false | _ => true
        ⟨.IfThenElse a b (some (wrap (.LiteralBool elseVal))), source⟩
      else expr
    | some .OrElse, [a, b] =>
      if containsAssignmentOrImperativeCall imperativeCallees b then
        ⟨.IfThenElse a (wrap (.LiteralBool true)) (some b), source⟩
      else expr
    | _, _ => expr
  | _ => expr

/-- Desugar short-circuit operators in a program. -/
def desugarShortCircuit (program : Program) : Program :=
  -- Every static procedure is imperative now that Laurel `function`s are gone,
  -- and this pass runs before the lifting pass, so calls to
  -- them are still in expression position here. They therefore all count as
  -- imperative callees whose short-circuited operands must be guarded.
  let imperativeCallees := program.staticProcedures.map (·.name.text)
  mapProgramStmtExpr (mapStmtExpr (desugarShortCircuitNode imperativeCallees)) program

end -- public section

/-- Pipeline pass: desugar short-circuit operators. -/
public def desugarShortCircuitPass : LoweringPass where
  name := "DesugarShortCircuit"
  creates := [NodeKind.StmtExpr.IfThenElse, NodeKind.Pseudo.statementExpression]
  removes := [NodeKind.Pseudo.imperativeShortCircuit]
  documentation := "Rewrites a short-circuit boolean operator (`&&`, `||`, `=>`) into a conditional expression when its guarded operand contains an assignment or an imperative call. Short-circuits over pure operands are left alone, and the Core translator handles them. This must precede `LiftImperativeExpressions`, which would otherwise hoist the imperative call out of the branch that guards it."
  run := fun _ p _ =>
    (desugarShortCircuit p, [], {})

end Strata.Laurel
