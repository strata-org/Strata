/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Util.Tactics

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

/-- Desugar short-circuit operators to IfThenElse when the second operand is imperative. -/
def desugarShortCircuitExpr (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  let md := expr.md
  match expr with
  | WithMetadata.mk val _ =>
  match val with
  | .PrimitiveOp op args =>
    let args' := args.attach.map fun ⟨a, _⟩ => desugarShortCircuitExpr model a
    match op, args with
    | .AndThen, [_, b] | .Implies, [_, b] =>
      if containsAssignmentOrImperativeCall model b then
        let elseVal := match op with | .AndThen => false | _ => true
        ⟨.IfThenElse args'[0]! args'[1]! (some (bare (.LiteralBool elseVal))), md⟩
      else ⟨.PrimitiveOp op args', md⟩
    | .OrElse, [_, b] =>
      if containsAssignmentOrImperativeCall model b then
        ⟨.IfThenElse args'[0]! (bare (.LiteralBool true)) (some args'[1]!), md⟩
      else ⟨.PrimitiveOp op args', md⟩
    | _, _ => ⟨.PrimitiveOp op args', md⟩
  | .IfThenElse cond th el =>
    ⟨.IfThenElse (desugarShortCircuitExpr model cond) (desugarShortCircuitExpr model th)
      (match el with | some e => some (desugarShortCircuitExpr model e) | none => none), md⟩
  | .Block stmts label =>
    ⟨.Block (stmts.attach.map fun ⟨s, _⟩ => desugarShortCircuitExpr model s) label, md⟩
  | .While c invs dec body =>
    ⟨.While (desugarShortCircuitExpr model c)
      (invs.attach.map fun ⟨i, _⟩ => desugarShortCircuitExpr model i)
      (match dec with | some d => some (desugarShortCircuitExpr model d) | none => none)
      (desugarShortCircuitExpr model body), md⟩
  | .LocalVariable name ty init =>
    ⟨.LocalVariable name ty (match init with | some i => some (desugarShortCircuitExpr model i) | none => none), md⟩
  | .Assign targets value =>
    ⟨.Assign (targets.attach.map fun ⟨t, _⟩ => desugarShortCircuitExpr model t) (desugarShortCircuitExpr model value), md⟩
  | .StaticCall callee args =>
    ⟨.StaticCall callee (args.attach.map fun ⟨a, _⟩ => desugarShortCircuitExpr model a), md⟩
  | .Return v =>
    ⟨.Return (match v with | some v' => some (desugarShortCircuitExpr model v') | none => none), md⟩
  | _ => expr
termination_by expr
decreasing_by all_goals ((try cases x); simp_all; try term_by_mem)

private def desugarShortCircuitProcedure (model : SemanticModel) (proc : Procedure) : Procedure :=
  { proc with body := match proc.body with
    | .Transparent b => .Transparent (desugarShortCircuitExpr model b)
    | .Opaque posts impl mods => .Opaque (posts.map (desugarShortCircuitExpr model)) (impl.map (desugarShortCircuitExpr model)) mods
    | other => other }

/-- Desugar short-circuit operators in a program. -/
def desugarShortCircuit (model : SemanticModel) (program : Program) : Program :=
  { program with staticProcedures := program.staticProcedures.map (desugarShortCircuitProcedure model) }

end -- public section
end Strata.Laurel
