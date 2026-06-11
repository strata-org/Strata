/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Tactics

/-!

Given a transparent body, merge the returns into a single outer return.
Emits a diagnostic if it fails at any step.

-/

namespace Strata.Laurel

/-- Recurse into a statement, applying the guard-return rewrite inside blocks and branches.
    Returns `Except DiagnosticModel StmtExprMd` so that unsupported statement forms produce
    a diagnostic instead of panicking. -/
def removeReturns (stmt : StmtExprMd) : Except DiagnosticModel StmtExprMd :=
  match _h : stmt.val with
  | .Return (some expr) => .ok expr
  | .Block [head] _ => removeReturns head
  | .Block (head :: tail) label => do
    let newTail ← removeReturns ⟨.Block tail none, stmt.source⟩
    let passThrough: StmtExprMd :=
      let tailList := match newTail.val with
        | .Block stmts _ => stmts
        | _ => [newTail]
      ⟨ .Block (head :: tailList) label, stmt.source ⟩
    match _hhead : head.val with
    | .IfThenElse cond thenBr none =>
      let newThen ← removeReturns thenBr
      .ok ⟨ .IfThenElse cond newThen newTail, head.source ⟩
    | .Assign _ _ => .ok passThrough
    | .Assume _ => .ok passThrough
    | .Assert _ => .ok passThrough
    | .Block _ _ => .ok passThrough
    | .IfThenElse _ _ (some _) => .error (diagnosticFromSource head.source "in a transparent body, if-then-else is only supported as the last statement in a block")
    | _ => .error (diagnosticFromSource head.source
        s!"unsupported statement {head.val.constructorName} in block head")
  | .IfThenElse cond thenBr (some elseBr) => do
      let thenExpr ← removeReturns thenBr
      let elseExpr ← removeReturns elseBr
      .ok ⟨ .IfThenElse cond thenExpr (some elseExpr), stmt.source⟩
  | _ => .error (diagnosticFromSource stmt.source
      s!"ending a transparent body with a {stmt.val.constructorName} statement is not supported")
termination_by sizeOf stmt
decreasing_by all_goals (
  have hs : sizeOf stmt = 1 + sizeOf stmt.val + sizeOf stmt.source := by
    cases stmt; simp [AstNode.mk.sizeOf_spec]
  rw [_h] at hs
  simp only [StmtExpr.Block.sizeOf_spec, StmtExpr.IfThenElse.sizeOf_spec,
    List.cons.sizeOf_spec, List.nil.sizeOf_spec, Option.some.sizeOf_spec] at hs
  first
  | (have hh : sizeOf head = 1 + sizeOf head.val + sizeOf head.source := by
       cases head; simp [AstNode.mk.sizeOf_spec]
     rw [_hhead] at hh
     simp only [StmtExpr.IfThenElse.sizeOf_spec, Option.none.sizeOf_spec] at hh
     omega)
  | (simp only [AstNode.mk.sizeOf_spec, StmtExpr.Block.sizeOf_spec, Option.none.sizeOf_spec]
     have hh : sizeOf head = 1 + sizeOf head.val + sizeOf head.source := by
       cases head; simp [AstNode.mk.sizeOf_spec]
     omega)
  | omega)

/-- Transform a single procedure by applying the guard-return elimination to its body.
    Returns the procedure and any diagnostic emitted on failure. -/
private def eliminateReturnsInExpression (proc : Procedure) : Procedure × Array DiagnosticModel :=
  match proc.body with
  | .Transparent body =>
    match removeReturns body with
    | .ok result => ({ proc with body := .Transparent ⟨.Return result, body.source ⟩ }, #[])
    | .error diag => (proc, #[diag])
  | _ => (proc, #[])

public section

/--
Transform a program by eliminating returns in all functional procedure bodies.
-/
def eliminateReturnsInExpressionTransform (program : Program) : Program × Array DiagnosticModel :=
  let (procs, diags) := program.staticProcedures.foldl (fun (ps, ds) proc =>
    let (proc', procDiags) := eliminateReturnsInExpression proc
    (proc' :: ps, ds ++ procDiags)
  ) ([], #[])
  ({ program with staticProcedures := procs.reverse }, diags)

end -- public section

end Laurel
