/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Tactics
import Strata.Languages.Laurel.EliminateValueInReturns
public import Strata.Languages.Laurel.LaurelPass

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
termination_by sizeOf stmt.val
decreasing_by
  all_goals
    simp only [_h, StmtExpr.Block.sizeOf_spec, StmtExpr.IfThenElse.sizeOf_spec,
      List.cons.sizeOf_spec, List.nil.sizeOf_spec, Option.none.sizeOf_spec,
      Option.some.sizeOf_spec]
    try have hhd := AstNode.sizeOf_val_lt head
    try have htb := AstNode.sizeOf_val_lt thenBr
    try have heb := AstNode.sizeOf_val_lt elseBr
    try simp only [_hhead, StmtExpr.IfThenElse.sizeOf_spec, Option.none.sizeOf_spec] at hhd
    omega

/-- Transform a single procedure by applying the guard-return elimination to its body.
    Returns the procedure and any diagnostic emitted on failure. -/
private def eliminateReturnsInExpression (proc : Procedure) : Procedure × List DiagnosticModel :=
  match proc.body with
  | .Transparent body =>
    match removeReturns body with
    | .ok result => ({ proc with body := .Transparent ⟨.Return result, body.source ⟩ }, [])
    | .error diag => (proc, [diag])
  | _ => (proc, [])

public section

/--
Transform a program by eliminating returns in all procedure bodies.
-/
def mergeAndLiftReturns (program : Program) : Program × List DiagnosticModel :=
  let (procs, diags) := program.staticProcedures.foldl (fun (ps, ds) proc =>
    let (proc', procDiags) := eliminateReturnsInExpression proc
    (proc' :: ps, ds ++ procDiags)
  ) ([], [])
  ({ program with staticProcedures := procs.reverse }, diags)

end -- public section

/-- Pipeline pass: merge and lift returns. -/
public def mergeAndLiftReturnsPass : LoweringPass where
  name := "MergeAndLiftReturns"
  documentation := "Attempts to merge and lift returns so that only a single outer return remains, enabling the procedure to be more easily converted to a functional form."
  needsResolves := true
  comesBefore := [⟨ eliminateValueInReturnsPass.meta, "Lifts returns with a value, so the value should not yet have been lowered."⟩]
  run := fun _ p _m =>
    let (p', diags) := mergeAndLiftReturns p
    (p', diags, {})

end Laurel
