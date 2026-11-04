/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.MapStmtExpr
public import StrataLaurel.Implementation.LaurelPass

/-!
# Eliminate Return Statements

Replaces `return` statements in imperative procedure bodies with assignments
to the output parameters followed by an `exit` to a labelled block that wraps
the entire body. This ensures that code placed after the body block (e.g.,
postcondition assertions inserted by the contract pass) is always reached.

This pass should run after `EliminateReturnsInExpression` (which handles
functional/expression-position returns) and before the contract pass.
-/

namespace Strata.Laurel

public section

@[expose, match_pattern]
public def returnLabel : String := "$return"

/-- Transform a single procedure: wrap body in a labelled block and replace returns. -/
private def eliminateReturnStmts (proc : Procedure) : Procedure :=
  match proc.body with
  | .Opaque postconds (some impl) mods =>
    let impl' := replaceReturn proc.outputs impl
    let wrapped := match impl'.val with
      | .Block stmts none [] none => ⟨.Block stmts (some returnLabel) [] none, impl'.source⟩
      | _ => ⟨ .Block [impl'] (some returnLabel) [] none, proc.name.source ⟩
    { proc with body := .Opaque postconds (some wrapped) mods }
  | .Transparent body =>
    let body' := replaceReturn proc.outputs body
    let wrapped := match body'.val with
      | .Block stmts none [] none => ⟨.Block stmts (some returnLabel) [] none, body'.source⟩
      | _ => ⟨ .Block [body'] (some returnLabel) [] none, proc.name.source ⟩
    { proc with body := .Transparent wrapped }
  | _ => proc
where

  /-- Replace `Return vals` with one assignment per output followed by
    `exit "$return"` (or just the `exit` for a valueless return). Uses
    `mapStmtExpr` for bottom-up traversal.

    Handling a valued return is required because the heap param pass introduces valued
    returns in StrataLaurel/Implementation/HeapParameterizationConstants.lean.
    We should change that so we can remove this case. -/
  replaceReturn (outputs : List Parameter) (expr : StmtExprMd) : StmtExprMd :=
    mapStmtExpr (fun e =>
      match e.val with
      | .Return [] => ⟨ .Goto returnLabel .blockEnd, expr.source ⟩
      | .Return vals =>
        let exit : StmtExprMd := ⟨ .Goto returnLabel .blockEnd, expr.source ⟩
        if vals.length == outputs.length then
          let assigns := (outputs.zip vals).map fun (out, val) =>
            (⟨ .Assign [⟨ .Local out.name, expr.source ⟩] val, expr.source ⟩ : StmtExprMd)
          ⟨.Block (assigns ++ [exit]) none [] none, e.source⟩
        else exit
      | _ => e) expr

/-- Transform a program by eliminating return statements in all procedure bodies. -/
def eliminateReturnStatements (program : Program) : Program :=
  mapProgramProcedures eliminateReturnStmts program

public def eliminateReturnStatementsPass : LaurelPass where
  name := "EliminateReturnStatements"
  creates := [NodeKind.StmtExpr.Goto, NodeKind.StmtExpr.Block]
  unsupported := [NodeKind.StmtExpr.Try.finally?.some]
  removes := [
      NodeKind.StmtExpr.Return,
      NodeKind.Pseudo.generatedReturn
    ]
  documentation := "Lower return statements to exit statements. Wrap each procedure body with a 'return' block"
  run := fun _ p _m =>
    let p' := eliminateReturnStatements p
    (p', [], {})

end -- public section

end Strata.Laurel
